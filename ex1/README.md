## Notes

**Build constraint**
```
mkdir build  
cd build  
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON ..  
make  
```

**To run tests**  
```
cd test  
make simple0.ll  
../build/constraint simple0.ll 
```
