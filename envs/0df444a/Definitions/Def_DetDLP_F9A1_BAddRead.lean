-- Prove2me | Definitions.Def_DetDLP_F9A1_BAddRead
-- name    : DetDLP_F9A1_BAddRead
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:49:57.214051+00:00
-- url     : https://prove2.me/theorems/1c90e9d7-3dde-49eb-ad6e-45429c474b0b
-- title:
--   Wire operations for residual scalar addition and readout
-- statement:
--   Flatten the residual coefficients row by row, add corresponding words modulo the supplied modulus, and read and divide the first word in each row. Both raw operations act on framed binary lists.

import Definitions.Def_DetDLP_ResidualScalarOracle
import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_DetDLP_PolyTBridge

set_option autoImplicit false
namespace DetDLP.F9A1
open Polynomial DetDLP_W1_Queries Groundwork.PolyT

noncomputable def bWords (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic)
    (x : ResidualScalarOracle.B f ell q) : List ℕ :=
  List.ofFn fun idx : Fin (ell * f.natDegree) => ResidualScalarOracle.word f ell q hf x
    (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2

noncomputable def bEncode (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic)
    (x : ResidualScalarOracle.B f ell q) : List Bool :=
  encodeNatListBin (bWords f ell q hf x)

def bAddRaw (w : List Bool) : List Bool :=
  let m := bval (first w)
  let xs := w5_M6Sort.decode (first (more w))
  let ys := w5_M6Sort.decode (first (more (more w)))
  encodeNatListBin ((xs.zip ys).map fun ab => (ab.1 + ab.2) % m)

def bReadZeroDivRaw (w : List Bool) : List Bool :=
  let m := bval (first w)
  let d := (first (more w)).length
  let ell := (first (more (more w))).length
  let xs := w5_M6Sort.decode (first (more (more (more w))))
  encodeNatListBin ((List.range ell).map fun j => xs.getD (j * d + 0) 0 / m)

end DetDLP.F9A1


