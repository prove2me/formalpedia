-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
-- name    : TaoFivePrimes_RHHighDirichletBinning
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T03:34:39.942288+00:00
-- url     : https://prove2.me/theorems/7749b4be-9743-4a81-8d05-38df7160a698
-- title:
--   Exact binned Dirichlet coefficient accumulation
-- statement:
--   Transparent integer algorithms for24 normalized offset powers and consecutive-bin coefficient accumulation, and a proposed-value decoder. Definitions alone assert no accuracy, sign, zero count or RH statement.
-- source:
--   Platt DOI10.1090/mcom/3198, binning and Taylor/Fourier reconstruction; surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
set_option autoImplicit false
namespace RHHighDirichletBinning
noncomputable def field (w k : Nat) : Int := ((w/2^(160*k)%2^160:Nat):Int)-2^159
noncomputable def bin (w : Nat) : Nat := w/2^480
noncomputable def termsAux : Nat → Int → Int → Int → Int → List (Int×Int)
  | 0, _, _, _, _ => []
  | k+1, d, wr, wi, p => (wr*p/(2:Int)^128,wi*p/(2:Int)^128)::
      termsAux k d wr wi (p*d/(2:Int)^128)
noncomputable def terms (w : Nat) : List (Int×Int) := termsAux 24 (field w 2) (field w 0) (field w 1) (2^128)
noncomputable def add (xs ys : List (Int×Int)) : List (Int×Int) :=
  List.zipWith (fun a b=>(a.1+b.1,a.2+b.2)) xs ys
noncomputable def accumulate : Nat → List (Int×Int) → List Nat → List (Nat×List (Int×Int))
  | j, acc, [] => [(j,acc)]
  | j, acc, w::ws => if bin w=j then accumulate j (add acc (terms w)) ws
      else (j,acc)::accumulate (bin w) (terms w) ws
noncomputable def bins : List Nat → List (Nat×List (Int×Int))
  | [] => []
  | w::ws => accumulate (bin w) (terms w) ws
noncomputable def decodeCoefficients : Nat → Nat → List (Int×Int)
  | 0, _ => []
  | k+1, w => (field w 0,field w 1)::decodeCoefficients k (w/2^320)
noncomputable def decode (w : Nat) : Nat×List (Int×Int) := (w%2^16,decodeCoefficients 24 (w/2^16))
end RHHighDirichletBinning
noncomputable def TaoFivePrimes_RHHighDirichletBinning : Nat := 24


