-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryConvolution
-- name    : Submission_ThreeSum_TernaryConvolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:18:18.298707+00:00
-- url     : https://prove2.me/theorems/8c39c342-31de-4527-91a6-16e64141e604
-- title:
--   Ternary Convolution
-- statement:
--   Definitions and structural lemmas for Ternary Convolution, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
def digitCoefficient (q a b : Fin 3) : ℤ :=
  ∑ r : Fin 3, inverseCoefficient q r * digitChoose r a * digitChoose r b
def pairCoefficient {N : ℕ} (Q A B : TritWord N) : ℤ :=
  ∏ i, digitCoefficient (Q i) (A i) (B i)
def factorial {N : ℕ} (A : TritWord N) : ℤ := ∏ i, ((A i).val.factorial : ℤ)
def Adds {N : ℕ} (A B Q : TritWord N) : Prop :=
  ∀ i, (A i).val+(B i).val=(Q i).val
instance {N : ℕ} (A B Q : TritWord N) : Decidable (Adds A B Q) :=
  inferInstanceAs (Decidable (∀ i, (A i).val+(B i).val=(Q i).val))
def convolution {N : ℕ} (f g : TritWord N → ℤ) (Q : TritWord N) : ℤ :=
  ∑ A, ∑ B, if Adds A B Q then f A*g B else 0
def inverseWeight {N : ℕ} (Q R : TritWord N) : ℤ :=
  ∏ i, inverseCoefficient (Q i) (R i)
def binomialInverse {N : ℕ} (H : TritWord N → ℤ) (Q : TritWord N) : ℤ :=
  ∑ R, inverseWeight Q R * H R
def partialKernel {N : ℕ} (s : Finset (Fin N)) (Q A : TritWord N) : ℤ :=
  ∏ i, if i ∈ s then inverseCoefficient (Q i) (A i) else if A i=Q i then 1 else 0
def partialInverse {N : ℕ} (s : Finset (Fin N)) (H : TritWord N → ℤ)
    (Q : TritWord N) : ℤ := ∑ A, partialKernel s Q A * H A
end ThreeSum.TernaryConvolution


