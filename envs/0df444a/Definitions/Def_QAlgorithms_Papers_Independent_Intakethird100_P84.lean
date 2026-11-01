-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P84
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:04:13.986859+00:00
-- url     : https://prove2.me/theorems/03a58561-60ec-4146-9b2b-a232f973e57c
-- title:
--   Definitions for Monotonicity of quantum relative entropy revisited
-- statement:
--   The objects the formalized statements of *Monotonicity of quantum relative entropy revisited* (arXiv:quant-ph/0209053) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsTwoPositive`: PDF p.2, (2): positivity of the 2-by-2 block amplification; no higher amplifications or unitality are required.
--   - `embed12`: PDF p.11, implicit tensor convention: A12 tensor I3, reassociated to I × (J × K). There is no dimension normalization.
--   - `petzExampleDensity`: PDF p.7, Example 1: the first density; its domain is 0 < mu < 1/2.
--   - `exampleReference`: PDF p.7, Example 1: the maximally mixed reference density in dimension 3.
--   - `exampleEffects`: PDF p.7, Example 1: the three explicitly printed effects in source order. The off-diagonal entries in the last effect are -z and -conj(z).
--   - `measurementDensity`: PDF pp.6–7: a finite measurement law viewed as its diagonal density. On a normalized density and POVM the entries are the source's Tr(D E_j), by cyclicity of trace.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, https://arxiv.org/abs/quant-ph/0209053v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35

/-!
Petz, Monotonicity of quantum relative entropy revisited,
arXiv:quant-ph/0209053v1, PDF pp.2,5–12.

All matrix spaces are finite complex matrix algebras with ordinary trace.
Full-domain inequalities use the accepted extended `relativeEntropy`, with
+infinity on support failure. The finite real expression is restricted as follows.
The equality statements use the frozen `qRelEntropy` only on
invertible normalized densities. Its correction -rho+sigma has trace zero on
this domain, so its value is precisely the source's natural-log relative entropy.
The SSA equalities use the frozen entropy in bits: multiplying each side by
log 2 > 0 gives exactly the source's natural-log equality, in both directions.
For singular second arguments only the extended entropy is used.
Cited background statements are included at the complete source strength.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.
open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)
open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- PDF p.2, (2): positivity of the 2-by-2 block amplification; no higher
amplifications or unitality are required. -/
def IsTwoPositive {I J : Type*} [Fintype I] [Fintype J]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  ∀ X : Matrix (Fin 2 × I) (Fin 2 × I) ℂ,
    X.PosSemidef → (idTensorSuperop T X).PosSemidef

/-- PDF p.11, implicit tensor convention: A12 tensor I3, reassociated to
I × (J × K). There is no dimension normalization. -/
def embed12 {I J K : Type*} (A : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × (J × K)) (I × (J × K)) ℂ :=
  fun a b => if a.2.2 = b.2.2 then A (a.1, a.2.1) (b.1, b.2.1) else 0

/-- PDF p.7, Example 1: the first density; its domain is 0 < mu < 1/2. -/
def petzExampleDensity (mu : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![((1 - 2 * mu : ℝ) : ℂ), (mu : ℂ), (mu : ℂ)]

/-- PDF p.7, Example 1: the maximally mixed reference density in dimension 3. -/
def exampleReference : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![(1 / 3 : ℂ), (1 / 3 : ℂ), (1 / 3 : ℂ)]

/-- PDF p.7, Example 1: the three explicitly printed effects in source order.
The off-diagonal entries in the last effect are -z and -conj(z). -/
def exampleEffects (x : ℝ) (z : ℂ) : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![Matrix.diagonal ![1, 0, 0],
    !![0, 0, 0; 0, (x : ℂ), z; 0, conj z, ((1 - x : ℝ) : ℂ)],
    !![0, 0, 0; 0, ((1 - x : ℝ) : ℂ), -z; 0, -(conj z), (x : ℂ)]]

/-- PDF pp.6–7: a finite measurement law viewed as its diagonal density.
On a normalized density and POVM the entries are the source's Tr(D E_j),
by cyclicity of trace. -/
def measurementDensity {I O : Type*} [Fintype I] [DecidableEq O]
    (E : O → Matrix I I ℂ) (D : Matrix I I ℂ) : Matrix O O ℂ :=
  Matrix.diagonal fun j => (effectProb (E j) D : ℂ)

/-- PDF p.2: the identity map satisfies the exact two-positive block condition. -/
example {I : Type*} [Fintype I] :
    IsTwoPositive (LinearMap.id : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) := by
  intro X hX
  exact hX

/-- PDF p.11: identity embedding retains a diagonal third-register block. -/
example {I J K : Type*} (A : Matrix (I × J) (I × J) ℂ)
    (a b : I × J) (k : K) :
    embed12 A (a.1, (a.2, k)) (b.1, (b.2, k)) = A a b := by
  simp [embed12]

/-- PDF p.7: the first weight is exactly 1-2 mu. -/
example (mu : ℝ) : petzExampleDensity mu 0 0 = ((1 - 2 * mu : ℝ) : ℂ) := by
  simp [petzExampleDensity]

/-- PDF p.7: the reference has ordinary trace one. -/
example : exampleReference.trace = 1 := by
  norm_num [exampleReference, Matrix.trace, Fin.sum_univ_three] <;>
    (change (2 / 3 : ℂ) + 1 / 3 = 1; norm_num)

/-- PDF p.7: the two off-diagonal effect entries cancel. -/
example (x : ℝ) (z : ℂ) :
    exampleEffects x z 1 1 2 + exampleEffects x z 2 1 2 = 0 := by
  simp [exampleEffects]

/-- PDF pp.6–7: measurement probabilities are the actual diagonal entries. -/
example {I O : Type*} [Fintype I] [DecidableEq O]
    (E : O → Matrix I I ℂ) (D : Matrix I I ℂ) (j : O) :
    measurementDensity E D j j = (effectProb (E j) D : ℂ) := by
  simp [measurementDensity]

end QAlgorithms.Papers.Independent.Intakethird100.P84


