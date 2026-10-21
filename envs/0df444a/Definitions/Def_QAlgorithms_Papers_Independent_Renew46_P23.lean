-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P23
-- name    : QAlgorithms_Papers_Independent_Renew46_P23
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:30:27.260093+00:00
-- url     : https://prove2.me/theorems/5b06cbd5-8f2a-4c85-84c4-7d2d46c879fe
-- title:
--   Definitions for Sufficiency in quantum statistical inference. A survey with examples
-- statement:
--   The objects the formalized statements of *Sufficiency in quantum statistical inference. A survey with examples* (arXiv:quant-ph/0604091) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `bernoulliSampleLaw`: PDF p.2: the joint law of n independent Bernoulli(p) observations, including p = 0 and p = 1. The measurable structure on Bool is discrete.
--   - `measurementMap`: Example 1, PDF p.3: the observable map determined by the measurement partition of unity. Its complex linearity is part of the construction.
--   - `binaryDensityStatistic`: Example 3, PDF p.6: a [0,1]-valued version of dP/d(P+Q). Clipping only changes the selected derivative on a (P+Q)-null set.
--   - `gaussianSampleLaw`: Example 4, PDF p.7: the actual iid Gaussian location family. Mathlib's second argument is variance, so the fixed standard deviation sigma is squared. The result below requires sigma > 0.
--   - `permutationAction`: Example 6, PDF p.12: conjugation by the tensor-factor permutation, expressed on matrix entries in the product basis.
--   - `permutationAverage`: Example 6, PDF p.12: the fixed, family-independent permutation average. Its range is the permutation-invariant algebra.
--   - `traceDensityDual`: Equation (12), PDF p.14: the trace-dual density, constructed by evaluation on matrix units. The indices j,i are reversed since Tr(D E_ji) = D_ij.
-- source:
--   Sufficiency in quantum statistical inference. A survey with examples, arXiv:quant-ph/0604091v1, https://arxiv.org/abs/quant-ph/0604091v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

/-!
Jenčová–Petz, arXiv:quant-ph/0604091v1, PDF pages 2–21.
Only pinned accepted modules are imported. New definitions are paper-local.
General modular perturbations and other deferred nodes are recorded in HARD.md
and GAPS.json. Compilation is pending the authorized batch handoff.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Renew46.P23

open QAlgorithms.Papers.Independent.Next46.P43
  (SufficientSigmaAlgebra MinimalSufficientSigmaAlgebra IsCStarCoarseGraining)
open QAlgorithms.Papers.Independent.Information100.P60 (copies)
open QAlgorithms.Papers.Independent.Dependency50.P28 (relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

local instance : MeasurableSpace Bool := ⊤

/-- PDF p.2: the joint law of n independent Bernoulli(p) observations,
including p = 0 and p = 1. The measurable structure on Bool is discrete. -/
def bernoulliSampleLaw (n : ℕ) (p : Set.Icc (0 : ℝ) 1) :
    Measure (Fin n → Bool) :=
  Measure.pi (fun _ : Fin n => ProbabilityTheory.bernoulliMeasure true false p)

example : ProbabilityTheory.bernoulliMeasure true false (0 : unitInterval) =
    Measure.dirac false := by
  simp

example (n : ℕ) (p : Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (bernoulliSampleLaw n p) := by
  unfold bernoulliSampleLaw
  infer_instance

/-- Example 1, PDF p.3: the observable map determined by the measurement
partition of unity. Its complex linearity is part of the construction. -/
def measurementMap {X N : Type*} [Fintype X] [CStarAlgebra N]
    (E : X → N) : (X → ℂ) →ₗ[ℂ] N where
  toFun f := ∑ x, f x • E x
  map_add' f g := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp [Finset.smul_sum, smul_smul]

example {X N : Type*} [Fintype X] [CStarAlgebra N] (E : X → N) :
    measurementMap E 0 = 0 := by
  exact (measurementMap E).map_zero

/-- Example 3, PDF p.6: a [0,1]-valued version of dP/d(P+Q).
Clipping only changes the selected derivative on a (P+Q)-null set. -/
def binaryDensityStatistic {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) (x : X) : ℝ≥0∞ :=
  min (P.rnDeriv (P + Q) x) 1

example {X : Type*} [MeasurableSpace X] (P Q : Measure X) (x : X) :
    binaryDensityStatistic P Q x ≤ 1 := by
  exact min_le_right _ _

/-- Example 4, PDF p.7: the actual iid Gaussian location family.
Mathlib's second argument is variance, so the fixed standard deviation sigma
is squared. The result below requires sigma > 0. -/
def gaussianSampleLaw (n : ℕ) (sigma : ℝ) (m : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal m (Real.toNNReal (sigma ^ 2)))

example : ProbabilityTheory.gaussianReal (0 : ℝ) (0 : ℝ≥0) = Measure.dirac 0 := by
  simp

example (n : ℕ) (sigma m : ℝ) : IsProbabilityMeasure (gaussianSampleLaw n sigma m) := by
  unfold gaussianSampleLaw
  infer_instance

/-- Example 6, PDF p.12: conjugation by the tensor-factor permutation,
expressed on matrix entries in the product basis. -/
def permutationAction {I : Type*} (n : ℕ) (p : Equiv.Perm (Fin n)) :
    Matrix (Fin n → I) (Fin n → I) ℂ →ₗ[ℂ]
      Matrix (Fin n → I) (Fin n → I) ℂ where
  toFun A x y := A (x ∘ p) (y ∘ p)
  map_add' A B := rfl
  map_smul' c A := rfl

example {I : Type*} (n : ℕ) (A : Matrix (Fin n → I) (Fin n → I) ℂ) :
    permutationAction n (Equiv.refl (Fin n)) A = A := by
  rfl

/-- Example 6, PDF p.12: the fixed, family-independent permutation average.
Its range is the permutation-invariant algebra. -/
def permutationAverage {I : Type*} (n : ℕ) :
    Matrix (Fin n → I) (Fin n → I) ℂ →ₗ[ℂ]
      Matrix (Fin n → I) (Fin n → I) ℂ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
    ∑ p : Equiv.Perm (Fin n), permutationAction n p

example {I : Type*} (n : ℕ) :
    permutationAverage (I := I) n 0 = 0 := by
  exact (permutationAverage n).map_zero

/-- Equation (12), PDF p.14: the trace-dual density, constructed by evaluation
on matrix units. The indices j,i are reversed since Tr(D E_ji) = D_ij. -/
def traceDensityDual {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (sigma : Matrix J J ℂ →ₗ[ℂ] Matrix I I ℂ) (D : Matrix I I ℂ) : Matrix J J ℂ :=
  Matrix.of (fun i j => (D * sigma (Matrix.single j i 1)).trace)

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (sigma : Matrix J J ℂ →ₗ[ℂ] Matrix I I ℂ) :
    traceDensityDual sigma 0 = 0 := by
  ext i j
  simp [traceDensityDual]

end QAlgorithms.Papers.Independent.Renew46.P23


