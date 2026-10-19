-- Prove2me | Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
-- name    : QAlgorithms_Defs_MitigationDecompositions
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:19:18.08736+00:00
-- url     : https://prove2.me/theorems/f7555c19-7118-44ae-9ce7-c95d64eddc6f
-- title:
--   MitigationDecompositions
-- statement:
--   MitigationDecompositions
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MitigationDecompositions.lean

import Definitions.Def_QAlgorithms_Defs_MitigationTomography
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.ErrorMitigation

/-- arxiv-1712.09271v2 PDF p.5; arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.13; arxiv-1712.09271v2 PDF p.14; arxiv-1712.09271v2 PDF p.18. -/
def preparationCoefficients {J : Type*} [Fintype J] [DecidableEq J]
    (MinHat : Matrix J J ℝ) (_invertible : IsUnit MinHat) (ideal : J → ℝ) : J → ℝ :=
  MinHat⁻¹.mulVec ideal

/-- arxiv-1712.09271v2 PDF p.5; arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.13; arxiv-1712.09271v2 PDF p.14; arxiv-1712.09271v2 PDF p.18. -/
def observableCoefficients {J : Type*} [Fintype J] [DecidableEq J]
    (MoutHat : Matrix J J ℝ) (_invertible : IsUnit MoutHat) (ideal : J → ℝ) : J → ℝ :=
  Matrix.vecMul ideal MoutHat⁻¹

/-- Invertible tensor synthesis as a linear equivalence, allowing any consistent basis labels
+(1712.09271 p.13, D1--D3). No reconstructed-operator equality is a field. -/
structure CompleteSynthesis (Rows Choices : Type*) [Fintype Rows] [Fintype Choices] where
  matrix : Matrix Rows Choices ℝ
  basis : (Choices → ℝ) ≃ₗ[ℝ] (Rows → ℝ)
  coordinates : ∀ v, basis v = matrix.mulVec v

/-- arxiv-1712.09271v2 PDF p.5; arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.13; arxiv-1712.09271v2 PDF p.14; arxiv-1712.09271v2 PDF p.18. -/
def compensationCoefficients {n : ℕ}
    (A : CompleteSynthesis (Fin n → Fin 4 × Fin 4) (Fin n → Fin 16))
    (ideal estimated : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) (lam : ℝ) :
    (Fin n → Fin 16) → ℝ :=
  A.basis.symm (fun p =>
    (ideal-lam • estimated) ((tensorVectorization n).symm p).1 ((tensorVectorization n).symm p).2)

/-- arxiv-1712.09271v2 PDF p.5; arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.13; arxiv-1712.09271v2 PDF p.14; arxiv-1712.09271v2 PDF p.18. -/
def inverseCoefficients {n : ℕ}
    (A : CompleteSynthesis (Fin n → Fin 4 × Fin 4) (Fin n → Fin 16))
    (ideal estimated : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ)
    (_hi : IsUnit ideal) (_he : IsUnit estimated) : (Fin n → Fin 16) → ℝ :=
  A.basis.symm (fun p =>
    (ideal*estimated⁻¹) ((tensorVectorization n).symm p).1 ((tensorVectorization n).symm p).2)

/-- Absolute coefficient mass, including zero (1712.09271 p.18, I11--I13). -/
def coefficientMass {J : Type*} [Fintype J] (q : J → ℝ) : ℝ := ∑ i, |q i|

/-- arxiv-1712.09271v2 PDF p.4; arxiv-1712.09271v2 PDF p.18; arxiv-1712.09271v2 PDF p.19. -/
def quasiprobabilityChoice {J : Type*} [Fintype J] (q : J → ℝ)
    (positive : 0 < coefficientMass q) : PMF J :=
  PMF.ofFintype (fun i => ENNReal.ofReal (|q i|/coefficientMass q)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (abs_nonneg _) positive.le)]
    rw [← Finset.sum_div]
    change ENNReal.ofReal (coefficientMass q/coefficientMass q) = 1
    rw [div_self positive.ne']; simp)

/-- Sanity check for the source model (arxiv-1712.09271v2 PDF p.4). -/
example {J : Type*} [Fintype J] : coefficientMass (0 : J → ℝ) = 0 := by simp [coefficientMass]

end QAlgorithms.ErrorMitigation


