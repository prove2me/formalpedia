-- Prove2me | Definitions.Def_QAlgorithms_Defs_DiscreteAdiabaticData
-- name    : QAlgorithms_Defs_DiscreteAdiabaticData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:07.323147+00:00
-- url     : https://prove2.me/theorems/97dc14ca-4b32-428a-903d-5dea045022f9
-- title:
--   DiscreteAdiabaticData
-- statement:
--   DiscreteAdiabaticData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\DiscreteAdiabaticData.lean

import Mathlib

noncomputable section

open scoped Matrix ComplexConjugate ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.DiscreteAdiabatic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- QAlgorithms.DiscreteAdiabatic.walkOperator: arxiv-2111.08152v1 PDF p.4, arxiv-2111.08152v1 PDF p.14, arxiv-2111.08152v1 PDF p.15, arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6, arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.32, arxiv-2111.08152v1 PDF p.33, arxiv-2111.08152v1 PDF p.10. Source domains are explicit below. -/
def walkOperator (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H := U.toContinuousLinearEquiv.toContinuousLinearMap

/-- QAlgorithms.DiscreteAdiabatic.walkEvolution: arxiv-2111.08152v1 PDF p.4, arxiv-2111.08152v1 PDF p.14, arxiv-2111.08152v1 PDF p.15. Source domains are explicit below. -/
def walkEvolution {T : ℕ} (W : Fin (T+1) → H ≃ₗᵢ[ℂ] H) : Fin (T+1) → H →L[ℂ] H :=
  Fin.induction 1 (fun i V => walkOperator (W i.castSucc)*V)

/-- QAlgorithms.DiscreteAdiabatic.forwardDifference: arxiv-2111.08152v1 PDF p.5. Source domains are explicit below. -/
def forwardDifference {T : ℕ} (W : Fin (T+1) → H ≃ₗᵢ[ℂ] H)
    (k j : ℕ) (valid : j+k ≤ T) : H →L[ℂ] H :=
  ∑ i : Fin (k+1), ((-1 : ℂ)^(k-i.val)*(Nat.choose k i.val : ℂ)) •
    walkOperator (W ⟨j+i.val,by have := i.isLt; omega⟩)

/-- QAlgorithms.DiscreteAdiabatic.neighborEnvelope: arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6. Source domains are explicit below. -/
def neighborEnvelope {T : ℕ} (k : ℕ) (c : Fin (T+1) → ℝ≥0) (j : Fin (T+1)) : ℝ :=
  ((Finset.univ.filter fun i : Fin (T+1) => i.val+k ≤ T ∧
    |(i.val : ℤ)-(j.val : ℤ)| ≤ 1).sup c : ℝ≥0)

/-- QAlgorithms.DiscreteAdiabatic.CircularArc: arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6, arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.32, arxiv-2111.08152v1 PDF p.33. Source domains are explicit below. -/
structure CircularArc where
  lower : ℝ
  upper : ℝ
  ordered : lower ≤ upper
  proper : upper-lower < 2*Real.pi

/-- QAlgorithms.DiscreteAdiabatic.CircularArc.points: arxiv-2111.08152v1 PDF p.4, arxiv-2111.08152v1 PDF p.14, arxiv-2111.08152v1 PDF p.15, arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6, arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.32, arxiv-2111.08152v1 PDF p.33, arxiv-2111.08152v1 PDF p.10. Source domains are explicit below. -/
def CircularArc.points (A : CircularArc) : Set ℂ :=
  (fun theta : ℝ => Complex.exp (Complex.I*(theta : ℂ))) '' Set.Icc A.lower A.upper

/-- QAlgorithms.DiscreteAdiabatic.angularDistance: arxiv-2111.08152v1 PDF p.4, arxiv-2111.08152v1 PDF p.14, arxiv-2111.08152v1 PDF p.15, arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6, arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.32, arxiv-2111.08152v1 PDF p.33, arxiv-2111.08152v1 PDF p.10. Source domains are explicit below. -/
def angularDistance (u v : ℂ) : ℝ := |Complex.arg (u*star v)|

/-- QAlgorithms.DiscreteAdiabatic.arcSeparation: arxiv-2111.08152v1 PDF p.4, arxiv-2111.08152v1 PDF p.14, arxiv-2111.08152v1 PDF p.15, arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6, arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.32, arxiv-2111.08152v1 PDF p.33, arxiv-2111.08152v1 PDF p.10. Source domains are explicit below. -/
def arcSeparation (A B : CircularArc) : ℝ :=
  sInf ((fun uv : ℂ × ℂ => angularDistance uv.1 uv.2) '' (A.points ×ˢ B.points))

/-- QAlgorithms.DiscreteAdiabatic.ArcWindow: arxiv-2111.08152v1 PDF p.4, arxiv-2111.08152v1 PDF p.14, arxiv-2111.08152v1 PDF p.15, arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6, arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.32, arxiv-2111.08152v1 PDF p.33, arxiv-2111.08152v1 PDF p.10. Source domains are explicit below. -/
structure ArcWindow where
  selected : CircularArc
  complementary : CircularArc
  disjoint : Disjoint selected.points complementary.points

/-- QAlgorithms.DiscreteAdiabatic.SpectralBandData: arxiv-2111.08152v1 PDF p.4, arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6, arxiv-2111.08152v1 PDF p.10. Source domains are explicit below. -/
structure SpectralBandData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : ℕ) where
  positive : 0 < T
  threshold : ℕ
  admissible : threshold ≤ T
  W : Fin (T+1) → H ≃ₗᵢ[ℂ] H
  sigmaP : Fin (T+1) → Set ℂ
  sigmaQ : Fin (T+1) → Set ℂ
  partition : ∀ j, sigmaP j ∪ sigmaQ j = spectrum ℂ (walkOperator (W j))
  separate : ∀ j, Disjoint (sigmaP j) (sigmaQ j)
  window : (j : Fin (T+1)) → (k : Fin 3) → j.val+k.val ≤ T → ArcWindow
  contains : ∀ j k valid (l : ℕ) (hl : l ≤ k.val),
    sigmaP ⟨j.val+l,by have := j.isLt; omega⟩ ⊆ (window j k valid).selected.points ∧
    sigmaQ ⟨j.val+l,by have := j.isLt; omega⟩ ⊆ (window j k valid).complementary.points
  nested : ∀ j k l hk hl, k ≤ l →
    (window j k hk).selected.points ⊆ (window j l hl).selected.points ∧
    (window j k hk).complementary.points ⊆ (window j l hl).complementary.points

example {T : ℕ} (W : Fin (T+1) → H ≃ₗᵢ[ℂ] H) : walkEvolution W 0 = 1 := rfl

example {T : ℕ} (W : Fin (T+1) → H ≃ₗᵢ[ℂ] H) (j : ℕ) (hj : j ≤ T) :
    forwardDifference W 0 j hj = walkOperator (W ⟨j,by omega⟩) := by simp [forwardDifference]

example (c : Fin 2 → ℝ≥0) (j : Fin 2) : neighborEnvelope (T:=1) 2 c j = 0 := by
  have he : (Finset.univ.filter fun i : Fin 2 => i.val+2 ≤ 1 ∧ |(i.val : ℤ)-(j.val : ℤ)| ≤ 1) = ∅ := by
    ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
    omega
  simp [neighborEnvelope,he]

end QAlgorithms.DiscreteAdiabatic


