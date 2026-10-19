-- Prove2me | Definitions.Def_QAlgorithms_Defs_CKSFourierData
-- name    : QAlgorithms_Defs_CKSFourierData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:13.259368+00:00
-- url     : https://prove2.me/theorems/6ce0e2bf-5234-4e11-b223-d365d9068226
-- title:
--   CKSFourierData
-- statement:
--   CKSFourierData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\CKSFourierData.lean

import Definitions.Def_QAlgorithms_Defs_PositiveLCU
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.CKSFourier

/-- QAlgorithms.CKSFourier.Grid: arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.13. Source domains are explicit below. -/
structure Grid where
  J : ℕ
  K : ℕ
  J_pos : 1 ≤ J
  K_pos : 1 ≤ K
  deltaY : ℝ
  deltaZ : ℝ
  deltaY_pos : 0 < deltaY
  deltaZ_pos : 0 < deltaZ

/-- QAlgorithms.CKSFourier.Grid.Index: arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.13, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
abbrev Grid.Index (G : Grid) := Fin G.J × Fin (2*G.K+1)

/-- QAlgorithms.CKSFourier.Grid.y: arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.13, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def Grid.y (G : Grid) (j : Fin G.J) : ℝ := j.val*G.deltaY

/-- QAlgorithms.CKSFourier.Grid.z: arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.13, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def Grid.z (G : Grid) (k : Fin (2*G.K+1)) : ℝ := ((k.val : ℤ)-(G.K : ℤ))*G.deltaZ

/-- QAlgorithms.CKSFourier.Grid.beta: arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.13, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def Grid.beta (G : Grid) (index : G.Index) : ℝ :=
  G.deltaY*G.deltaZ*|G.z index.2| *Real.exp (-(G.z index.2)^2/2)/Real.sqrt (2*Real.pi)

/-- QAlgorithms.CKSFourier.Grid.coefficients: arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.13, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def Grid.coefficients (G : Grid) : LCU.PositiveCoefficients G.Index := by
  classical
  have hy := G.deltaY_pos
  have hzpos := G.deltaZ_pos
  have hpi := Real.pi_pos
  refine ⟨G.beta, fun i => by unfold Grid.beta; positivity, ?_⟩
  let i : G.Index := (⟨0,by have := G.J_pos; omega⟩,⟨G.K+1,by have := G.K_pos; omega⟩)
  have hz : G.z i.2 = G.deltaZ := by simp [Grid.z,i]
  have hp : 0 < G.beta i := by unfold Grid.beta; rw [hz]; positivity
  exact lt_of_lt_of_le hp (Finset.single_le_sum (fun j _ => by unfold Grid.beta; positivity) (Finset.mem_univ i))

/-- QAlgorithms.CKSFourier.inverseApproximant: arxiv-1511.02306v2 PDF p.10. Source domains are explicit below. -/
def inverseApproximant (G : Grid) (x : ℝ) : ℂ :=
  Complex.I/(Real.sqrt (2*Real.pi) : ℂ)*∑ j : Fin G.J, ∑ k : Fin (2*G.K+1),
    (G.deltaY*G.deltaZ*G.z k*Real.exp (-(G.z k)^2/2) : ℂ)*
      Complex.exp (-Complex.I*(x*G.y j*G.z k : ℝ))

/-- QAlgorithms.CKSFourier.coefficientMass: arxiv-1511.02306v2 PDF p.12. Source domains are explicit below. -/
def coefficientMass (G : Grid) : ℝ := LCU.coefficientMass G.coefficients

/-- QAlgorithms.CKSFourier.coefficientState: arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def coefficientState (G : Grid) : EuclideanSpace ℂ G.Index := LCU.coefficientState G.coefficients

/-- Matrix form of equation (18), arxiv-1511.02306v2 PDF p.10. -/
def matrixInverseApproximant {I : Type*} [Fintype I] [DecidableEq I]
    (G : Grid) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ j : Fin G.J, ∑ k : Fin (2*G.K+1),
    (Complex.I/(Real.sqrt (2*Real.pi) : ℂ)*(G.deltaY*G.deltaZ*G.z k*Real.exp (-(G.z k)^2/2) : ℂ)) •
      NormedSpace.exp (-(Complex.I*(G.y j*G.z k : ℝ)) • A)

example (G : Grid) : G.z ⟨G.K,by omega⟩ = 0 := by simp [Grid.z]

example (G : Grid) (j : Fin G.J) : G.beta (j,⟨G.K,by omega⟩) = 0 := by simp [Grid.beta,Grid.z]


end QAlgorithms.CKSFourier


