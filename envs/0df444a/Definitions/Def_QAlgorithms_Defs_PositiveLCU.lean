-- Prove2me | Definitions.Def_QAlgorithms_Defs_PositiveLCU
-- name    : QAlgorithms_Defs_PositiveLCU
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:56.52737+00:00
-- url     : https://prove2.me/theorems/8fd5ba27-c93f-4ac2-9864-77b9b1fc3c10
-- title:
--   PositiveLCU
-- statement:
--   PositiveLCU
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\PositiveLCU.lean

import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Circuit
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.LCU

/-- QAlgorithms.LCU.PositiveCoefficients: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
structure PositiveCoefficients (J : Type*) [Fintype J] where
  beta : J → ℝ
  nonnegative : ∀ j, 0 ≤ beta j
  mass_pos : 0 < ∑ j, beta j

/-- QAlgorithms.LCU.coefficientMass: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def coefficientMass {J : Type*} [Fintype J] (C : PositiveCoefficients J) : ℝ := ∑ j, C.beta j

/-- QAlgorithms.LCU.coefficientState: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def coefficientState {J : Type*} [Fintype J] (C : PositiveCoefficients J) :
    EuclideanSpace ℂ J := WithLp.toLp 2 fun j => (Real.sqrt (C.beta j / coefficientMass C) : ℂ)

/-- QAlgorithms.LCU.IsCoefficientPreparation: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def IsCoefficientPreparation {J : Type*} [Fintype J] [DecidableEq J]
    (C : PositiveCoefficients J) (zero : J) (B : Matrix J J ℂ) : Prop :=
  B ∈ Matrix.unitaryGroup J ℂ ∧ act B (ket zero) = coefficientState C

/-- QAlgorithms.LCU.selectUnitary: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def selectUnitary {J I : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (V : J → Matrix.unitaryGroup I ℂ) : Matrix (J × I) (J × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (V q.1 : Matrix I I ℂ) p.2 q.2 else 0

/-- QAlgorithms.LCU.blockUnitary: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3, arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.10, arxiv-1511.02306v2 PDF p.14. Source domains are explicit below. -/
def blockUnitary {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I] [DecidableEq J]
    (B : Matrix.unitaryGroup J ℂ) (V : J → Matrix.unitaryGroup I ℂ) :
    Matrix (J × I) (J × I) ℂ :=
  Matrix.kronecker (star (B : Matrix J J ℂ)) 1 * selectUnitary V *
    Matrix.kronecker (B : Matrix J J ℂ) 1

example : coefficientMass (⟨fun _ : Unit => 3, by norm_num, by norm_num⟩) = 3 := by
  simp [coefficientMass]

example (C : PositiveCoefficients Unit) : coefficientState C () = 1 := by
  have h : 0 < C.beta () := by simpa using C.mass_pos
  simp [coefficientState, coefficientMass, div_self h.ne']

example {J I : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] (V : J → Matrix.unitaryGroup I ℂ) (j : J) (x y : I) :
    selectUnitary V (j,x) (j,y) = (V j : Matrix I I ℂ) x y := by simp [selectUnitary]

end QAlgorithms.LCU


