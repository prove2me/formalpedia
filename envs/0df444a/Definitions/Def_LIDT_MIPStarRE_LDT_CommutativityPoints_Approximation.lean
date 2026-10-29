-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
-- name    : LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:42:56.137532+00:00
-- url     : https://prove2.me/theorems/fb394e1a-cbe8-4255-936f-b1139ccc811f
-- title:
--   LIDT definitions: LDT / CommutativityPoints / Approximation
-- statement:
--   This bundle supplies the finite-field point and line reindexing used by the commutativity argument at the last restricted coordinate. It identifies the final restricted diagonal sample with a full diagonal line and defines the evaluated answer families used at the distinguished parameter.
--
--   Principal definitions:
--   - `lastRestrictionIndex`: the final restriction index in the restricted diagonal-line test.
--   - `pointNextEquiv`: the decomposition of a next-level point into a truncated point and its final coordinate.
--   - `opFamilyOfOutcome`: the operator family reconstructed from outcome operators, with total equal to their sum.
--   - `lastRestrictedDirectionEquiv`: the equivalence between a final restricted direction and a full point of the next field space.
--   - `lastRestrictedSampleEquivDiagonalLine`: the equivalence between a final restricted sample and a complete diagonal line.
--   - `rebasedLastRestrictedQuestionEquiv`: the rebase equivalence that moves the distinguished base point to the queried parameter.
--   - `rawDiagonalLineAnswerFamily`: the raw restricted diagonal answer family evaluated at `zeroCoord`.
--   - `rawAnswerDiagonalLineAnswerFamily`: the corresponding family for answer-valued restricted diagonal measurements.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/CommutativityPoints/Approximation.lean#L24-L494

-- Generated from MIPStarRE/LDT/CommutativityPoints/Approximation.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 10 — commutativity points approximation layer

Restricted-diagonal approximation infrastructure for commutativity at points.
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

/-- The final restriction index, corresponding to the paper's `m`-restricted
diagonal-lines test. -/
 def lastRestrictionIndex (params : Parameters) : Fin params.m :=
  ⟨params.m - 1, Nat.sub_lt params.hm Nat.zero_lt_one⟩

/-- Decompose a point in `Point params.next` into its truncated point and final coordinate. -/
def pointNextEquiv (params : Parameters) [FieldModel params.q] :
    Point params.next ≃ Point params × Fq params where
  toFun := fun u => (truncatePoint params u, pointHeight params u)
  invFun := fun ux => appendPoint params ux.1 ux.2
  left_inv := fun u => by
    funext i
    by_cases h : i.1 < params.m
    · simp [appendPoint, truncatePoint, h]
    · have hi : i.1 = params.m := by
        have hi_lt : i.1 < params.m + 1 := by
          simpa [Parameters.next] using i.2
        omega
      have hlast : i = lastCoord params := by
        apply Fin.ext
        simp [lastCoord, hi]
      simp [appendPoint, truncatePoint, pointHeight, hlast]
  right_inv := fun ⟨u, x⟩ => by
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]

/-- Decompose the uniform average over a next-level point into a height and prefix average. -/
lemma avgOver_uniform_pointNext_decompose
    (params : Parameters) [FieldModel params.q]
    (f : Point params.next → Error) :
    avgOver (uniformDistribution (Point params.next)) f =
      avgOver (uniformDistribution (Fq params))
        (fun x => avgOver (uniformDistribution (Point params))
          (fun u => f (appendPoint params u x))) := by
  simpa [pointNextEquiv] using
    (MIPStarRE.LDT.avgOver_uniform_equiv_prod_swap
      (e := pointNextEquiv params) (f := f))



/-- Build an operator family from its outcomes, taking the total to be their sum. -/
noncomputable def opFamilyOfOutcome {Outcome : Type*} [Fintype Outcome]
    (outcome : Outcome → MIPStarRE.Quantum.Op ι) :
    OpFamily Outcome ι where
  outcome := outcome
  total := ∑ a : Outcome, outcome a

abbrev pointPairOutcomeSwapEquiv (params : Parameters) :
    PointPairOutcome params ≃ PointPairOutcome params :=
  Equiv.prodComm _ _

private lemma lastRestrictionIndex_val_succ
    (params : Parameters) :
    (lastRestrictionIndex params).val + 1 = params.m := by
  have hm := params.hm
  dsimp [lastRestrictionIndex]
  omega

/-- At the final restriction index, a restricted diagonal direction records all
`m` coordinates, so it is equivalent to an unrestricted point of `Point params`. -/
 noncomputable def lastRestrictedDirectionEquiv
    (params : Parameters)
    [FieldModel params.q] :
    (Fin ((lastRestrictionIndex params).val + 1) → Fq params) ≃ Point params where
  toFun := extendRestrictedDirection (lastRestrictionIndex params)
  invFun := fun direction i =>
    direction ⟨i.val, by
      have h := lastRestrictionIndex_val_succ params
      omega⟩
  left_inv := fun free => by
    funext i
    have hlt : i.val < params.m := by
      have h := lastRestrictionIndex_val_succ params
      omega
    have hle : (⟨i.val, hlt⟩ : Fin params.m).val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨i.val, Nat.lt_succ_of_le hle⟩ : Fin ((lastRestrictionIndex params).val + 1)) = i := by
      ext
      rfl
    rw [← hidx]
    simp [extendRestrictedDirection, hle]
  right_inv := fun direction => by
    funext k
    have hk : k.val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨k.val, by
            have h := lastRestrictionIndex_val_succ params
            omega⟩ : Fin params.m) = k := by
      ext
      rfl
    rw [← hidx]
    simp [extendRestrictedDirection, hk]

/-- At the final restriction index, a restricted diagonal sample is exactly a
full diagonal line: the sample point becomes the base point and the restricted
direction determines all line coefficients. -/
 noncomputable def lastRestrictedSampleEquivDiagonalLine
    (params : Parameters)
    [FieldModel params.q] :
    RestrictedDiagonalSample params (lastRestrictionIndex params) ≃ DiagonalLine params where
  toFun := fun s =>
    { base := s.1
      direction := lastRestrictedDirectionEquiv params s.2 }
  invFun := fun ℓ =>
    (ℓ.base, (lastRestrictedDirectionEquiv params).symm ℓ.direction)
  left_inv := fun ⟨base, free⟩ => by
    refine Prod.ext rfl ?_
    funext i
    have hlt : i.val < params.m := by
      have h := lastRestrictionIndex_val_succ params
      omega
    have hle : (⟨i.val, hlt⟩ : Fin params.m).val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨i.val, Nat.lt_succ_of_le hle⟩ : Fin ((lastRestrictionIndex params).val + 1)) = i := by
      ext
      rfl
    rw [← hidx]
    simp [lastRestrictedDirectionEquiv, extendRestrictedDirection, hle]
  right_inv := fun ⟨base, direction⟩ => by
    change
      ({ base := base,
         direction := extendRestrictedDirection (lastRestrictionIndex params)
           (fun i => direction ⟨i.val, by
             have h := lastRestrictionIndex_val_succ params
             omega⟩) } : DiagonalLine params) =
      ({ base := base, direction := direction } : DiagonalLine params)
    congr
    funext k
    have hk : k.val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨k.val, by
            have h := lastRestrictionIndex_val_succ params
            omega⟩ : Fin params.m) = k := by
      ext
      rfl
    rw [← hidx]
    simp [extendRestrictedDirection, hk]

/-- Rebase the last restricted diagonal sample so that its distinguished base
point appears at the queried parameter. This identifies the corrected diagonal
test sample space with the shared point-with-diagonal-line questions used in
the commutativity-at-points argument. -/
 noncomputable def rebasedLastRestrictedQuestionEquiv
    (params : Parameters)
    [FieldModel params.q] :
    (RestrictedDiagonalSample params (lastRestrictionIndex params) × Fq params) ≃
      PointDiagonalLineQuestion params where
  toFun := fun st =>
    let ℓ := lastRestrictedSampleEquivDiagonalLine params st.1
    (DiagonalLine.rebaseAt ℓ (subCoord zeroCoord st.2), st.2)
  invFun := fun q =>
    let ℓ := DiagonalLine.rebaseAt q.1 q.2
    ((lastRestrictedSampleEquivDiagonalLine params).symm ℓ, q.2)
  left_inv := fun ⟨s, t⟩ => by
    simp [DiagonalLine.rebaseAt_rebase, addCoord_subCoord_left]
  right_inv := fun ⟨ℓ, t⟩ => by
    simp [DiagonalLine.rebaseAt_rebase, addCoord_subCoord_right]

/-- Evaluate each restricted diagonal measurement at the distinguished base
parameter `zeroCoord`, matching the corrected paper definition of the diagonal
branch. -/
 noncomputable def rawDiagonalLineAnswerFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    postprocess
      ((strategy.diagonalMeasurement { base := s.1, direction := v }).toSubMeas)
      (· zeroCoord)







/-- Evaluate each answer-valued restricted diagonal measurement at the
distinguished base parameter `zeroCoord`. -/
 noncomputable def rawAnswerDiagonalLineAnswerFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    postprocess
      ((strategy.diagonalMeasurement { base := s.1, direction := v }).toSubMeas)
      (· zeroCoord)







end MIPStarRE.LDT.CommutativityPoints

end

end LIDT


