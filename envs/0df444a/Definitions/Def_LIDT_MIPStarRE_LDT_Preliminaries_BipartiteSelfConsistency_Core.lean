-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:50:30.230646+00:00
-- url     : https://prove2.me/theorems/63909a6b-124b-430b-b995-3a6ffe38d262
-- title:
--   LIDT definitions: LDT / Preliminaries / BipartiteSelfConsistency / Core
-- statement:
--   This bundle establishes the core comparisons between left and right tensor placements in the bipartite self-consistency framework. Permutation invariance identifies the two placements, and the resulting inequalities compare qSDD distances with the bipartite SSC defect.
--
--   Principal definitions:
--   - `qSDDCore_rightTensor_eq_leftTensor_of_permInv`: identifies right and left tensor qSDD distances under permutation invariance.
--   - `qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect`: bounds the lifted qSDD distance by twice the bipartite SSC defect.
--   - `twoNotionsOfSelfConsistency`: compares the two self-consistency defects used in the paper.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Core.lean#L40-L323

-- Generated from MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Core.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Preliminary comparison theorems: bipartite self-consistency (core)

Core building blocks for bipartite self-consistency: reflexivity of the
question-level state-dependent distance `qSDD` and its lift to the family-level
`sddError`.

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT



/-- On a permutation-invariant bipartite state, the `qSDDCore` distance between
right-tensor placements of two local operator families equals the corresponding
left-tensor distance.

This is a shared tensor-placement helper for Bob/right-register variants of
`≈_δ` arguments.  The proof expands each squared-difference term and applies
`PermInvState.swap_ev` to `(A_a-B_a)^†(A_a-B_a)`. -/
lemma qSDDCore_rightTensor_eq_leftTensor_of_permInv
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (A B : Outcome → MIPStarRE.Quantum.Op ι) :
    qSDDCore ψ
      (fun a => rightTensor (ι₁ := ι) (A a))
      (fun a => rightTensor (ι₁ := ι) (B a)) =
    qSDDCore ψ
      (fun a => leftTensor (ι₂ := ι) (A a))
      (fun a => leftTensor (ι₂ := ι) (B a)) := by
  unfold qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  let D : MIPStarRE.Quantum.Op ι := A a - B a
  have hright_diff :
      rightTensor (ι₁ := ι) (A a) - rightTensor (ι₁ := ι) (B a) =
        rightTensor (ι₁ := ι) D := by
    simpa [rightTensor, opTensor, D] using
      (MIPStarRE.Quantum.kronecker_sub_right
        (A := (1 : MIPStarRE.Quantum.Op ι))
        (B₁ := A a) (B₂ := B a))
  have hleft_diff :
      leftTensor (ι₂ := ι) (A a) - leftTensor (ι₂ := ι) (B a) =
        leftTensor (ι₂ := ι) D := by
    simpa [D] using leftTensor_sub (ι₁ := ι) (ι₂ := ι) (A a) (B a)
  rw [hright_diff, hleft_diff]
  calc
    ev ψ ((rightTensor (ι₁ := ι) D)ᴴ * rightTensor (ι₁ := ι) D)
        = ev ψ (rightTensor (ι₁ := ι) (Dᴴ * D)) := by
          rw [rightTensor_conjTranspose, rightTensor_mul_rightTensor]
    _ = ev ψ (leftTensor (ι₂ := ι) (Dᴴ * D)) := by
          rw [← hperm.swap_ev (Dᴴ * D)]
    _ = ev ψ ((leftTensor (ι₂ := ι) D)ᴴ * leftTensor (ι₂ := ι) D) := by
          rw [leftTensor_conjTranspose, leftTensor_mul_leftTensor]

private lemma qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : PermInvState ψ)
    (M : SubMeas Outcome ι) :
    qSDD ψ M.liftLeft M.liftRight ≤ 2 * qBipartiteSSCDefect ψ M := by
  have h_expand :
      ∀ a : Outcome,
        ev ψ
            (((leftTensor (ι₂ := ι) (M.outcome a) -
                  rightTensor (ι₁ := ι) (M.outcome a))ᴴ) *
              (leftTensor (ι₂ := ι) (M.outcome a) -
                rightTensor (ι₁ := ι) (M.outcome a))) =
          ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
            ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
            2 * ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    intro a
    have hLherm :
        (leftTensor (ι₂ := ι) (M.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (M.outcome a) := by
      exact
        (Matrix.nonneg_iff_posSemidef.mp
          (leftTensor_nonneg (ι₂ := ι) (M.outcome_pos a))).isHermitian.eq
    have hRherm :
        (rightTensor (ι₁ := ι) (M.outcome a))ᴴ =
          rightTensor (ι₁ := ι) (M.outcome a) := by
      exact
        (Matrix.nonneg_iff_posSemidef.mp
          (rightTensor_nonneg (ι₁ := ι) (M.outcome_pos a))).isHermitian.eq
    calc
      ev ψ
          (((leftTensor (ι₂ := ι) (M.outcome a) -
                rightTensor (ι₁ := ι) (M.outcome a))ᴴ) *
            (leftTensor (ι₂ := ι) (M.outcome a) -
              rightTensor (ι₁ := ι) (M.outcome a)))
        =
          ev ψ
            (((leftTensor (ι₂ := ι) (M.outcome a) *
                  leftTensor (ι₂ := ι) (M.outcome a) -
                leftTensor (ι₂ := ι) (M.outcome a) *
                  rightTensor (ι₁ := ι) (M.outcome a)) -
              (rightTensor (ι₁ := ι) (M.outcome a) *
                  leftTensor (ι₂ := ι) (M.outcome a) -
                rightTensor (ι₁ := ι) (M.outcome a) *
                  rightTensor (ι₁ := ι) (M.outcome a)))) := by
            congr 1
            simp [hLherm, hRherm, sub_mul, mul_sub]
            abel
      _ =
          ev ψ
            (leftTensor (ι₂ := ι) (M.outcome a) *
              leftTensor (ι₂ := ι) (M.outcome a)) -
            ev ψ
              (leftTensor (ι₂ := ι) (M.outcome a) *
                rightTensor (ι₁ := ι) (M.outcome a)) -
            (ev ψ
                (rightTensor (ι₁ := ι) (M.outcome a) *
                  leftTensor (ι₂ := ι) (M.outcome a)) -
              ev ψ
                (rightTensor (ι₁ := ι) (M.outcome a) *
                  rightTensor (ι₁ := ι) (M.outcome a))) := by
            rw [ev_sub, ev_sub, ev_sub]
      _ =
          ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
            ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
            2 * ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            rw [leftTensor_mul_leftTensor, leftTensor_mul_rightTensor_eq_opTensor,
              rightTensor_mul_leftTensor_eq_opTensor, rightTensor_mul_rightTensor]
            ring
  have h_gap_eq :
      ∑ a : Outcome,
          (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
            ev ψ (opTensor (M.outcome a) (M.outcome a))) =
        ev ψ (leftTensor (ι₂ := ι) M.total) -
          ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    calc
      ∑ a : Outcome,
          (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
            ev ψ (opTensor (M.outcome a) (M.outcome a)))
        =
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (M.outcome a) -
                opTensor (M.outcome a) (M.outcome a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [ev_sub]
      _ =
          ev ψ
            (∑ a : Outcome,
              (leftTensor (ι₂ := ι) (M.outcome a) -
                opTensor (M.outcome a) (M.outcome a))) := by
            rw [← ev_sum ψ
              (fun a =>
                leftTensor (ι₂ := ι) (M.outcome a) -
                  opTensor (M.outcome a) (M.outcome a))]
      _ =
          ev ψ
            ((∑ a : Outcome, leftTensor (ι₂ := ι) (M.outcome a)) -
              ∑ a : Outcome, opTensor (M.outcome a) (M.outcome a)) := by
            rw [Finset.sum_sub_distrib]
      _ =
          ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ M.outcome, M.sum_eq_total]
            rw [ev_sub, ev_sum]
  have h_gap_nonneg :
      0 ≤ ev ψ (leftTensor (ι₂ := ι) M.total) -
        ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    calc
      0 ≤
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (M.outcome a) -
                opTensor (M.outcome a) (M.outcome a)) := by
            exact Finset.sum_nonneg fun a _ =>
              ev_nonneg_of_psd ψ _ <|
                sub_nonneg.mpr <|
                  opTensor_le_leftTensor
                    (M.outcome_pos a)
                    (M.outcome_le_one a)
      _ =
          ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            calc
              ∑ a : Outcome,
                  ev ψ
                    (leftTensor (ι₂ := ι) (M.outcome a) -
                      opTensor (M.outcome a) (M.outcome a))
                =
                  ∑ a : Outcome,
                    (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
                      ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    rw [ev_sub]
              _ =
                  ev ψ (leftTensor (ι₂ := ι) M.total) -
                    ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
                    exact h_gap_eq
  have h_pointwise :
      qSDD ψ M.liftLeft M.liftRight ≤
        2 *
          (ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
    unfold qSDD qSDDCore
    calc
      ∑ a : Outcome,
          ev ψ
            (((M.liftLeft.outcome a - M.liftRight.outcome a)ᴴ) *
              (M.liftLeft.outcome a - M.liftRight.outcome a))
        =
          ∑ a : Outcome,
            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
              ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
              2 * ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            simpa [SubMeas.liftLeft, SubMeas.liftRight] using h_expand a
      _ =
          ∑ a : Outcome,
            (2 *
              (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                ev ψ (opTensor (M.outcome a) (M.outcome a)))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hψ.swap_ev (M.outcome a * M.outcome a)]
            ring
      _ = 2 *
          ∑ a : Outcome,
            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
              ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            rw [← Finset.mul_sum]
      _ ≤ 2 *
          ∑ a : Outcome,
            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
              ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.sum_le_sum fun a _ => by
                apply sub_le_sub
                · exact ev_mono ψ _ _ <|
                    leftTensor_mono (ι₂ := ι) <|
                      MIPStarRE.Quantum.sq_le_self
                        (M.outcome_pos a)
                        (M.outcome_le_one a)
                · exact le_rfl
            · norm_num
      _ =
          2 *
            (ev ψ (leftTensor (ι₂ := ι) M.total) -
              ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            rw [h_gap_eq]
  unfold qBipartiteSSCDefect
  rw [max_eq_right h_gap_nonneg]
  exact h_pointwise

/-- `prop:two-notions-of-self-consistency`.

If the indexed sub-measurement `A` is bipartite-strongly-self-consistent
on the permutation-invariant state `ψ` (i.e., `BipartiteSSCRel ψ 𝒟 A δ`,
meaning `∑ₐ ev ψ (Aₐ ⊗ I) − ∑ₐ ev ψ (Aₐ ⊗ Aₐ) ≤ δ`), then the left
and right lifts are close: `SDDRel ψ 𝒟 (liftLeft A) (liftRight A) (2 * δ)`.

**Paper proof sketch:**
1. Expand `∑ₐ ev ψ ((Aₐ⊗I − I⊗Aₐ)² )`.
2. Using Kronecker mixed-product rule and PermInvState.swap_ev, this
   equals `2 · (∑ₐ ev ψ (Aₐ²⊗I) − ∑ₐ ev ψ (Aₐ⊗Aₐ))`.
3. Since `Aₐ² ≤ Aₐ` (sub-measurement bound), we get
   `≤ 2 · (∑ₐ ev ψ (Aₐ⊗I) − ∑ₐ ev ψ (Aₐ⊗Aₐ)) = 2 · bipartiteSSCDefect`.
4. Average over 𝒟 and apply the BipartiteSSCRel hypothesis. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    (PermInvState ψ ∧ BipartiteSSCRel ψ 𝒟 A δ) →
      SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A)
        (IdxSubMeas.liftRight A) (2 * δ) := by
  intro ⟨hψ, hssc⟩
  rcases hssc with ⟨hssc⟩
  constructor
  unfold sddError
  calc
    avgOver 𝒟
        (fun q =>
          qSDD ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftRight A) q))
      ≤
        avgOver 𝒟 (fun q => 2 * qBipartiteSSCDefect ψ (A q)) := by
          apply avgOver_mono
          intro q
          simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
            SubMeas.liftLeft, SubMeas.liftRight,
            leftPlacedSubMeas, rightPlacedSubMeas] using
            qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect ψ hψ (A q)
    _ = 2 * avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
          rw [avgOver_const_mul]
    _ ≤ 2 * δ := by
          have hssc' : avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) ≤ δ := by
            simpa [bipartiteSSCError] using hssc
          exact mul_le_mul_of_nonneg_left hssc' (by norm_num)

end MIPStarRE.LDT.Preliminaries

end

end LIDT


