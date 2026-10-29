-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:53:11.288359+00:00
-- url     : https://prove2.me/theorems/3aa85575-d1b0-4835-86a8-90e2517a817c
-- title:
--   LIDT definitions: LDT / Preliminaries / BipartiteSelfConsistency / Local
-- statement:
--   This bundle provides the local bridge from bipartite self-consistency to left-lifted self-consistency. Under permutation invariance of the bipartite state, the result transfers the local-family estimate needed by the preliminary analytic reductions.
--
--   Principal definitions:
--   - `bipartiteSSC_implies_localSSC_liftLeft`: derives local self-consistency for left-lifted families from bipartite self-consistency.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Local.lean#L26-L174

-- Generated from MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Local.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
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
# Preliminary comparison theorems: bipartite self-consistency (local bridges)

Bridge lemmas connecting the bipartite self-consistency relation on a
permutation-invariant state to the single-sided local self-consistency relation
after a left/right lift of the family.

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Bridge lemma: for a permutation-invariant bipartite state, bipartite SSC
on local families implies local SSC on the left-lifted families.

Requires `PermInvState ψ` because the bipartite defect
`∑ ev(A_a ⊗ A_a)` and local defect `∑ ev(A_a² ⊗ I)` are generally
incomparable without symmetry; the permutation-invariance bridge
`ev(M ⊗ I) = ev(I ⊗ M)` makes the two notions equivalent.

The proof expands `qSDD ψ A.liftLeft A.liftRight`, uses
`PermInvState.swap_ev` to identify the left and right square terms, and
then reads off `∑ ev(A_a² ⊗ I) ≥ ∑ ev(A_a ⊗ A_a)` from
`qSDD_nonneg`. -/
lemma bipartiteSSC_implies_localSSC_liftLeft {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SSCRel ψ 𝒟 (IdxSubMeas.liftLeft A) δ := by
  intro ⟨hssc⟩
  constructor
  unfold sscError bipartiteSSCError at *
  calc
    avgOver 𝒟 (fun q => qSSCDefect ψ ((IdxSubMeas.liftLeft A) q))
      ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
          apply avgOver_mono
          intro q
          let M := A q
          let diagSq : Error :=
            ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a))
          let overlap : Error :=
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a))
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
                    rw [leftTensor_mul_leftTensor,
                      leftTensor_mul_rightTensor_eq_opTensor,
                      rightTensor_mul_leftTensor_eq_opTensor,
                      rightTensor_mul_rightTensor]
                    ring
          have hdiag_ge_overlap : overlap ≤ diagSq := by
            have hnonneg := qSDD_nonneg ψ M.liftLeft M.liftRight
            have hq :
                qSDD ψ M.liftLeft M.liftRight = 2 * (diagSq - overlap) := by
              unfold qSDD qSDDCore diagSq overlap
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
                      rw [hperm.swap_ev (M.outcome a * M.outcome a)]
                      ring
                _ = 2 *
                    ∑ a : Outcome,
                      (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                        ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
                      rw [← Finset.mul_sum]
                _ = 2 * (diagSq - overlap) := by
                      rw [show
                        (∑ a : Outcome,
                            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                              ev ψ (opTensor (M.outcome a) (M.outcome a)))) =
                          diagSq - overlap by
                            simp [diagSq, overlap, Finset.sum_sub_distrib]]
            rw [hq] at hnonneg
            nlinarith
          unfold qSSCDefect qBipartiteSSCDefect
          apply max_le_max le_rfl
          have :
              ev ψ (leftTensor (ι₂ := ι) M.total) - diagSq ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) - overlap := by
            linarith
          simpa [M, IdxSubMeas.liftLeft, SubMeas.liftLeft, diagSq,
            leftTensor_mul_leftTensor] using this
    _ ≤ δ := hssc

end MIPStarRE.LDT.Preliminaries

end

end LIDT


