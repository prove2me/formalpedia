-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:55:32.440181+00:00
-- url     : https://prove2.me/theorems/0a8d4508-7b62-44f4-8997-62d4ac42a3bd
-- title:
--   LIDT definitions: LDT / Preliminaries / SelfConsistency / DataProcessing
-- statement:
--   This bundle defines the two ingredients of the self-consistency data-processing step. It records the wrong-register estimate and then derives the data-processing inequality showing that self-consistency controls the processed measurement family.
--
--   Principal definitions:
--   - `wrongSideEstimate`: bounds the contribution evaluated on the wrong register.
--   - `selfConsistencyImpliesDataProcessing`: derives the data-processing bound from self-consistency.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SelfConsistency/DataProcessing.lean#L28-L343

-- Generated from MIPStarRE/LDT/Preliminaries/SelfConsistency/DataProcessing.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Self-consistency: data processing

`prop:self-consistency-implies-data-processing`: self-consistency implies that
postprocessing a measurement cannot substantially decrease consistency.

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:self-consistency-implies-data-processing`.

Proof:
1. First prove the “wrong-side” estimate
   `P_[f_q] ⊗ I ≈_{2δ + 4√ε} I ⊗ A_[f_q]` by:
   - expanding the `qSDD` square,
   - bounding the mass of `P` via `completenessTransferProjectiveP`,
   - comparing the mixed overlap with the diagonal overlap of `A`,
   - and using SSC plus question-dependent postprocessing monotonicity.
2. Apply `twoNotionsOfSelfConsistencyAfterEvaluation` to obtain
   `A_[f_q] ⊗ I ≈_{2δ} I ⊗ A_[f_q]`.
3. Use the `SDDRel` triangle inequality to conclude
   `P_[f_q] ⊗ I ≈_{8δ + 8√ε} A_[f_q] ⊗ I`. -/
private lemma wrongSideEstimate
    {Question α β : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question α ι)
    (P : IdxProjSubMeas Question α ι)
    (δ ε : Error) (f : Question → α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
      (IdxSubMeas.liftLeft A) ε →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) (f q)))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) (f q)))
        (2 * δ + 4 * Real.sqrt ε) := by
  intro hssc ⟨hε⟩
  let PL : IdxProjSubMeas Question α (ι × ι) := fun q =>
    { toSubMeas := ((P q).toSubMeas).liftLeft
      proj := fun a => by simp [SubMeas.liftLeft, leftTensor_mul_leftTensor, (P q).proj a] }
  let LPf : IdxSubMeas Question β (ι × ι) :=
    IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) (f q))
  let RAf : IdxSubMeas Question β (ι × ι) :=
    IdxSubMeas.liftRight (fun q => postprocess (A q) (f q))
  let crossPost : Question → Error := fun q =>
    qMatchMass ψ (LPf q) (RAf q)
  let crossOrig : Question → Error := fun q =>
    qMatchMass ψ
      ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P)) q)
      ((IdxSubMeas.liftRight A) q)
  let overlapA : Question → Error := fun q =>
    qMatchMass ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftRight A) q)
  have hcomp :
      CompTransferStmt ψ 𝒟 (IdxSubMeas.liftLeft A) PL ε := by
    apply completenessTransferProjectiveP ψ 𝒟 hψ h𝒟 (IdxSubMeas.liftLeft A) PL ε
    exact
      sddRel_symm ψ 𝒟
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
        (IdxSubMeas.liftLeft A) ε
        ⟨hε⟩
  have hmassP :
      idxSubMeasMass ψ 𝒟 LPf ≤
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) + 2 * Real.sqrt ε := by
    have hpost :
        idxSubMeasMass ψ 𝒟 LPf =
          idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas PL) := by
      unfold idxSubMeasMass subMeasMass avgOver LPf PL
      refine Finset.sum_congr rfl ?_
      intro q hq
      change
        𝒟.weight q *
            ev ψ (((postprocess ((P q).toSubMeas) (f q)).liftLeft).total) =
          𝒟.weight q * ev ψ ((((P q).toSubMeas).liftLeft).total)
      simp [SubMeas.liftLeft, postprocess_total]
    have hbase := hcomp.completenessTransfer
    rw [hpost]
    linarith
  have hmassA :
      idxSubMeasMass ψ 𝒟 RAf =
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) := by
    unfold idxSubMeasMass subMeasMass avgOver RAf
    refine Finset.sum_congr rfl ?_
    intro q hq
    change
      𝒟.weight q *
          ev ψ (rightTensor (ι₁ := ι) ((postprocess (A q) (f q)).total)) =
      𝒟.weight q * ev ψ (leftTensor (ι₂ := ι) ((A q).total))
    rw [postprocess_total, ← hperm.swap_ev ((A q).total)]
  have hcross_post_ge :
      avgOver 𝒟 crossPost ≥ avgOver 𝒟 crossOrig := by
    unfold avgOver crossPost crossOrig
    refine Finset.sum_le_sum ?_
    intro q hq
    exact mul_le_mul_of_nonneg_left
      (qMatchMass_leftRight_postprocess_ge ψ ((P q).toSubMeas) (A q) (f q))
      (𝒟.nonnegative q)
  have hcross_close :
      |avgOver 𝒟 crossOrig - avgOver 𝒟 overlapA| ≤ Real.sqrt ε := by
    simpa [crossOrig, overlapA, qMatchMass, IdxProjSubMeas.toIdxSubMeas,
      IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
      easyApproxFromApproxDelta ψ hψ 𝒟 h𝒟
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
        (IdxSubMeas.liftLeft A)
        (IdxSubMeas.liftRight A)
        ε
        ⟨hε⟩
  have hcross_ge :
      avgOver 𝒟 crossPost ≥ avgOver 𝒟 overlapA - Real.sqrt ε := by
    linarith [hcross_post_ge, (abs_le.mp hcross_close).1]
  have hssc_gap :
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) - avgOver 𝒟 overlapA ≤ δ := by
    rcases hssc with ⟨hssc⟩
    calc
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) - avgOver 𝒟 overlapA
        = avgOver 𝒟
            (fun q =>
              subMeasMass ψ ((IdxSubMeas.liftLeft A) q) - overlapA q) := by
              unfold idxSubMeasMass subMeasMass avgOver overlapA
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro q hq
              ring
      _ ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
            apply avgOver_mono
            intro q
            have hdef :
                qBipartiteSSCDefect ψ (A q) =
                  max 0 (subMeasMass ψ ((IdxSubMeas.liftLeft A) q) - overlapA q) := by
              simp [qBipartiteSSCDefect, overlapA, qMatchMass, subMeasMass,
                IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
                leftTensor_mul_rightTensor_eq_opTensor]
            rw [hdef]
            exact le_max_right 0 _
      _ ≤ δ := by
            simpa [bipartiteSSCError, overlapA, qMatchMass, IdxSubMeas.liftLeft,
              IdxSubMeas.liftRight] using hssc
  have hpointwise :
      ∀ q, qSDD ψ (LPf q) (RAf q) ≤
        subMeasMass ψ (LPf q) + subMeasMass ψ (RAf q) - 2 * crossPost q := by
    intro q
    let diagP : Error := ∑ b : β, ev ψ ((LPf q).outcome b * (LPf q).outcome b)
    let diagA : Error := ∑ b : β, ev ψ ((RAf q).outcome b * (RAf q).outcome b)
    have hdiagP_le :
        diagP ≤ subMeasMass ψ (LPf q) := by
      simpa [diagP, subMeasMass] using subMeas_diagMass_le_mass ψ (LPf q)
    have hdiagA_le :
        diagA ≤ subMeasMass ψ (RAf q) := by
      simpa [diagA, subMeasMass] using subMeas_diagMass_le_mass ψ (RAf q)
    have h_expand : qSDD ψ (LPf q) (RAf q) = diagP + diagA - 2 * crossPost q := by
      have hterm :
          ∀ b : β,
            ev ψ (((LPf q).outcome b - (RAf q).outcome b)ᴴ *
                ((LPf q).outcome b - (RAf q).outcome b)) =
              ev ψ ((LPf q).outcome b * (LPf q).outcome b) +
                ev ψ ((RAf q).outcome b * (RAf q).outcome b) -
                2 * ev ψ ((LPf q).outcome b * (RAf q).outcome b) := by
        intro b
        have hcomm :
            ev ψ ((RAf q).outcome b * (LPf q).outcome b) =
              ev ψ ((LPf q).outcome b * (RAf q).outcome b) := by
          exact
            ev_mul_comm_of_psd ψ _ _
              ((RAf q).outcome_pos b)
              ((LPf q).outcome_pos b)
        calc
          ev ψ (((LPf q).outcome b - (RAf q).outcome b)ᴴ *
              ((LPf q).outcome b - (RAf q).outcome b))
            =
              ev ψ
                ((((LPf q).outcome b * (LPf q).outcome b) -
                    (LPf q).outcome b * (RAf q).outcome b) -
                  ((RAf q).outcome b * (LPf q).outcome b -
                    (RAf q).outcome b * (RAf q).outcome b)) := by
                  congr 1
                  simp [sub_mul, mul_sub, SubMeas.outcome_hermitian]
                  abel
          _ =
              ev ψ ((LPf q).outcome b * (LPf q).outcome b) -
                ev ψ ((LPf q).outcome b * (RAf q).outcome b) -
                (ev ψ ((RAf q).outcome b * (LPf q).outcome b) -
                  ev ψ ((RAf q).outcome b * (RAf q).outcome b)) := by
                    rw [ev_sub, ev_sub, ev_sub]
          _ =
              ev ψ ((LPf q).outcome b * (LPf q).outcome b) +
                ev ψ ((RAf q).outcome b * (RAf q).outcome b) -
                2 * ev ψ ((LPf q).outcome b * (RAf q).outcome b) := by
                  rw [hcomm]
                  ring
      unfold qSDD qSDDCore crossPost
      calc
        ∑ b : β,
            ev ψ (((LPf q).outcome b - (RAf q).outcome b)ᴴ *
              ((LPf q).outcome b - (RAf q).outcome b))
          =
            ∑ b : β,
              (ev ψ ((LPf q).outcome b * (LPf q).outcome b) +
                ev ψ ((RAf q).outcome b * (RAf q).outcome b) -
                2 * ev ψ ((LPf q).outcome b * (RAf q).outcome b)) := by
                  refine Finset.sum_congr rfl ?_
                  intro b hb
                  exact hterm b
        _ = diagP + diagA - 2 * qMatchMass ψ (LPf q) (RAf q) := by
              unfold diagP diagA qMatchMass
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [h_expand]
    linarith
  constructor
  calc
    sddError ψ 𝒟 LPf RAf
      ≤ avgOver 𝒟
          (fun q =>
            subMeasMass ψ (LPf q) + subMeasMass ψ (RAf q) - 2 * crossPost q) := by
              unfold sddError
              apply avgOver_mono
              intro q
              exact hpointwise q
    _ = idxSubMeasMass ψ 𝒟 LPf +
          idxSubMeasMass ψ 𝒟 RAf -
            2 * avgOver 𝒟 crossPost := by
              unfold idxSubMeasMass subMeasMass avgOver
              calc
                ∑ q ∈ 𝒟.support,
                    𝒟.weight q *
                      (ev ψ (LPf q).total + ev ψ (RAf q).total -
                        2 * crossPost q)
                  =
                    ∑ q ∈ 𝒟.support,
                      (𝒟.weight q * ev ψ (LPf q).total +
                        (𝒟.weight q * ev ψ (RAf q).total -
                          2 * (𝒟.weight q * crossPost q))) := by
                          refine Finset.sum_congr rfl ?_
                          intro q hq
                          ring
                _ =
                    (∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (LPf q).total) +
                      ((∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (RAf q).total) -
                        2 * ∑ q ∈ 𝒟.support, 𝒟.weight q * crossPost q) := by
                          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
                _ = idxSubMeasMass ψ 𝒟 LPf +
                    idxSubMeasMass ψ 𝒟 RAf -
                      2 * avgOver 𝒟 crossPost := by
                          simp [idxSubMeasMass, avgOver, subMeasMass]
                          ring
    _ ≤
        (idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) + 2 * Real.sqrt ε) +
          idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) -
            2 * (avgOver 𝒟 overlapA - Real.sqrt ε) := by
              rw [hmassA]
              linarith
    _ ≤ 2 * δ + 4 * Real.sqrt ε := by
          linarith

/-- `prop:self-consistency-implies-data-processing`.

A projective approximation to a strongly self-consistent family remains close
after postprocessing on the left register. The proof combines the wrong-side
estimate, self-consistency after evaluation, and the `SDDRel` triangle
inequality. -/
theorem selfConsistencyImpliesDataProcessing
    {Question α β : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question α ι)
    (P : IdxProjSubMeas Question α ι)
    (δ ε : Error) (f : Question → α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
      (IdxSubMeas.liftLeft A) ε →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) (f q)))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) (f q)))
        (8 * δ + 8 * Real.sqrt ε) := by
  intro hssc hsdd
  have hwrong :
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) (f q)))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) (f q)))
        (2 * δ + 4 * Real.sqrt ε) :=
    wrongSideEstimate ψ hperm hψ 𝒟 h𝒟 A P δ ε f hssc hsdd
  have hself :
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) (f q)))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) (f q)))
        (2 * δ) :=
    twoNotionsOfSelfConsistencyAfterEvaluation ψ hperm 𝒟 A δ f hssc
  have hself_symm :
      SDDRel ψ 𝒟
        (IdxSubMeas.liftRight (fun q => postprocess (A q) (f q)))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) (f q)))
        (2 * δ) :=
    sddRel_symm ψ 𝒟
      (IdxSubMeas.liftLeft (fun q => postprocess (A q) (f q)))
      (IdxSubMeas.liftRight (fun q => postprocess (A q) (f q)))
      (2 * δ)
      hself
  have htri :
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) (f q)))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) (f q)))
        (2 * ((2 * δ + 4 * Real.sqrt ε) + (2 * δ))) := by
    exact
      stateDependentDistanceRel_triangle ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) (f q)))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) (f q)))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) (f q)))
        (2 * δ + 4 * Real.sqrt ε) (2 * δ)
        hwrong hself_symm
  exact
    stateDependentDistanceRel_mono ψ 𝒟
      (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) (f q)))
      (IdxSubMeas.liftLeft (fun q => postprocess (A q) (f q)))
      (2 * ((2 * δ + 4 * Real.sqrt ε) + (2 * δ)))
      (8 * δ + 8 * Real.sqrt ε)
      (by linarith)
      htri

end MIPStarRE.LDT.Preliminaries

end

end LIDT


