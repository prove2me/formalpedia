-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:47:39.371147+00:00
-- url     : https://prove2.me/theorems/fce50f16-7505-46e5-aae1-d27019fbe744
-- title:
--   LIDT definitions: LDT / Preliminaries / SwitchSandwichMain / Completeness
-- statement:
--   This bundle supplies the completeness-transfer results for the switch-sandwich argument. It gives the core transfer estimate and its specialization when the comparison family is projective, which is the form consumed by the preliminary completion proof.
--
--   Principal definitions:
--   - `completenessTransfer_core`: the core completeness-transfer estimate.
--   - `completenessTransferProjectiveP`: the projective comparison-family specialization.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/Completeness.lean#L52-L207

-- Generated from MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/Completeness.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Switch-sandwich main: completeness estimate

`prop:switch-sandwich` assembled from the left and right transfer steps on a
normalized quantum state with a subprobability distribution.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT



private lemma completenessTransfer_core {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) :
    sddError ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ≤ ε →
    idxSubMeasMass ψ 𝒟 A ≥
      idxSubMeasMass ψ 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε := by
  intro hε
  let gap : Question → Error := fun q =>
    subMeasMass ψ ((IdxProjSubMeas.toIdxSubMeas P) q) - subMeasMass ψ (A q)
  let sdd : Question → Error := fun q =>
    qSDD ψ (A q) ((IdxProjSubMeas.toIdxSubMeas P) q)
  have hgap_pointwise : ∀ q, gap q ≤ 2 * Real.sqrt (sdd q) := by
    intro q
    let diagA : Error := ∑ a : Outcome, ev ψ ((A q).outcome a * (A q).outcome a)
    let diagP : Error := ∑ a : Outcome, ev ψ ((P q).outcome a * (P q).outcome a)
    let overlap : Error := ∑ a : Outcome, ev ψ ((A q).outcome a * (P q).outcome a)
    have hmassP_eq_diagP :
        subMeasMass ψ ((IdxProjSubMeas.toIdxSubMeas P) q) = diagP := by
      simpa [subMeasMass, IdxProjSubMeas.toIdxSubMeas, diagP] using
        (projSubMeas_diagMass_eq_mass ψ (P q)).symm
    have hdiagA_le_massA :
        diagA ≤ subMeasMass ψ (A q) := by
      simpa [subMeasMass, diagA] using subMeas_diagMass_le_mass ψ (A q)
    have hgap_left_raw :
        |diagA - overlap| ≤ Real.sqrt (sdd q) := by
      simpa [diagA, overlap, sdd, IdxProjSubMeas.toIdxSubMeas] using
        question_overlap_gap_left ψ hψ (A q) ((P q).toSubMeas)
    have hgap_left :
        overlap - diagA ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_left_raw]
    have hgap_right_raw :
        |overlap - diagP| ≤ Real.sqrt (sdd q) := by
      simpa [diagP, overlap, sdd, IdxProjSubMeas.toIdxSubMeas] using
        question_overlap_gap_right ψ hψ (A q) ((P q).toSubMeas)
    have hgap_right :
        diagP - overlap ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_right_raw]
    have hmass_gap :
        gap q ≤ diagP - diagA := by
      have hmassP_eq_diagP' :
          ev ψ ((IdxProjSubMeas.toIdxSubMeas P q).total) = diagP := by
        simpa [subMeasMass] using hmassP_eq_diagP
      dsimp [gap, subMeasMass]
      calc
        ev ψ ((IdxProjSubMeas.toIdxSubMeas P q).total) - ev ψ (A q).total
          ≤ ev ψ ((IdxProjSubMeas.toIdxSubMeas P q).total) - diagA := by
              exact sub_le_sub_left hdiagA_le_massA _
        _ = diagP - diagA := by rw [hmassP_eq_diagP']
    have hdiag_gap : diagP - diagA ≤ 2 * Real.sqrt (sdd q) := by
      linarith
    exact le_trans hmass_gap hdiag_gap
  have hgap_avg :
      avgOver 𝒟 gap ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) := by
    unfold avgOver
    refine Finset.sum_le_sum ?_
    intro q hq
    exact mul_le_mul_of_nonneg_left (hgap_pointwise q) (𝒟.nonnegative q)
  have hsqrt_avg_abs :
      |avgOver 𝒟 (fun q => Real.sqrt (sdd q))| ≤
        Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise 𝒟
        (fun q => Real.sqrt (sdd q))
        sdd
        (by
          intro q
          rw [abs_of_nonneg (Real.sqrt_nonneg _)])
        (by
          intro q
          exact qSDD_nonneg ψ (A q) ((IdxProjSubMeas.toIdxSubMeas P) q))
        h𝒟
  have hsqrt_avg_nonneg :
      0 ≤ avgOver 𝒟 (fun q => Real.sqrt (sdd q)) := by
    unfold avgOver
    exact Finset.sum_nonneg fun q hq =>
      mul_nonneg (𝒟.nonnegative q) (Real.sqrt_nonneg _)
  have hsqrt_avg :
      avgOver 𝒟 (fun q => Real.sqrt (sdd q)) ≤
        Real.sqrt (avgOver 𝒟 sdd) := by
    simpa [abs_of_nonneg hsqrt_avg_nonneg] using hsqrt_avg_abs
  have hscale_avg :
      avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) =
        2 * avgOver 𝒟 (fun q => Real.sqrt (sdd q)) := by
    unfold avgOver
    calc
      ∑ q ∈ 𝒟.support, 𝒟.weight q * (2 * Real.sqrt (sdd q))
        = ∑ q ∈ 𝒟.support, 2 * (𝒟.weight q * Real.sqrt (sdd q)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            ring
      _ = 2 * ∑ q ∈ 𝒟.support, 𝒟.weight q * Real.sqrt (sdd q) := by
            rw [← Finset.mul_sum]
  have hsdd_sqrt :
      avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) ≤
        2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := by
    rw [hscale_avg]
    calc
      2 * avgOver 𝒟 (fun q => Real.sqrt (sdd q))
        ≤ 2 * Real.sqrt (avgOver 𝒟 sdd) := by
            exact mul_le_mul_of_nonneg_left hsqrt_avg (by positivity)
      _ = 2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := by
            simp [sddError, sdd]
  have hgap_total :
      idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas P) -
          idxSubMeasMass ψ 𝒟 A
        ≤ 2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := by
    calc
      idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas P) -
          idxSubMeasMass ψ 𝒟 A
        = avgOver 𝒟 gap := by
            unfold idxSubMeasMass subMeasMass avgOver gap
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro q hq
            simp [mul_sub, subMeasMass]
      _ ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) := hgap_avg
      _ ≤ 2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := hsdd_sqrt
  have hsqrt_ε :
      Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) ≤ Real.sqrt ε := by
    exact Real.sqrt_le_sqrt hε
  have hgap_total' :
      idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas P) -
          idxSubMeasMass ψ 𝒟 A
        ≤ 2 * Real.sqrt ε := by
    exact le_trans hgap_total <| by
      exact mul_le_mul_of_nonneg_left hsqrt_ε (by positivity)
  linarith

/-- `prop:completeness-transfer-projective-P`.

The paper proof uses a normalized state and a probability distribution.
These are now explicit hypotheses `hψ` and `h𝒟`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) :
    SDDRel ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ε →
      CompTransferStmt ψ 𝒟 A P ε := by
  intro ⟨hε⟩
  exact {
    completenessTransfer :=
      completenessTransfer_core ψ 𝒟 hψ h𝒟 A P ε hε
  }

end MIPStarRE.LDT.Preliminaries

end

end LIDT


