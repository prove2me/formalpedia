-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:58:03.448409+00:00
-- url     : https://prove2.me/theorems/fa11440f-d784-4f87-9d97-097f65cbe269
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / SpectralTruncation / ProjectiveNonMeasurement
-- statement:
--   This bundle defines the spectral truncation and rounded projector family used to repair an almost-projective measurement. It handles the cutoff, continuity on outcome spectra, exact and large-error branches, and the unconditional witness-producing construction at the paper's source-defect scale.
--
--   Principal definitions:
--   - `truncationCutoff`: the spectral cutoff used in rounding.
--   - `truncationCutoff_le_inv_one_sub_mul`: the cutoff bound needed for error control.
--   - `continuousOn_outcome_spectrum`: continuity of the truncation map on the outcome spectrum.
--   - `roundedProjectorFamily`: the family of rounded projectors.
--   - `projectiveNonMeasurement_of_sourceAlmostProjective_two_mul`: constructs the projective-non-measurement witness from the source defect.
--   - `projectiveNonMeasurement_of_sourceAlmostProjective_zero`: handles the exact zero-defect endpoint.
--   - `projectiveNonMeasurement_of_sourceAlmostProjective_large`: handles the large-error branch.
--   - `projectiveNonMeasurement_of_sourceAlmostProjective_two_mul_full`: gives the unconditional constructive producer.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean#L31-L711

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Projective Non-Measurement from Spectral Truncation

This file proves the constructive spectral-truncation form of the paper witness
`lem:projective-non-measurement`.  The rounded projective family is obtained by
functional calculus, using the threshold `1 - sqrt ζ` in the nontrivial regime
and the zero family in the large-error regime.

## References

- `references/ldt-paper/orthonormalization.tex` (lines 420-550)
- Blueprint: Chapter 4 (`blueprint/src/chapter/ch04_projective.tex`)
- Related downstream applications: #422 (mainFormal), #834 (Step 6)
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

private noncomputable def truncationCutoff (δ : Error) : Error → Error :=
  fun x => if 1 - δ ≤ x then 1 else 0

private lemma truncationCutoff_le_inv_one_sub_mul
    (δ x : Error) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hx0 : 0 ≤ x) :
    truncationCutoff δ x ≤ (1 / (1 - δ)) * x := by
  by_cases h : 1 - δ ≤ x
  · have hden : 0 < 1 - δ := by linarith
    simp [truncationCutoff, h]
    have hdiv : 1 ≤ x / (1 - δ) := by
      rw [le_div_iff₀ hden]
      linarith
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  · have hden : 0 < 1 - δ := by linarith
    have hfac : 0 ≤ (1 - δ)⁻¹ := by positivity
    have hmul : 0 ≤ (1 - δ)⁻¹ * x := mul_nonneg hfac hx0
    simpa [truncationCutoff, h] using hmul

private lemma continuousOn_outcome_spectrum {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (a : Outcome) (f : Error → Error) :
    ContinuousOn f (spectrum ℝ (A.outcome a)) := by
  classical
  have hherm : (A.outcome a).IsHermitian := A.outcome_hermitian a
  have hs : (spectrum ℝ (A.outcome a)).Finite := by
    rw [hherm.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  exact hs.continuousOn _

private noncomputable def roundedProjectorFamily {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (δ : Error) : OpFamily Outcome ι where
  outcome := fun a => cfc (truncationCutoff δ) (A.outcome a)
  total := ∑ a, cfc (truncationCutoff δ) (A.outcome a)

private lemma outcome_spectrum_nonneg {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (a : Outcome) :
    ∀ x ∈ spectrum ℝ (A.outcome a), 0 ≤ x := by
  have hherm : (A.outcome a).IsHermitian := A.outcome_hermitian a
  have hsa : IsSelfAdjoint (A.outcome a) := hherm.isSelfAdjoint
  have hnonneg : 0 ≤ cfc (id : Error → Error) (A.outcome a) := by
    rw [cfc_id ℝ (A.outcome a) (ha := hsa)]
    exact A.outcome_pos a
  exact (cfc_nonneg_iff (R := ℝ) (f := id) (a := A.outcome a) (ha := hsa)).mp hnonneg

private lemma outcome_spectrum_le_one {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (a : Outcome) :
    ∀ x ∈ spectrum ℝ (A.outcome a), x ≤ 1 := by
  have hherm : (A.outcome a).IsHermitian := A.outcome_hermitian a
  have hsa : IsSelfAdjoint (A.outcome a) := hherm.isSelfAdjoint
  have hle : cfc (id : Error → Error) (A.outcome a) ≤ 1 := by
    rw [cfc_id ℝ (A.outcome a) (ha := hsa)]
    exact A.outcome_le_one a
  exact (cfc_le_one_iff (f := id) (a := A.outcome a) (ha := hsa)).mp hle

private lemma roundedProjectorFamily_projective {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (δ : Error) (a : Outcome) :
    MIPStarRE.Quantum.IsProj ((roundedProjectorFamily A δ).outcome a) := by
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change cfc (truncationCutoff δ) (A.outcome a) * cfc (truncationCutoff δ) (A.outcome a) =
      cfc (truncationCutoff δ) (A.outcome a)
    calc
      cfc (truncationCutoff δ) (A.outcome a) * cfc (truncationCutoff δ) (A.outcome a)
          = cfc (fun x => truncationCutoff δ x * truncationCutoff δ x) (A.outcome a) := by
              symm
              exact cfc_mul (R := ℝ) (truncationCutoff δ) (truncationCutoff δ) (A.outcome a)
                (hf := continuousOn_outcome_spectrum A a (truncationCutoff δ))
                (hg := continuousOn_outcome_spectrum A a (truncationCutoff δ))
      _ = cfc (truncationCutoff δ) (A.outcome a) := by
            apply cfc_congr
            intro x _hx
            by_cases h : 1 - δ ≤ x <;> simp [truncationCutoff, h]
  · exact cfc_predicate (R := ℝ) (truncationCutoff δ) (A.outcome a)

private lemma roundedProjectorFamily_outcome_le_scale {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (δ : Error) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (a : Outcome) :
    (roundedProjectorFamily A δ).outcome a ≤
      (((1 / (1 - δ)) : Error) : ℂ) • A.outcome a := by
  have hsa : IsSelfAdjoint (A.outcome a) :=
    (show (A.outcome a).IsHermitian from A.outcome_hermitian a).isSelfAdjoint
  have hmono :
      cfc (truncationCutoff δ) (A.outcome a) ≤
        cfc (fun x => (1 / (1 - δ)) * x) (A.outcome a) := by
    apply cfc_mono (R := ℝ) (a := A.outcome a)
      (hf := continuousOn_outcome_spectrum A a (truncationCutoff δ))
    intro x hx
    exact truncationCutoff_le_inv_one_sub_mul δ x hδ hδhalf
      (outcome_spectrum_nonneg A a x hx)
  calc
    (roundedProjectorFamily A δ).outcome a = cfc (truncationCutoff δ) (A.outcome a) := rfl
    _ ≤ cfc (fun x => (1 / (1 - δ)) * x) (A.outcome a) := hmono
    _ = (((1 / (1 - δ)) : Error) : ℂ) • A.outcome a := by
          simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
            (cfc_const_mul_id (R := ℝ) ((1 / (1 - δ)) : Error) (A.outcome a)
              (ha := hsa))

private lemma roundedProjectorFamily_total_le_scale {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (δ : Error) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (roundedProjectorFamily A δ).total ≤
      (((1 / (1 - δ)) : Error) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
  calc
    (roundedProjectorFamily A δ).total
      = ∑ a, (roundedProjectorFamily A δ).outcome a := by rfl
    _ ≤ ∑ a, (((1 / (1 - δ)) : Error) : ℂ) • A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact roundedProjectorFamily_outcome_le_scale A δ hδ hδhalf a
    _ = (((1 / (1 - δ)) : Error) : ℂ) • ∑ a, A.outcome a := by
          rw [Finset.smul_sum]
    _ = (((1 / (1 - δ)) : Error) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
          simp [A.sum_eq_total, A.total_eq_one]

private lemma roundedProjectorFamily_outcome_qSDD_bound {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (δ : Error)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (a : Outcome) :
    ev ψ (((A.outcome a - (roundedProjectorFamily A δ).outcome a)ᴴ) *
        (A.outcome a - (roundedProjectorFamily A δ).outcome a)) ≤
      (1 / δ) * ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
  have hsa : IsSelfAdjoint (A.outcome a) :=
    (show (A.outcome a).IsHermitian from A.outcome_hermitian a).isSelfAdjoint
  have hmono :
      cfc (fun x => (x - truncationCutoff δ x) ^ (2 : Nat)) (A.outcome a) ≤
        cfc (fun x : Error => (1 / δ) * (x - x ^ (2 : Nat))) (A.outcome a) := by
    apply cfc_mono (R := ℝ) (a := A.outcome a)
      (hf := continuousOn_outcome_spectrum A a (fun x => (x - truncationCutoff δ x) ^ (2 : Nat)))
      (hg := continuousOn_outcome_spectrum A a (fun x : Error => (1 / δ) * (x - x ^ (2 : Nat))))
    intro x hx
    simpa [truncationCutoff, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      truncationInequality δ x hδ hδhalf
        (outcome_spectrum_nonneg A a x hx)
        (outcome_spectrum_le_one A a x hx)
  have hleft :
      cfc (fun x => (x - truncationCutoff δ x) ^ (2 : Nat)) (A.outcome a) =
        (A.outcome a - (roundedProjectorFamily A δ).outcome a) *
          (A.outcome a - (roundedProjectorFamily A δ).outcome a) := by
    have hid : cfc (R := ℝ) (id : Error → Error) (A.outcome a) = A.outcome a := by
      change cfc (fun x : Error => x) (A.outcome a) = A.outcome a
      exact cfc_id' ℝ (A.outcome a) (ha := hsa)
    have hsub :
        cfc (fun x => x - truncationCutoff δ x) (A.outcome a) =
          A.outcome a - cfc (truncationCutoff δ) (A.outcome a) := by
      calc
        cfc (fun x => x - truncationCutoff δ x) (A.outcome a)
          = cfc (R := ℝ) (id : Error → Error) (A.outcome a) -
              cfc (truncationCutoff δ) (A.outcome a) := by
              simpa using
                (cfc_sub (R := ℝ) (f := id) (g := truncationCutoff δ) (a := A.outcome a)
                  (hf := continuousOn_outcome_spectrum A a id)
                  (hg := continuousOn_outcome_spectrum A a (truncationCutoff δ)))
        _ = A.outcome a - cfc (truncationCutoff δ) (A.outcome a) := by
              rw [hid]
    calc
      cfc (fun x => (x - truncationCutoff δ x) ^ (2 : Nat)) (A.outcome a)
        = cfc (fun x => x - truncationCutoff δ x) (A.outcome a) ^ 2 := by
            exact cfc_pow (R := ℝ) (fun x => x - truncationCutoff δ x) 2 (A.outcome a)
              (hf := continuousOn_outcome_spectrum A a (fun x => x - truncationCutoff δ x))
              (ha := hsa)
      _ = (A.outcome a - cfc (truncationCutoff δ) (A.outcome a)) ^ 2 := by
            rw [hsub]
      _ = (A.outcome a - (roundedProjectorFamily A δ).outcome a) *
            (A.outcome a - (roundedProjectorFamily A δ).outcome a) := by
            simp [roundedProjectorFamily, pow_two]
  have hright :
      cfc (fun x => (1 / δ) * (x - x ^ (2 : Nat))) (A.outcome a) =
        (((1 / δ) : Error) : ℂ) • (A.outcome a - A.outcome a * A.outcome a) := by
    have hid : cfc (R := ℝ) (id : Error → Error) (A.outcome a) = A.outcome a := by
      change cfc (fun x : Error => x) (A.outcome a) = A.outcome a
      exact cfc_id' ℝ (A.outcome a) (ha := hsa)
    have hsub :
        cfc (fun x : Error => x - x ^ (2 : Nat)) (A.outcome a) =
          A.outcome a - A.outcome a * A.outcome a := by
      calc
        cfc (fun x : Error => x - x ^ (2 : Nat)) (A.outcome a)
          = cfc (R := ℝ) (id : Error → Error) (A.outcome a) -
              cfc (fun x : Error => x ^ (2 : Nat)) (A.outcome a) := by
              simpa using
                (cfc_sub (R := ℝ) (f := id) (g := fun x : Error => x ^ (2 : Nat))
                  (a := A.outcome a)
                  (hf := continuousOn_outcome_spectrum A a id)
                  (hg := continuousOn_outcome_spectrum A a (fun x : Error => x ^ (2 : Nat))))
        _ = A.outcome a - cfc (fun x : Error => x ^ (2 : Nat)) (A.outcome a) := by
              rw [hid]
        _ = A.outcome a - A.outcome a * A.outcome a := by
              rw [cfc_pow_id (R := ℝ) (A.outcome a) 2 (ha := hsa)]
              simp [pow_two]
    calc
      cfc (fun x : Error => (1 / δ) * (x - x ^ (2 : Nat))) (A.outcome a)
        = (1 / δ : Error) • cfc (fun x : Error => x - x ^ (2 : Nat)) (A.outcome a) := by
            exact cfc_const_mul (R := ℝ) (1 / δ : Error) (fun x : Error => x - x ^ (2 : Nat))
              (A.outcome a)
              (hf := continuousOn_outcome_spectrum A a (fun x : Error => x - x ^ (2 : Nat)))
      _ = (((1 / δ) : Error) : ℂ) • (A.outcome a - A.outcome a * A.outcome a) := by
            rw [hsub]
            simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hdiff_herm :
      (A.outcome a - (roundedProjectorFamily A δ).outcome a).IsHermitian := by
    exact (show (A.outcome a).IsHermitian from A.outcome_hermitian a).sub
      (roundedProjectorFamily_projective A δ a).isSelfAdjoint.isHermitian
  have hmain :
      (A.outcome a - (roundedProjectorFamily A δ).outcome a) *
          (A.outcome a - (roundedProjectorFamily A δ).outcome a) ≤
        (((1 / δ) : Error) : ℂ) • (A.outcome a - A.outcome a * A.outcome a) := by
    rw [← hleft, ← hright]
    exact hmono
  calc
    ev ψ (((A.outcome a - (roundedProjectorFamily A δ).outcome a)ᴴ) *
        (A.outcome a - (roundedProjectorFamily A δ).outcome a))
      = ev ψ ((A.outcome a - (roundedProjectorFamily A δ).outcome a) *
          (A.outcome a - (roundedProjectorFamily A δ).outcome a)) := by
            simp [hdiff_herm.eq]
    _ ≤ ev ψ ((((1 / δ) : Error) : ℂ) • (A.outcome a - A.outcome a * A.outcome a)) :=
          ev_mono ψ _ _ hmain
    _ = (1 / δ) * ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
          simpa using ev_scale ψ (1 / δ) (A.outcome a - A.outcome a * A.outcome a)

private lemma roundedProjectorFamily_closeness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ δ : Error)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hsource : ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ) :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily (roundedProjectorFamily A δ))
      ((1 / δ) * ζ) := by
  constructor
  have hq :
      qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι)
          (roundedProjectorFamily A δ) ≤
        (1 / δ) * ζ := by
    unfold qSDDOp qSDDCore
    calc
      ∑ a : Outcome,
          ev ψ (((A.toSubMeas.outcome a - (roundedProjectorFamily A δ).outcome a)ᴴ) *
            (A.toSubMeas.outcome a - (roundedProjectorFamily A δ).outcome a))
        ≤ ∑ a : Outcome, (1 / δ) * ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
            refine Finset.sum_le_sum ?_
            intro a _
            simpa using roundedProjectorFamily_outcome_qSDD_bound ψ A δ hδ hδhalf a
      _ = (1 / δ) * ∑ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
            rw [← Finset.mul_sum]
      _ ≤ (1 / δ) * ζ := by
            have hδinv_nonneg : 0 ≤ 1 / δ := by positivity
            exact mul_le_mul_of_nonneg_left hsource hδinv_nonneg
  simpa [sddErrorOp, avgOver, uniformDistribution, constOpFamily] using hq

private lemma roundedProjectorFamily_total_le_one_zero {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) :
    (roundedProjectorFamily A 0).total ≤ (1 : MIPStarRE.Quantum.Op ι) := by
  have houtcome_le :
      ∀ a : Outcome, (roundedProjectorFamily A 0).outcome a ≤ A.outcome a := by
    intro a
    have hmono :
        cfc (truncationCutoff 0) (A.outcome a) ≤
          cfc (R := ℝ) (id : Error → Error) (A.outcome a) := by
      apply cfc_mono (R := ℝ) (a := A.outcome a)
        (f := truncationCutoff 0) (g := id)
        (hf := continuousOn_outcome_spectrum A a (truncationCutoff 0))
        (hg := continuousOn_outcome_spectrum A a id)
      intro x hx
      have hx0 := outcome_spectrum_nonneg A a x hx
      have hx1 := outcome_spectrum_le_one A a x hx
      by_cases h : 1 ≤ x
      · have hx_eq : x = 1 := le_antisymm hx1 h
        simp [truncationCutoff, hx_eq]
      · simp [truncationCutoff, h, hx0]
    calc
      (roundedProjectorFamily A 0).outcome a = cfc (truncationCutoff 0) (A.outcome a) := rfl
      _ ≤ cfc (R := ℝ) (id : Error → Error) (A.outcome a) := hmono
      _ = A.outcome a := cfc_id' ℝ (A.outcome a)
        (ha := (show IsSelfAdjoint (A.outcome a) from
          (show (A.outcome a).IsHermitian from A.outcome_hermitian a).isSelfAdjoint))
  calc
    (roundedProjectorFamily A 0).total = ∑ a, (roundedProjectorFamily A 0).outcome a := by rfl
    _ ≤ ∑ a, A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact houtcome_le a
    _ = 1 := by simpa [A.sum_eq_total] using A.total_eq_one

private lemma sourceAlmostProjective_eq_zero_per_outcome {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (hsource : ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 0) :
    ∀ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a) = 0 := by
  classical
  have hsum_nonneg :
      0 ≤ ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) :=
    sourceAlmostProjective_nonneg ψ A
  have hsum_zero :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) = 0 :=
    le_antisymm hsource hsum_nonneg
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
      ev_nonneg_of_psd ψ _ <|
        sub_nonneg.mpr <|
          MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)).mp hsum_zero
  intro a
  exact hterms a (by simp)

/-- Construct the paper witness `lem:projective-non-measurement` from the
source almost-projective defect at the paper's `2ζ` scale.

This is the spectral-truncation stage of Section 5 in the form needed by the
top-level orthonormalization theorem: the input defect is bounded by `2 * ζ`,
and choosing the truncation threshold `1 - sqrt ζ` gives the paper's
`2 * sqrt ζ` closeness bound together with the total bound
`(1 + 2 * sqrt ζ) * I`. -/
theorem projectiveNonMeasurement_of_sourceAlmostProjective_two_mul
    {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 < ζ) (hζ_small : ζ ≤ 1 / 4)
    (hsource : ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    projectiveNonMeasurement ψ A ζ := by
  classical
  let ε : Error := spectralTruncationError ζ
  have hζ_nonneg : 0 ≤ ζ := le_of_lt hζ
  have hε_pos : 0 < ε := by
    dsimp [ε]
    rw [spectralTruncationError_eq_sqrt]
    exact Real.sqrt_pos.mpr hζ
  have hε_half : ε ≤ 1 / 2 := by
    dsimp [ε]
    rw [spectralTruncationError_eq_sqrt]
    have hs : Real.sqrt ζ ≤ Real.sqrt (1 / 4 : Error) := Real.sqrt_le_sqrt hζ_small
    norm_num at hs ⊢
    exact hs
  have hε_sq : ε * ε = ζ := by
    dsimp [ε]
    simpa [spectralTruncationError_eq_sqrt, pow_two] using Real.sq_sqrt hζ_nonneg
  have hclose_scale : (1 / ε) * (2 * ζ) ≤ 2 * spectralTruncationError ζ := by
    have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
    have hε_eq : (1 / ε) * (2 * ζ) = 2 * ε := by
      field_simp [hε_ne]
      linarith [hε_sq]
    have hEq : (1 / ε) * (2 * ζ) = 2 * spectralTruncationError ζ := by
      calc
        (1 / ε) * (2 * ζ) = 2 * ε := hε_eq
        _ = 2 * spectralTruncationError ζ := by simp [ε]
    exact hEq.le
  have htotal_scale : 1 / (1 - ε) ≤ 1 + 2 * spectralTruncationError ζ := by
    have hden_pos : 0 < 1 - ε := by linarith
    have hcore : 1 / (1 - ε) ≤ 1 + 2 * ε := by
      rw [div_le_iff₀ hden_pos]
      nlinarith [hε_half]
    simpa [ε] using hcore
  refine ⟨roundedProjectorFamily A ε, ?_⟩
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro a
    exact roundedProjectorFamily_projective A ε a
  · exact MIPStarRE.LDT.Preliminaries.sddOpRel_mono ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily (roundedProjectorFamily A ε))
      ((1 / ε) * (2 * ζ)) (2 * spectralTruncationError ζ)
      (roundedProjectorFamily_closeness ψ A (2 * ζ) ε hε_pos hε_half hsource)
      hclose_scale
  · have hbase := roundedProjectorFamily_total_le_scale A ε hε_pos hε_half
    have hcoeff_nonneg : 0 ≤ (1 + 2 * ε - 1 / (1 - ε) : Error) := by
      linarith [htotal_scale]
    have hsmul_real :
        ((1 / (1 - ε) : Error) • (1 : MIPStarRE.Quantum.Op ι)) ≤
          ((1 + 2 * ε : Error) • (1 : MIPStarRE.Quantum.Op ι)) := by
      apply sub_nonneg.mp
      rw [← sub_smul]
      change 0 ≤ (((1 + 2 * ε) - (1 / (1 - ε)) : Error) • (1 : MIPStarRE.Quantum.Op ι))
      exact smul_nonneg hcoeff_nonneg
        (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))
    have hsmul :
        (((1 / (1 - ε)) : Error) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) ≤
          (((1 + 2 * ε : Error)) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
      simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hsmul_real
    exact le_trans hbase <| by simpa [ε] using hsmul

/-- The exact endpoint `ζ = 0` of `lem:projective-non-measurement`.

Here the source almost-projective defect vanishes exactly. We round each effect
to the spectral projector onto its `1`-eigenspace. The total operator is then
dominated by `I`, and the finite-spectrum comparison shows that the resulting
state-dependent operator distance is exactly zero. -/
theorem projectiveNonMeasurement_of_sourceAlmostProjective_zero
    {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (hsource : ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 0) :
    projectiveNonMeasurement ψ A 0 := by
  classical
  refine ⟨roundedProjectorFamily A 0, ?_⟩
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro a
    exact roundedProjectorFamily_projective A 0 a
  · constructor
    have hq :
        qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι) (roundedProjectorFamily A 0) ≤ 0 := by
      have hzero_terms := sourceAlmostProjective_eq_zero_per_outcome ψ A hsource
      unfold qSDDOp qSDDCore
      have hterm_le :
          ∀ a : Outcome,
            ev ψ (((A.toSubMeas.outcome a - (roundedProjectorFamily A 0).outcome a)ᴴ) *
              (A.toSubMeas.outcome a - (roundedProjectorFamily A 0).outcome a)) ≤ 0 := by
        intro a
        have hherm : (A.outcome a).IsHermitian := A.outcome_hermitian a
        let defect : Error → Error := fun x => x - x ^ (2 : Nat)
        let gap : Error → Error := fun x => (x - truncationCutoff 0 x) ^ (2 : Nat)
        let ratio : ι → Error := fun i =>
          if hfi : hherm.eigenvalues i - hherm.eigenvalues i ^ (2 : Nat) = 0 then 0
          else (hherm.eigenvalues i - truncationCutoff 0 (hherm.eigenvalues i)) ^ (2 : Nat) /
            (hherm.eigenvalues i - hherm.eigenvalues i ^ (2 : Nat))
        let K : Error := ∑ i : ι, ratio i
        have hratio_nonneg : ∀ i : ι, 0 ≤ ratio i := by
          intro i
          dsimp [ratio]
          by_cases hfi : hherm.eigenvalues i - hherm.eigenvalues i ^ (2 : Nat) = 0
          · simpa only [hfi, if_pos] using (show (0 : Error) ≤ 0 by positivity)
          · have hx0 : 0 ≤ hherm.eigenvalues i :=
              outcome_spectrum_nonneg A a (hherm.eigenvalues i)
                (hherm.eigenvalues_mem_spectrum_real i)
            have hx1 : hherm.eigenvalues i ≤ 1 :=
              outcome_spectrum_le_one A a (hherm.eigenvalues i)
                (hherm.eigenvalues_mem_spectrum_real i)
            have hdef_nonneg : 0 ≤ defect (hherm.eigenvalues i) := by
              dsimp [defect]
              nlinarith [hx0, hx1]
            have hgap_nonneg :
                0 ≤
                  (hherm.eigenvalues i - truncationCutoff 0 (hherm.eigenvalues i)) ^
                    (2 : Nat) := by
              exact sq_nonneg _
            simpa [hfi, defect] using div_nonneg hgap_nonneg hdef_nonneg
        have hgap_le :
            ∀ x ∈ spectrum ℝ (A.outcome a), gap x ≤ K * defect x := by
          intro x hx
          rw [hherm.spectrum_real_eq_range_eigenvalues] at hx
          rcases hx with ⟨i, rfl⟩
          have hx0 : 0 ≤ hherm.eigenvalues i :=
            outcome_spectrum_nonneg A a (hherm.eigenvalues i)
              (hherm.eigenvalues_mem_spectrum_real i)
          have hx1 : hherm.eigenvalues i ≤ 1 :=
            outcome_spectrum_le_one A a (hherm.eigenvalues i)
              (hherm.eigenvalues_mem_spectrum_real i)
          have hratio_le : ratio i ≤ K := by
            dsimp [K]
            simpa using
              Finset.single_le_sum (fun j _ => hratio_nonneg j)
                (by simp : i ∈ Finset.univ)
          dsimp [ratio, defect, gap]
          by_cases hfi : hherm.eigenvalues i - hherm.eigenvalues i ^ (2 : Nat) = 0
          · have hmul : hherm.eigenvalues i * (1 - hherm.eigenvalues i) = 0 := by
              nlinarith [hfi]
            rcases mul_eq_zero.mp hmul with hzero | hone
            · have : hherm.eigenvalues i = 0 := hzero
              norm_num [truncationCutoff, this]
            · have : hherm.eigenvalues i = 1 := by linarith
              norm_num [truncationCutoff, this]
          · have hdef_nonneg : 0 ≤ hherm.eigenvalues i - hherm.eigenvalues i ^ (2 : Nat) := by
              nlinarith [hx0, hx1]
            have hratio_eq :
                (hherm.eigenvalues i - truncationCutoff 0 (hherm.eigenvalues i)) ^ (2 : Nat) =
                  ratio i * (hherm.eigenvalues i - hherm.eigenvalues i ^ (2 : Nat)) := by
              have hdef_ne : hherm.eigenvalues i - hherm.eigenvalues i ^ (2 : Nat) ≠ 0 := by
                simpa using hfi
              dsimp [ratio]
              rw [if_neg hfi]
              exact (div_mul_cancel₀ _ hdef_ne).symm
            calc
              (hherm.eigenvalues i - truncationCutoff 0 (hherm.eigenvalues i)) ^ (2 : Nat)
                = ratio i * (hherm.eigenvalues i - hherm.eigenvalues i ^ (2 : Nat)) := hratio_eq
              _ ≤ K * (hherm.eigenvalues i - hherm.eigenvalues i ^ (2 : Nat)) := by
                    gcongr
        have hmono :
            cfc gap (A.outcome a) ≤ cfc (fun x : Error => K * defect x) (A.outcome a) := by
          apply cfc_mono (R := ℝ) (a := A.outcome a)
            (hf := continuousOn_outcome_spectrum A a gap)
            (hg := continuousOn_outcome_spectrum A a (fun x : Error => K * defect x))
          exact hgap_le
        have hsa : IsSelfAdjoint (A.outcome a) := hherm.isSelfAdjoint
        have hleft :
            cfc gap (A.outcome a) =
              (A.outcome a - (roundedProjectorFamily A 0).outcome a) *
                (A.outcome a - (roundedProjectorFamily A 0).outcome a) := by
          have hid : cfc (R := ℝ) (id : Error → Error) (A.outcome a) = A.outcome a := by
            change cfc (fun x : Error => x) (A.outcome a) = A.outcome a
            exact cfc_id' ℝ (A.outcome a) (ha := hsa)
          have hsub :
              cfc (fun x : Error => x - truncationCutoff 0 x) (A.outcome a) =
                A.outcome a - cfc (truncationCutoff 0) (A.outcome a) := by
            calc
              cfc (fun x : Error => x - truncationCutoff 0 x) (A.outcome a)
                = cfc (R := ℝ) (id : Error → Error) (A.outcome a) -
                    cfc (truncationCutoff 0) (A.outcome a) := by
                    simpa using
                      (cfc_sub (R := ℝ) (f := id) (g := truncationCutoff 0) (a := A.outcome a)
                        (hf := continuousOn_outcome_spectrum A a id)
                        (hg := continuousOn_outcome_spectrum A a (truncationCutoff 0)))
              _ = A.outcome a - cfc (truncationCutoff 0) (A.outcome a) := by
                    rw [hid]
          calc
            cfc gap (A.outcome a)
              = cfc (fun x : Error => x - truncationCutoff 0 x) (A.outcome a) ^ 2 := by
                  exact cfc_pow (R := ℝ)
                    (fun x : Error => x - truncationCutoff 0 x) 2 (A.outcome a)
                    (hf := continuousOn_outcome_spectrum A a
                      (fun x : Error => x - truncationCutoff 0 x))
                    (ha := hsa)
            _ = (A.outcome a - cfc (truncationCutoff 0) (A.outcome a)) ^ 2 := by rw [hsub]
            _ = (A.outcome a - (roundedProjectorFamily A 0).outcome a) *
                  (A.outcome a - (roundedProjectorFamily A 0).outcome a) := by
                  simp [roundedProjectorFamily, pow_two]
        have hright :
            cfc (fun x : Error => K * defect x) (A.outcome a) =
              (K : Error) • (A.outcome a - A.outcome a * A.outcome a) := by
          have hid : cfc (R := ℝ) (id : Error → Error) (A.outcome a) = A.outcome a := by
            change cfc (fun x : Error => x) (A.outcome a) = A.outcome a
            exact cfc_id' ℝ (A.outcome a) (ha := hsa)
          have hsub :
              cfc defect (A.outcome a) = A.outcome a - A.outcome a * A.outcome a := by
            calc
              cfc defect (A.outcome a)
                = cfc (R := ℝ) (id : Error → Error) (A.outcome a) -
                    cfc (fun x : Error => x ^ (2 : Nat)) (A.outcome a) := by
                    simpa using
                      (cfc_sub (R := ℝ) (f := id)
                        (g := fun x : Error => x ^ (2 : Nat)) (a := A.outcome a)
                        (hf := continuousOn_outcome_spectrum A a id)
                        (hg := continuousOn_outcome_spectrum A a (fun x : Error => x ^ (2 : Nat))))
              _ = A.outcome a - cfc (fun x : Error => x ^ (2 : Nat)) (A.outcome a) := by
                    rw [hid]
              _ = A.outcome a - A.outcome a * A.outcome a := by
                    rw [cfc_pow_id (R := ℝ) (A.outcome a) 2 (ha := hsa)]
                    simp [pow_two]
          calc
            cfc (fun x : Error => K * defect x) (A.outcome a)
              = (K : Error) • cfc defect (A.outcome a) := by
                  exact cfc_const_mul (R := ℝ) K defect (A.outcome a)
                    (hf := continuousOn_outcome_spectrum A a defect)
            _ = (K : Error) • (A.outcome a - A.outcome a * A.outcome a) := by rw [hsub]
        have hdiff_herm :
            (A.outcome a - (roundedProjectorFamily A 0).outcome a).IsHermitian := by
          exact (show (A.outcome a).IsHermitian from A.outcome_hermitian a).sub
            (roundedProjectorFamily_projective A 0 a).isSelfAdjoint.isHermitian
        have hmain :
            (A.outcome a - (roundedProjectorFamily A 0).outcome a) *
                (A.outcome a - (roundedProjectorFamily A 0).outcome a) ≤
              (K : Error) • (A.outcome a - A.outcome a * A.outcome a) := by
          rw [← hleft, ← hright]
          exact hmono
        calc
          ev ψ (((A.outcome a - (roundedProjectorFamily A 0).outcome a)ᴴ) *
              (A.outcome a - (roundedProjectorFamily A 0).outcome a))
            = ev ψ ((A.outcome a - (roundedProjectorFamily A 0).outcome a) *
                (A.outcome a - (roundedProjectorFamily A 0).outcome a)) := by
                simp [hdiff_herm.eq]
          _ ≤ ev ψ ((K : Error) • (A.outcome a - A.outcome a * A.outcome a)) :=
              ev_mono ψ _ _ hmain
          _ = K * ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
              simpa using ev_real_smul ψ K (A.outcome a - A.outcome a * A.outcome a)
          _ = 0 := by rw [hzero_terms a, mul_zero]
      have hsum_le :
          ∑ a : Outcome,
              ev ψ (((A.toSubMeas.outcome a - (roundedProjectorFamily A 0).outcome a)ᴴ) *
                (A.toSubMeas.outcome a - (roundedProjectorFamily A 0).outcome a)) ≤
            ∑ a : Outcome, 0 := by
        refine Finset.sum_le_sum ?_
        intro a _
        exact hterm_le a
      have hsum_zero :
          ∑ a : Outcome,
              ev ψ (((A.toSubMeas.outcome a - (roundedProjectorFamily A 0).outcome a)ᴴ) *
                (A.toSubMeas.outcome a - (roundedProjectorFamily A 0).outcome a)) ≤ 0 := by
        simpa using hsum_le
      exact hsum_zero
    simpa [sddErrorOp, avgOver, uniformDistribution, constOpFamily,
      spectralTruncationError_eq_sqrt, Real.sqrt_zero] using hq
  · have htotal :
        (roundedProjectorFamily A 0).total ≤ (1 : MIPStarRE.Quantum.Op ι) :=
      roundedProjectorFamily_total_le_one_zero A
    simpa [spectralTruncationError_eq_sqrt, Real.sqrt_zero, roundedProjectorFamily] using htotal

/-- The large-error branch of `lem:projective-non-measurement`.

The paper treats the surrounding orthonormalization lemma as trivial when
`ζ > 1/4`. On a normalized state, the zero projector family already satisfies
the required `2\sqrt{ζ}` state-dependent operator bound in this regime. -/
theorem projectiveNonMeasurement_of_sourceAlmostProjective_large
    {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized) (hlarge : 1 / 4 < ζ) :
    projectiveNonMeasurement ψ A ζ := by
  classical
  let Z : OpFamily Outcome ι := (zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas
  refine ⟨Z, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simp [Z, zeroProjSubMeas, SubMeas.toOpFamily]
  · constructor
    have hq1 :
        qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι)
            Z ≤ 1 := by
      unfold qSDDOp qSDDCore Z
      calc
        ∑ a : Outcome,
            ev ψ (((A.toSubMeas.outcome a - 0)ᴴ) * (A.toSubMeas.outcome a - 0))
          = ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simp [A.outcome_hermitian a]
        _ ≤ 1 := by
              simpa using Preliminaries.subMeas_diagMass_le_one ψ hψ A.toSubMeas
    have hbound : 1 ≤ 2 * spectralTruncationError ζ := by
      rw [spectralTruncationError_eq_sqrt]
      have hsqrt : 1 / 2 < Real.sqrt ζ := by
        have : Real.sqrt (1 / 4 : Error) < Real.sqrt ζ :=
          Real.sqrt_lt_sqrt (by positivity : 0 ≤ (1 / 4 : Error)) hlarge
        norm_num at this ⊢
        exact this
      nlinarith
    have hq :
        qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι)
            Z ≤
          2 * spectralTruncationError ζ :=
      le_trans hq1 hbound
    simpa [sddErrorOp, avgOver, uniformDistribution, constOpFamily, Z] using hq
  · simpa [Z, SubMeas.toOpFamily] using
      (zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.sum_eq_total
  · have hζ_nonneg : 0 ≤ ζ := le_trans (by positivity : 0 ≤ (1 / 4 : Error)) hlarge.le
    have hcoeff_nonneg : 0 ≤ (1 + 2 * spectralTruncationError ζ : Error) := by
      have hs_nonneg : 0 ≤ spectralTruncationError ζ := spectralTruncationError_nonneg hζ_nonneg
      positivity
    have hZtotal : Z.total = 0 := by
      simp [Z, zeroProjSubMeas, SubMeas.toOpFamily]
    rw [hZtotal]
    simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      (smul_nonneg hcoeff_nonneg
        (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι)))

/-- Unconditional constructive producer for `lem:projective-non-measurement`
from the paper's `2ζ` source-defect bound.

This theorem combines the exact endpoint `ζ = 0`, the nontrivial spectral proof
for `0 < ζ ≤ 1/4`, and the trivial large-error branch used in the surrounding
paper argument. -/
theorem projectiveNonMeasurement_of_sourceAlmostProjective_two_mul_full
    {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hsource : ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    projectiveNonMeasurement ψ A ζ := by
  classical
  by_cases hzero : ζ = 0
  · have hsource0 : ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 0 := by
      simpa [hzero] using hsource
    simpa [hzero] using projectiveNonMeasurement_of_sourceAlmostProjective_zero ψ A hsource0
  · by_cases hsmall : ζ ≤ 1 / 4
    · have hζ_nonneg : 0 ≤ ζ := by
        have hsource_nonneg : 0 ≤ ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) :=
          sourceAlmostProjective_nonneg ψ A
        nlinarith
      have hζ_pos : 0 < ζ := lt_of_le_of_ne hζ_nonneg (Ne.symm hzero)
      exact projectiveNonMeasurement_of_sourceAlmostProjective_two_mul
        ψ A ζ hζ_pos hsmall hsource
    · exact projectiveNonMeasurement_of_sourceAlmostProjective_large ψ A ζ hψ
        (lt_of_not_ge hsmall)





end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


