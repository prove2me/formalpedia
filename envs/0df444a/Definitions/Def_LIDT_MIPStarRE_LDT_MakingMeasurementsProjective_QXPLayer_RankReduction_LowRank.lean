-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:03:56.981192+00:00
-- url     : https://prove2.me/theorems/18716569-94ed-455d-b8dc-0529d879a3c1
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / QXPLayer / RankReduction / LowRank
-- statement:
--   This bundle implements the low-rank branch of the QXP projectivization construction. It chooses an auxiliary space from a total-rank bound, truncates rounded projectors spectrally when necessary, and identifies the discarded overlap with the state-dependent truncation distance.
--
--   Principal definitions:
--   - `projectiveLowRankSum_auxData_of_rank_bound`: Constructs auxiliary dimension and projective-measurement data from a rank bound.
--   - `projectiveLowRankSum_of_rank_bound`: Produces the low-rank projective family when the rounded family already fits the dimension bound.
--   - `projectiveLowRankSum_truncationOverlap_eq_ev_sum`: Expresses retained spectral overlap as an expectation sum.
--   - `projectiveLowRankSum_qSDD_truncation_eq_compl_overlap`: Identifies truncation qSDD with the discarded complementary overlap.
--   - `projectiveLowRankSum_truncate`: Spectrally truncates the rounded family in the rank-exceeds-dimension branch.
--   - `projectiveLowRankSum_of_roundingWitness`: Builds the low-rank family from a rounded projective family and its witness.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/LowRank.lean#L24-L502

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/LowRank.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Q/X/XHat/P low-rank truncation

Rank-reduction auxiliary-space constructions and the low-rank truncation branch for
the paper's `Q/X/XHat/P` intermediate layer.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

universe uOutcome uι

/-- Concrete auxiliary-space construction from a direct total-rank bound. -/
lemma projectiveLowRankSum_auxData_of_rank_bound {Outcome : Type uOutcome}
    [Fintype Outcome] [Nonempty Outcome]
    {ι : Type uι} [Fintype ι] [Nonempty ι]
    (m : Outcome → ℕ)
    (hm : ∑ a, m a ≤ Fintype.card ι) :
    ∃ auxSpace : FiniteHilbertSpace.{uι}, ∃ t : ProjMeas Outcome auxSpace.carrier,
      t.total = 1 ∧ Fintype.card auxSpace.carrier ≤ Fintype.card ι := by
  classical
  by_cases hsigma : Nonempty (FiniteHilbertSpace.sigmaFinCarrier m)
  · let := hsigma
    let auxSpace : FiniteHilbertSpace.{uι} := FiniteHilbertSpace.sigmaFin m
    refine ⟨auxSpace, sigmaFinProjMeas m, ?_⟩
    refine ⟨rfl, ?_⟩
    have hcard :
        Fintype.card (FiniteHilbertSpace.sigmaFinCarrier m) ≤ Fintype.card ι :=
      sigmaFinCard_le_of_sum_le (ι := ι) m hm
    change Fintype.card (ULift (FiniteHilbertSpace.sigmaFinCarrier m)) ≤ Fintype.card ι
    rw [Fintype.card_ulift]
    exact hcard
  · let a0 : Outcome := Classical.choice (inferInstance : Nonempty Outcome)
    let auxSpace : FiniteHilbertSpace.{uι} :=
      { carrier := ULift.{uι} Unit
        instFintype := inferInstance
        instDecidableEq := inferInstance
        instNonempty := inferInstance }
    refine ⟨auxSpace, pointProjMeas a0, ?_⟩
    refine ⟨rfl, ?_⟩
    have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    simpa [auxSpace] using Nat.succ_le_of_lt hcard_pos





/-- Concrete rank-reduction construction once the rounded projectors already have
total rank at most the ambient dimension. This is the `r ≤ d` branch of the
paper's rank-reduction proof, and is also the final packaging step after the
`r > d` truncation branch constructs its lower-rank family. -/
lemma projectiveLowRankSum_of_rank_bound {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome] [Nonempty Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ)
    (R : OpFamily Outcome ι)
    (hR : RoundingToProjectorsWitness ψ A ζ R)
    (hrank : ∑ a, (R.outcome a).rank ≤ Fintype.card ι)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  obtain ⟨auxSpace, t, _, hAuxDim⟩ :=
    projectiveLowRankSum_auxData_of_rank_bound
      (m := fun a : Outcome => (R.outcome a).rank) hrank
  let data : QLayerData Outcome ι :=
    { auxSpace := auxSpace
      q := R
      t := t }
  refine ⟨data, ?_⟩
  refine ⟨?_, ?_, ?_, source_almost_projective, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hR.projective a
  · intro a
    have hproj := hR.projective a
    change 0 ≤ R.outcome a
    exact hproj.nonneg
  · simpa [Qa, QTotal, data] using hR.sum_eq_total
  · exact MIPStarRE.LDT.Preliminaries.sddOpRel_mono ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily R)
      (2 * spectralTruncationError ζ) (roundingToProjectiveError ζ)
      hR.closeness
      (by
        have hε_nonneg : 0 ≤ spectralTruncationError ζ := spectralTruncationError_nonneg hζ
        dsimp [roundingToProjectiveError]
        exact mul_le_mul_of_nonneg_right (by norm_num : (2 : Error) ≤ 12) hε_nonneg)
  · calc
      QTotal data = R.total := rfl
      _ ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
          (1 : MIPStarRE.Quantum.Op ι) := hR.total_le
  · simpa [Qa, data] using hrank
  · simpa [data] using hAuxDim

/-- Sum the rank-one spectral overlaps of all rounded projectors back into
`ev ψ (∑_a R_a)`.  This isolates the dependent-sigma rewrite used in the
`r > d` truncation branch of `projectiveLowRankSum`. -/
private lemma projectiveLowRankSum_truncationOverlap_eq_ev_sum {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (R : OpFamily Outcome ι)
    (hproj : ∀ a, MIPStarRE.Quantum.IsProj (R.outcome a))
    (onb : (a : Outcome) →
      MIPStarRE.Quantum.ProjectorRangeONB (R.outcome a) (hproj a)) :
    (∑ x : (Σ a : Outcome, Fin (R.outcome a).rank),
        ev ψ ((onb x.1).rankOne x.2)) =
      ev ψ (∑ a, R.outcome a) := by
  classical
  calc
    (∑ x : (Σ a : Outcome, Fin (R.outcome a).rank),
        ev ψ ((onb x.1).rankOne x.2))
        = ∑ a : Outcome, ∑ i : Fin (R.outcome a).rank,
            ev ψ ((onb a).rankOne i) := by
          rw [Fintype.sum_sigma]
    _ = ∑ a : Outcome, ev ψ (R.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← ev_sum ψ (fun i : Fin (R.outcome a).rank => (onb a).rankOne i)]
          simpa [MIPStarRE.Quantum.ProjectorRangeONB.rankOne] using
            congrArg (ev ψ) (onb a).decomposition.symm
    _ = ev ψ (∑ a, R.outcome a) := by
          rw [ev_sum]

/-- The squared-distance defect between the rounded family `R` and its truncated
subprojector family is exactly the discarded rank-one overlap mass. -/
private lemma projectiveLowRankSum_qSDD_truncation_eq_compl_overlap
    {Outcome : Type uOutcome} {ι : Type uι}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι)
    (R : OpFamily Outcome ι)
    (hproj : ∀ a, MIPStarRE.Quantum.IsProj (R.outcome a))
    [DecidableEq (Σ a : Outcome, Fin (R.outcome a).rank)]
    (onb : (a : Outcome) →
      MIPStarRE.Quantum.ProjectorRangeONB (R.outcome a) (hproj a))
    (Large : Finset (Σ a : Outcome, Fin (R.outcome a).rank))
    (fiber : (a : Outcome) → Finset (Fin (R.outcome a).rank))
    (hLarge_compl_sigma :
      (Largeᶜ : Finset (Σ a : Outcome, Fin (R.outcome a).rank)) =
        (Finset.univ : Finset Outcome).sigma (fun a => (fiber a)ᶜ)) :
    qSDDOp ψ R
      ({ outcome := fun a => (onb a).subprojector (fiber a)
         total := ∑ a, (onb a).subprojector (fiber a) } : OpFamily Outcome ι) =
      ∑ x ∈ (Largeᶜ : Finset (Σ a : Outcome, Fin (R.outcome a).rank)),
        ev ψ ((onb x.1).rankOne x.2) := by
  classical
  unfold qSDDOp qSDDCore
  calc
    ∑ a : Outcome,
        ev ψ (((R.outcome a - (onb a).subprojector (fiber a))ᴴ) *
          (R.outcome a - (onb a).subprojector (fiber a)))
        = ∑ a : Outcome,
            ev ψ ((onb a).subprojector
              ((fiber a)ᶜ : Finset (Fin (R.outcome a).rank))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hdiff := (onb a).subprojector_diff_eq_compl (fiber a)
          have hproj_sub := (onb a).subprojector_isProj
            ((fiber a)ᶜ : Finset (Fin (R.outcome a).rank))
          rw [show R.outcome a - (onb a).subprojector (fiber a) =
              (onb a).subprojector ((fiber a)ᶜ : Finset (Fin (R.outcome a).rank)) by
                simpa using hdiff]
          simp [hproj_sub.isSelfAdjoint.isHermitian.eq, hproj_sub.isIdempotentElem.eq]
    _ = ∑ a : Outcome, ∑ i ∈ ((fiber a)ᶜ : Finset (Fin (R.outcome a).rank)),
          ev ψ ((onb a).rankOne i) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          change ev ψ (∑ i ∈ ((fiber a)ᶜ : Finset (Fin (R.outcome a).rank)),
              (onb a).rankOne i) =
            ∑ i ∈ ((fiber a)ᶜ : Finset (Fin (R.outcome a).rank)),
              ev ψ ((onb a).rankOne i)
          rw [ev_finset_sum]
    _ = ∑ x ∈ (Largeᶜ : Finset (Σ a : Outcome, Fin (R.outcome a).rank)),
          ev ψ ((onb x.1).rankOne x.2) := by
          rw [hLarge_compl_sigma]
          rw [Finset.sum_sigma]

/-- Construct the rank-reduced projector family in the `r > d` truncation
branch, starting from the rounded projectors `R_a`. -/
lemma projectiveLowRankSum_truncate {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome] [Nonempty Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1 / 4)
    (R : OpFamily Outcome ι)
    (hR : RoundingToProjectorsWitness ψ A ζ R)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  classical
  let d : ℕ := Fintype.card ι
  let Idx : Type uOutcome := Σ a : Outcome, Fin (R.outcome a).rank
  let : Fintype Idx := inferInstance
  let : DecidableEq Idx := Classical.decEq Idx
  by_cases hr : Fintype.card Idx ≤ d
  · have hrank : ∑ a, (R.outcome a).rank ≤ Fintype.card ι := by
      simpa [Idx, d, Fintype.card_sigma] using hr
    exact projectiveLowRankSum_of_rank_bound ψ A ζ hζ R hR hrank source_almost_projective
  · have hcard_gt : d < Fintype.card Idx := Nat.lt_of_not_ge hr
    let onb : (a : Outcome) →
        MIPStarRE.Quantum.ProjectorRangeONB (R.outcome a) (hR.projective a) :=
      fun a => MIPStarRE.Quantum.IsProj.rangeONB (R.outcome a) (hR.projective a)
    let rankOne : Idx → MIPStarRE.Quantum.Op ι := fun x => (onb x.1).rankOne x.2
    let overlap : Idx → Error := fun x => ev ψ (rankOne x)
    have hd_le : d ≤ Fintype.card Idx := le_of_lt hcard_gt
    obtain ⟨Large, hLarge_card, hLarge_order⟩ :=
      Truncation.exists_large_subset_ordered (α := Idx) overlap hd_le
    let fiber : (a : Outcome) → Finset (Fin (R.outcome a).rank) := fun a =>
      (Finset.univ : Finset (Fin (R.outcome a).rank)).filter
        (fun i => (⟨a, i⟩ : Idx) ∈ Large)
    let Q : OpFamily Outcome ι :=
      { outcome := fun a => (onb a).subprojector (fiber a)
        total := ∑ a, (onb a).subprojector (fiber a) }
    have hRsum_le : (∑ a, R.outcome a) ≤
        (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
          (1 : MIPStarRE.Quantum.Op ι) := by
      simpa [hR.sum_eq_total] using hR.total_le
    have hspectral_sqrt : spectralTruncationError ζ = Real.sqrt ζ :=
      spectralTruncationError_eq_sqrt ζ
    have hr_bound : (Fintype.card Idx : Error) ≤ (1 + 2 * Real.sqrt ζ) * d := by
      have hcard_idx : Fintype.card Idx = ∑ a, (R.outcome a).rank := by
        simp [Idx, Fintype.card_sigma]
      have hRsum_le_for_rank : (∑ a, R.outcome a) ≤
          ((((1 : Error) + 2 * spectralTruncationError ζ : Error) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι)) := by
        simpa using hRsum_le
      have hrank_bound :=
        sum_rank_le_scalar_mul_card_of_projectors_le (R := R.outcome)
          (hproj := hR.projective)
          (c := 1 + 2 * spectralTruncationError ζ) hRsum_le_for_rank
      rw [show (Fintype.card Idx : Error) = ((∑ a, (R.outcome a).rank : ℕ) : Error) by
        exact_mod_cast hcard_idx]
      simpa [d, hspectral_sqrt] using hrank_bound
    have hLarge_sigma :
        Large = (Finset.univ : Finset Outcome).sigma (fun a => fiber a) := by
      ext x
      rcases x with ⟨a, i⟩
      constructor
      · intro h
        exact Finset.mem_sigma.mpr ⟨Finset.mem_univ a, by simp [fiber, h]⟩
      · intro h
        rcases Finset.mem_sigma.mp h with ⟨_, hi⟩
        simpa [fiber] using hi
    have hLarge_card_sum : Large.card = ∑ a, (fiber a).card := by
      rw [hLarge_sigma]
      change (Multiset.card (Multiset.sigma Finset.univ.val fun a => (fiber a).val)) =
        ∑ a, (fiber a).card
      rw [Multiset.card_sigma]
      rfl
    have hrankQ : ∑ a, (Q.outcome a).rank ≤ Fintype.card ι := by
      have hsum_rank : ∑ a, (Q.outcome a).rank = ∑ a, (fiber a).card := by
        refine Finset.sum_congr rfl ?_
        intro a _
        simp [Q, MIPStarRE.Quantum.ProjectorRangeONB.subprojector_rank]
      calc
        ∑ a, (Q.outcome a).rank = ∑ a, (fiber a).card := hsum_rank
        _ = Large.card := hLarge_card_sum.symm
        _ = Fintype.card ι := by simpa [d] using hLarge_card
        _ ≤ Fintype.card ι := le_rfl
    have htotal_overlap : (∑ x : Idx, overlap x) ≤ 1 + 2 * Real.sqrt ζ := by
      have hoverlap_eq_ev_sum : (∑ x : Idx, overlap x) = ev ψ (∑ a, R.outcome a) := by
        simpa [Idx, overlap, rankOne] using
          (projectiveLowRankSum_truncationOverlap_eq_ev_sum
            (ψ := ψ) (R := R) (hproj := hR.projective) (onb := onb))
      have hev_le : ev ψ (∑ a, R.outcome a) ≤
          ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι)) := ev_mono ψ _ _ hRsum_le
      calc
        ∑ x : Idx, overlap x = ev ψ (∑ a, R.outcome a) := hoverlap_eq_ev_sum
        _ ≤ ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι)) := hev_le
        _ = 1 + 2 * Real.sqrt ζ := by
              have h :
                  ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ : Error) : ℂ) •
                    (1 : MIPStarRE.Quantum.Op ι)) =
                    1 + 2 * Real.sqrt ζ := by
                calc
                  ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ : Error) : ℂ) •
                      (1 : MIPStarRE.Quantum.Op ι))
                      = (1 + 2 * spectralTruncationError ζ) *
                          ev ψ (1 : MIPStarRE.Quantum.Op ι) :=
                        ev_scale ψ (1 + 2 * spectralTruncationError ζ)
                          (1 : MIPStarRE.Quantum.Op ι)
                  _ = 1 + 2 * Real.sqrt ζ := by
                        rw [ev_one_of_isNormalized ψ hψ, spectralTruncationError_eq_sqrt ζ]
                        ring
              simpa using h
    have hsmall : (∑ x ∈ (Largeᶜ : Finset Idx), overlap x) ≤ 4 * Real.sqrt ζ :=
      Truncation.sum_small_le_four_sqrt (α := Idx) Large
        (hL_card := hLarge_card) (hcard_gt := hcard_gt) (hr_bound := hr_bound)
        (hf_ordering := hLarge_order) (htotal := htotal_overlap)
        (hζ_nonneg := hζ) (hζ_le := hζ_le)
    have hLarge_compl_sigma :
        (Largeᶜ : Finset Idx) = (Finset.univ : Finset Outcome).sigma
          (fun a => (fiber a)ᶜ) := by
      ext x
      rcases x with ⟨a, i⟩
      constructor
      · intro h
        exact Finset.mem_sigma.mpr ⟨Finset.mem_univ a, by simpa [fiber] using h⟩
      · intro h
        rcases Finset.mem_sigma.mp h with ⟨_, hi⟩
        simpa [fiber] using hi
    have hqSDD_RQ : qSDDOp ψ R Q = ∑ x ∈ (Largeᶜ : Finset Idx), overlap x := by
      simpa [Q, Idx, overlap, rankOne] using
        (projectiveLowRankSum_qSDD_truncation_eq_compl_overlap
          (ψ := ψ) (R := R) (hproj := hR.projective) (onb := onb)
          (Large := Large) (fiber := fiber)
          (hLarge_compl_sigma := hLarge_compl_sigma))
    have hRQ : SDDOpRel ψ (uniformDistribution Unit) (constOpFamily R) (constOpFamily Q)
        (4 * spectralTruncationError ζ) := by
      have hcore : qSDDOp ψ R Q ≤ 4 * spectralTruncationError ζ := by
        calc
          qSDDOp ψ R Q = ∑ x ∈ (Largeᶜ : Finset Idx), overlap x := hqSDD_RQ
          _ ≤ 4 * Real.sqrt ζ := hsmall
          _ = 4 * spectralTruncationError ζ := by rw [hspectral_sqrt]
      constructor
      simpa [sddErrorOp, avgOver, uniformDistribution, constOpFamily] using hcore
    have hAQ : SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily Q)
        (roundingToProjectiveError ζ) := by
      have htri := MIPStarRE.LDT.Preliminaries.sddOpRel_triangle ψ (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily R) (constOpFamily Q)
        (2 * spectralTruncationError ζ) (4 * spectralTruncationError ζ)
        hR.closeness hRQ
      refine MIPStarRE.LDT.Preliminaries.sddOpRel_mono ψ (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily Q)
        (2 * (2 * spectralTruncationError ζ + 4 * spectralTruncationError ζ))
        (roundingToProjectiveError ζ) htri ?_
      dsimp [roundingToProjectiveError, spectralTruncationError]
      ring_nf
      exact le_rfl
    have hQtotal_le : Q.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
        (1 : MIPStarRE.Quantum.Op ι) := by
      have hpoint : ∀ a, Q.outcome a ≤ R.outcome a := by
        intro a
        simpa [Q] using (onb a).subprojector_le (fiber a)
      calc
        Q.total = ∑ a, Q.outcome a := rfl
        _ ≤ ∑ a, R.outcome a := Finset.sum_le_sum fun a _ => hpoint a
        _ ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι) := hRsum_le
    obtain ⟨auxSpace, t, _, hAuxDim⟩ :=
      projectiveLowRankSum_auxData_of_rank_bound
        (m := fun a : Outcome => (Q.outcome a).rank) hrankQ
    let data : QLayerData Outcome ι :=
      { auxSpace := auxSpace
        q := Q
        t := t }
    refine ⟨data, ?_⟩
    refine ⟨?_, ?_, ?_, source_almost_projective, ?_, ?_, ?_, ?_⟩
    · intro a
      simpa [Q, Qa, data] using (onb a).subprojector_isProj (fiber a)
    · intro a
      have hproj : MIPStarRE.Quantum.IsProj (Q.outcome a) := by
        simpa [Q] using (onb a).subprojector_isProj (fiber a)
      simpa [Qa, data] using hproj.nonneg
    · simp [Qa, QTotal, data, Q]
    · simpa [data] using hAQ
    · simpa [QTotal, data] using hQtotal_le
    · simpa [Qa, data] using hrankQ
    · simpa [data] using hAuxDim

/-- Internal rank-reduction constructor from an already rounded projective family.

Construct the paper's rank-reduced family `Q_a`, together with the auxiliary
projective measurement `T_a`, so that `Q_a` remains close to `A_a`, its total
stays bounded by `(1 + 2√ζ)I`, and the auxiliary dimension is at most the
original ambient dimension.

Paper source: proof of `\label{lem:projective-low-rank-sum}` in
`references/ldt-paper/orthonormalization.tex:540-658`, after applying
`\label{lem:projective-non-measurement}`.

**Source:** This is a source-faithful internal helper for the part of the proof
after the rounded family `R_a` has been obtained.  It starts from a chosen
rounded family carrying the explicit witness
`RoundingToProjectorsWitness ψ A ζ q`; equivalently, it consumes a concrete
witness of the statement `projectiveNonMeasurement ψ A ζ`.  The paper-facing
`projectiveLowRankSum` applies the rounding lemma internally before calling
this constructor.

The auxiliary space `ℂ^m` and the projective measurement
`T_a = ∑_i |a,i⟩⟨a,i|` come from the subsequent
"Matrix decomposition of `Q_a`" definition (orthonormalization.tex:777-795).
The proof uses the `r ≤ d` rank-bound branch directly and otherwise performs
the paper's `r > d` truncation branch from orthonormalization.tex:559-658: it
chooses the top-overlap `Large` set, assembles the truncated projectors from
`MIPStarRE.Quantum.IsProj.rangeONB`, proves the `4√ζ` truncation error, and
then builds the finite auxiliary projective measurement from the resulting rank
bound. The broader downstream `QXPLayerData` construction is intentionally
separated from this rank-reduction theorem: its statement now requires only the
primitive `X / XHat / P` identities used later, rather than explicit
rectangular complex-SVD matrices. -/
lemma projectiveLowRankSum_of_roundingWitness {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1 / 4)
    (q : OpFamily Outcome ι)
    (hrounded : RoundingToProjectorsWitness ψ A ζ q)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  classical
  by_cases hOutcome : Nonempty Outcome
  · let : Nonempty Outcome := hOutcome
    exact projectiveLowRankSum_truncate ψ hψ A ζ hζ hζ_le q hrounded
      source_almost_projective
  · let : IsEmpty Outcome := not_nonempty_iff.mp hOutcome
    exfalso
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have htotal_zero : A.toSubMeas.total = 0 := by
      simpa using A.toSubMeas.sum_eq_total.symm
    have hzero_one : (0 : MIPStarRE.Quantum.Op ι) = 1 := by
      rw [← htotal_zero, A.total_eq_one]
    have hentry : (0 : ℂ) = 1 := by
      simpa using congrFun (congrFun hzero_one i) i
    norm_num at hentry


end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


