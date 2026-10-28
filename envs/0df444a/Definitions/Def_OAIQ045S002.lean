-- Prove2me | Definitions.Def_OAIQ045S002
-- name    : OAIQ045S002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:22:59.008357+00:00
-- url     : https://prove2.me/theorems/e03ff184-ceb3-49bd-8669-4d87f5fdb520
-- title:
--   Definitions bundle OAIQ045S002 of the split of OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 232 declarations of OpenAI's Lean: 175 definitions and 57 theorems. The definitions and types are `OAI.SharpLogRamsey.GeometricCover.Description`, `OAI.SharpLogRamsey.Marking.cheapBoth`, `OAI.SharpLogRamsey.Marking.codeTuple`, `OAI.SharpLogRamsey.Marking.conditionedDeficit`, `OAI.SharpLogRamsey.Marking.covectorDomain`, `OAI.SharpLogRamsey.Marking.covectorTuple`, `OAI.SharpLogRamsey.Marking.excessCost`, `OAI.SharpLogRamsey.Marking.expensiveBudget`, `OAI.SharpLogRamsey.Marking.flagKind`, `OAI.SharpLogRamsey.Marking.maskAt`, `OAI.SharpLogRamsey.Marking.messageClass`, `OAI.SharpLogRamsey.Marking.pairCode`, `OAI.SharpLogRamsey.Marking.potential`, `OAI.SharpLogRamsey.Marking.reversedPairs`, `OAI.SharpLogRamsey.Marking.scan`, `OAI.SharpLogRamsey.Marking.secondMessage`, `OAI.SharpLogRamsey.Marking.sourceMessage`, `OAI.SharpLogRamsey.Marking.stepPrefactor`, `OAI.SharpLogRamsey.Marking.tupleMask`, `OAI.SharpLogRamsey.Marking.twoDomain`, `OAI.SharpLogRamsey.Marking.twoMask`, `OAI.SharpLogRamsey.NonplaneCertificate.flatFamily`, `OAI.SharpLogRamsey.PlanarLearning.Input`, `OAI.SharpLogRamsey.PlanarLearning.decode`, `OAI.SharpLogRamsey.PreparedDecoder.decode`, `OAI.SharpLogRamsey.PreparedDescription.good`, `OAI.SharpLogRamsey.PreparedGeometry.badHyperplanes`, `OAI.SharpLogRamsey.PreparedProposals.accepts`, `OAI.SharpLogRamsey.PreparedProposals.proposal`, `OAI.SharpLogRamsey.PreparedRow.rowTest`, `OAI.SharpLogRamsey.Projection.Collides`, `OAI.SharpLogRamsey.Projection.cut`, `OAI.SharpLogRamsey.Projection.flat_JoinedProjectionCenterTools_1`, `OAI.SharpLogRamsey.Projection.liftCap`, `OAI.SharpLogRamsey.Projection.liftedLibrary`, `OAI.SharpLogRamsey.Projection.orderedCollisions`, `OAI.SharpLogRamsey.Projection.project`, `OAI.SharpLogRamsey.Projection.projectDual`, `OAI.SharpLogRamsey.Projection.projected`, `OAI.SharpLogRamsey.Projection.quotientCut` and 135 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/SharpRamsey, in whole or in part: `SharpRamsey_Construction_InitialTools`, `SharpRamsey_Entropy_CompleteProgramWeight`, `SharpRamsey_Entropy_ExternalMass`, `SharpRamsey_Entropy_LargeCard`, `SharpRamsey_Entropy_MarkingTwoEntropy`, `SharpRamsey_Entropy_TreeCodeEntropy`, `SharpRamsey_Entropy_TruncatedTupleIntegrable`, `SharpRamsey_Execution_ExecutedConditioning`, `SharpRamsey_Execution_ExecutedReplacement`, `SharpRamsey_Execution_OutputComposition`, `SharpRamsey_Execution_OutputRebase`, `SharpRamsey_Execution_PreparedOutput`, `SharpRamsey_Exposure_DivergenceMap`, `SharpRamsey_Exposure_ExposureAverages`, `SharpRamsey_Exposure_ExposureBudget`, `SharpRamsey_Exposure_ExposureContexts`, `SharpRamsey_Exposure_ExposureGood`, `SharpRamsey_Exposure_ExposureMixture`, `SharpRamsey_Exposure_ExposureModel`, `SharpRamsey_Exposure_ExposureRealization`, `SharpRamsey_Exposure_MixtureRealization`, `SharpRamsey_Exposure_PreparedMixture`, `SharpRamsey_Exposure_RemainingEmbedding`, `SharpRamsey_Exposure_SourceCoupling`, `SharpRamsey_Exposure_SourceExposure`, `SharpRamsey_Exposure_SupportMixtures`, `SharpRamsey_Exposure_ZeroExposure`, `SharpRamsey_Geometry_GeometricInduction`, `SharpRamsey_Geometry_Projection`, `SharpRamsey_Geometry_ProjectionCenterTools`, `SharpRamsey_Geometry_ProjectionPublic`, `SharpRamsey_Geometry_QuotientSupports`, `SharpRamsey_Geometry_TotalDegreeCombination`, `SharpRamsey_Learning_PreparedDecoder`, `SharpRamsey_Learning_PreparedDescription`, `SharpRamsey_Learning_PreparedGeometry`, `SharpRamsey_Learning_PreparedProposals`, `SharpRamsey_Learning_ReadyTests`, `SharpRamsey_Learning_TestActualRow`, `SharpRamsey_Learning_ValidationCover`, `SharpRamsey_Marking_ClassConditioning`, `SharpRamsey_Marking_ClassStep`, `SharpRamsey_Marking_ClassTransport`, `SharpRamsey_Marking_FinalMarking`, `SharpRamsey_Marking_GoodIndices`, `SharpRamsey_Marking_GoodRealization`, `SharpRamsey_Marking_GoodRound`, `SharpRamsey_Marking_HighRankEndpoints`, `SharpRamsey_Marking_MarkingActual`, `SharpRamsey_Marking_MarkingCaps`, `SharpRamsey_Marking_MarkingClassSelection`, `SharpRamsey_Marking_MarkingClassification`, `SharpRamsey_Marking_MarkingFiniteClasses`, `SharpRamsey_Marking_MarkingOrientation`, `SharpRamsey_Marking_MarkingTwoCaps`, `SharpRamsey_Marking_MarkingTwoScans`, `SharpRamsey_Marking_Popular`, `SharpRamsey_Marking_RawLowerTail`, `SharpRamsey_Marking_StageBudget`, `SharpRamsey_Parameters_IterationScales`, `SharpRamsey_Parameters_NumericalIteration`, `SharpRamsey_Parameters_SourceScaleComparisons`, `SharpRamsey_Planar_PlanarPublic`, `SharpRamsey_Reciprocal_ExposureReciprocal`, `SharpRamsey_Reciprocal_LevelLosses`, `SharpRamsey_Reciprocal_ProdRectangleEvent`, `SharpRamsey_Reciprocal_Reciprocal`, `SharpRamsey_Reciprocal_ReciprocalActualCharges`, `SharpRamsey_Reciprocal_ReciprocalBands`, `SharpRamsey_Reciprocal_ReciprocalChargeHistories`, `SharpRamsey_Reciprocal_ReciprocalCurrent`, `SharpRamsey_Selection_EndpointCurrent`, `SharpRamsey_Selection_FreshFamilies`, `SharpRamsey_Selection_FreshRepresentatives`, `SharpRamsey_Selection_NullFreeLaw`, `SharpRamsey_Selection_UniversalTables`, `SharpRamsey_Spatial_SpatialPublic`, `SharpRamsey_Trees_PivotCalls`, `SharpRamsey_Trees_TreeDecoder`, `SharpRamsey_Windows_ExposureWindows`, `SharpRamsey_Windows_GoodPopulation`, `SharpRamsey_Windows_IntegerExperiment`, `SharpRamsey_Windows_IntegerQuarter`, `SharpRamsey_Windows_IntegerRealization`, `SharpRamsey_Windows_OpenExperiment`, `SharpRamsey_Windows_OpenQuarter`, `SharpRamsey_Windows_OpenRealization`, `SharpRamsey_Windows_PreparedWindows`, `SharpRamsey_Windows_UniformInteger`, `SharpRamsey_Windows_UniformOpen`, `SharpRamsey_Windows_WindowLayout`.
--
--   **Imports.** It imports the bundles `OAIQ045S000` and `OAIQ045S001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpLogRamsey.Marking.eventually_class_step`, `OAI.SharpLogRamsey.Marking.eventually_tracked_step`, `OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform`, `OAI.SharpLogRamsey.PreparedRow.geometric_row_probability`, `OAI.SharpLogRamsey.Selection.Windows.eventually_integer_decoder`, `OAI.SharpLogRamsey.Selection.Windows.eventually_open_decoder`, `OAI.SharpLogRamsey.Selection.Windows.eventually_open_movement`, `OAI.SharpLogRamsey.Selection.Windows.eventually_prepared_high`, `OAI.SharpLogRamsey.Selection.Windows.integer_population_realization`, `OAI.SharpLogRamsey.Selection.Windows.open_population_realization`, `OAI.SharpLogRamsey.Selection.Windows.prepared_context_of_mean` and `OAI.SharpLogRamsey.SpatialPublic.actual_prepared_input`; the proofs of `OAI.SharpLogRamsey.ActualPivot.Book.live_realization`, `OAI.SharpLogRamsey.ActualPivot.supplied_book`, `OAI.SharpLogRamsey.GeometricCover.uniform_four`, `OAI.SharpLogRamsey.LowerTransfer.prime_construction`, `OAI.SharpLogRamsey.Marking.eventually_class_step`, `OAI.SharpLogRamsey.Marking.eventually_high_ordered`, `OAI.SharpLogRamsey.Marking.eventually_tracked_step`, `OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform`, `OAI.SharpLogRamsey.PreparedRow.geometric_row_probability`, `OAI.SharpLogRamsey.Selection.Windows.eventually_integer_decoder`, `OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output`, `OAI.SharpLogRamsey.Selection.Windows.eventually_open_decoder`, `OAI.SharpLogRamsey.Selection.Windows.eventually_open_movement`, `OAI.SharpLogRamsey.Selection.Windows.eventually_open_output`, `OAI.SharpLogRamsey.Selection.Windows.eventually_prepared_high`, `OAI.SharpLogRamsey.Selection.Windows.integer_population_realization`, `OAI.SharpLogRamsey.Selection.Windows.open_population_realization`, `OAI.SharpLogRamsey.Selection.Windows.prepared_context_of_mean`, `OAI.SharpLogRamsey.SpatialPublic.actual_cover` and `OAI.SharpLogRamsey.SpatialPublic.actual_prepared_input`.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/SharpRamsey at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ045S000
import Definitions.Def_OAIQ045S001

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def Law.AbsolutelyContinuous (p q : Law α) : Prop := ∀ a, q.mass a = 0 → p.mass a = 0

noncomputable def divergence (p q : Law α) : ℝ :=
  ∑ a, p.mass a * Real.log (p.mass a / q.mass a)

theorem divergence_nonneg (p q : Law α) (hab : p.AbsolutelyContinuous q) :
    0 ≤ divergence p q := by
  calc
    0 = ∑ a, (p.mass a-q.mass a) := by rw [sum_sub_distrib,p.total,q.total]; ring
    _ ≤ _ := sum_le_sum fun a ha => mul_log_div_ge (p.nonneg a) (q.nonneg a) (hab a)

theorem Law.event_nonneg (p : Law α) (E : Finset α) : 0 ≤ p.event E :=
  sum_nonneg fun a _ha => p.nonneg a

theorem Law.le_fst (p : Law (α × β)) (a : α) (b : β) : p.mass (a,b) ≤ p.fst.mass a :=
  single_le_sum (fun c _hc => p.nonneg (a,c)) (mem_univ b)

theorem Law.absContinuous_prod (p : Law (α × β)) : p.AbsolutelyContinuous (p.fst.prod p.snd) := by
  rintro ⟨a,b⟩ h
  rcases mul_eq_zero.mp h with h | h
  · exact le_antisymm (by simpa [h] using p.le_fst a b) (p.nonneg _)
  · exact le_antisymm (by simpa [h] using p.le_snd a b) (p.nonneg _)

noncomputable def mutualInfo (p : Law (α × β)) : ℝ :=
  entropy p.fst+entropy p.snd-entropy p

theorem mutualInfo_eq_divergence (p : Law (α × β)) :
    mutualInfo p = divergence p (p.fst.prod p.snd) := by
  have he (a : α) (b : β) : p.mass (a,b)*Real.log (p.mass (a,b)/(p.fst.mass a*p.snd.mass b)) =
      p.mass (a,b)*Real.log (p.mass (a,b))-
      p.mass (a,b)*Real.log (p.fst.mass a)-p.mass (a,b)*Real.log (p.snd.mass b) := by
    by_cases h : p.mass (a,b) = 0
    · simp [h]
    have hp := lt_of_le_of_ne (p.nonneg (a,b)) (Ne.symm h)
    have hf : 0 < p.fst.mass a := hp.trans_le (p.le_fst a b)
    have hs : 0 < p.snd.mass b := hp.trans_le (p.le_snd a b)
    rw [Real.log_div h (mul_ne_zero hf.ne' hs.ne'),Real.log_mul hf.ne' hs.ne']
    ring
  have hf : ∑ a, ∑ b, p.mass (a,b)*Real.log (p.fst.mass a) =
      ∑ a, p.fst.mass a*Real.log (p.fst.mass a) := by
    apply sum_congr rfl; intro a ha
    rw [← sum_mul]; rfl
  have hs : ∑ a, ∑ b, p.mass (a,b)*Real.log (p.snd.mass b) =
      ∑ b, p.snd.mass b*Real.log (p.snd.mass b) := by
    rw [sum_comm]
    apply sum_congr rfl; intro b hb
    rw [← sum_mul]; rfl
  unfold divergence mutualInfo entropy Law.prod
  simp only [Fintype.sum_prod_type, he, sum_sub_distrib]
  rw [hf,hs]
  ring

theorem mutualInfo_nonneg (p : Law (α × β)) : 0 ≤ mutualInfo p := by
  rw [mutualInfo_eq_divergence]
  exact divergence_nonneg _ _ p.absContinuous_prod

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_DivergenceMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def totalCorrelation (p : Law (ι → β)) : ℝ :=
  (∑ i, entropy (p.marginal i))-entropy p

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

noncomputable def pairInformation (p : Law (ι → β)) (i j : ι) : NNReal :=
  ⟨mutualInfo (p.map (fun x => (x i,x j))),mutualInfo_nonneg _⟩

noncomputable def exposedInformation (p : Law (ι → β)) (i : ι) (E : Finset ι) : NNReal :=
  ⟨mutualInfo (p.map (fun x => (x i,fun j : E => x j))),mutualInfo_nonneg _⟩

noncomputable def maximumInformation (p : Law (ι → β)) (i : ι) (J : Finset ι) : NNReal :=
  J.sup (pairInformation p i)

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RemainingEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical
noncomputable section
variable {B β ι : Type*} [Fintype B] [Fintype β] [Fintype ι] [DecidableEq ι] [DecidableEq B]

def roundInformation {m : ℕ} (p : Law (ι → β)) (e : B×Fin m  ↪  ι) (own : ι → Option B) : ℝ :=
  (∑ f : B → Fin m, ∑ i, (maximumInformation p i (otherRepresentatives e own f i):ℝ))/
    Fintype.card (B → Fin m)

def nextPotential {m : ℕ} (p : Law (ι → β)) (e : B×Fin m  ↪  ι) : ℝ :=
  (∑ f : B → Fin m, ∑ z, (p.restrict (freshRepresentatives e f)).mass z*
    totalCorrelation ((p.cond (fun x (j:freshRepresentatives e f) => x j) z).restrict
      (freshRepresentatives e f)ᶜ))/Fintype.card (B → Fin m)

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset
open scoped Classical
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

def exposureScores (n : ℕ) : (k : ℕ) → {ι : Type u} → [Fintype ι] → [DecidableEq ι] →
    Law (ι → β) → (B × Fin (n+k) ↪ ι) → (ι → Option B) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases (roundInformation p e own)
      (fun t => (∑ f : B → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          exposureScores n k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (B → Fin (n+k+1))) j

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

def tupleDeficit (J : ℝ) (p : Law (ι → β)) : ℝ :=
  (Fintype.card ι:ℝ)*J-entropy p

end
end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
variable {Ω α Γ A : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype A]
theorem entropy_le_log_card (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) : entropy p ≤ Real.log S.card := by
  have hS : 0 < S.card := by
    by_contra! h
    have hz : S = ∅ := card_eq_zero.mp (by omega)
    have hzero : ∑ a, p.mass a = 0 := by
      apply sum_eq_zero
      intro a ha
      exact hs a (by simp [hz])
    linarith [p.total]
  have hsr : (0:ℝ) < S.card := by exact_mod_cast hS
  have hmass : ∑ a ∈ S, p.mass a = 1 := by
    rw [← p.total]
    exact sum_subset (subset_univ S) fun a ha hna => hs a hna
  have h := log_sum S p.mass (fun _ => 1/(S.card:ℝ))
    (fun a ha => p.nonneg a) (fun a ha => by positivity)
    (fun a ha hh => False.elim ((div_ne_zero (by norm_num) hsr.ne') hh))
  rw [hmass] at h
  have hc : ∑ _a ∈ S, (1/(S.card:ℝ)) = 1 := by
    simp only [sum_const, nsmul_eq_mul]
    field_simp
  rw [hc,div_one,Real.log_one,mul_zero] at h
  have he (a : α) : p.mass a*Real.log (p.mass a/(1/(S.card:ℝ))) =
      p.mass a*Real.log (p.mass a)+p.mass a*Real.log S.card := by
    by_cases hz : p.mass a = 0
    · simp [hz]
    rw [div_div_eq_mul_div, div_one, Real.log_mul hz hsr.ne']
    ring
  simp_rw [he] at h
  rw [sum_add_distrib, ← sum_mul, hmass,one_mul] at h
  have hh : ∑ a ∈ S, p.mass a*Real.log (p.mass a) =
      ∑ a, p.mass a*Real.log (p.mass a) := by
    exact sum_subset (subset_univ S) fun a ha hna => by rw [hs a hna,zero_mul]
  rw [hh] at h
  unfold entropy
  linarith

lemma Law.cond_support (p : Law Ω) (C : Ω → Γ) (c : Γ)
    (hc : (p.map C).mass c ≠ 0) (x : Ω) (hx : (p.cond C c).mass x ≠ 0) :
    p.mass x ≠ 0 ∧ C x = c := by
  rw [p.cond_mass C c hc] at hx
  split_ifs at hx with he
  · exact ⟨(div_ne_zero_iff.mp hx).1,he⟩
  · exact False.elim (hx (zero_div _))

end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

def tupleSupported (p : Law (ι → β)) (D : ι → Finset β) : Prop :=
  ∀ x, p.mass x ≠ 0 → ∀ i, x i ∈ D i

end
end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

def exposureDeficits (n : ℕ) (J : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → β) → (B × Fin (n+k) ↪ ι) → Fin k → ℝ
  | 0, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, j => Fin.cases (tupleDeficit J p)
      (fun t => (∑ f : B → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          exposureDeficits n J k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) t) /
          Fintype.card (B → Fin (n+k+1))) j

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β B X ι : Type*} [Fintype β] [Fintype B] [Fintype X] [Fintype ι]
  [DecidableEq B] [DecidableEq ι]

def badIndices (p : Law (ι→β)) (e : B×X ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) (f : B→X) : Finset ι :=
  univ.filter (fun i => D<J-entropy (p.marginal i) ∨
    ∃ j∈otherRepresentatives e own f i,a<(pairInformation p i j:ℝ)+(c i j:ℝ))

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β B ι : Type*} [Fintype β] [Fintype B] [Fintype ι] [DecidableEq B] [DecidableEq ι]

def roundBad {m : ℕ} (p : Law (ι→β)) (e : B×Fin m ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) : ℝ :=
  (∑ f : B→Fin m,((badIndices p e own c J D a f).card:ℝ))/Fintype.card (B→Fin m)

def roundSelectedBad {m : ℕ} (p : Law (ι→β)) (e : B×Fin m ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) : ℝ :=
  (∑ f : B→Fin m,
    ((freshRepresentatives e f∩badIndices p e own c J D a f).card:ℝ))/Fintype.card (B→Fin m)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

def exposureBad (n : ℕ) (J D a : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → β) → (B × Fin (n+k) ↪ ι) →
    (ι → Option B) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases
      (roundBad p e own (fun _ _ => 0) J D a)
      (fun t => (∑ f : B → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          exposureBad n J D a k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (B → Fin (n+k+1))) j

def exposureSelectedBad (n : ℕ) (J D a : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → β) → (B × Fin (n+k) ↪ ι) →
    (ι → Option B) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases
      (roundSelectedBad p e own (fun _ _ => 0) J D a)
      (fun t => (∑ f : B → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          exposureSelectedBad n J D a k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (B → Fin (n+k+1))) j

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Selection
variable {α : Type*} [Fintype α]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable def Law.tests (p : Law α) (v : α → V) (ρ : ℝ) : Set (Module.Dual K V) :=
  {f | p.event (univ.filter (fun a => f (v a) ≠ 0)) ≤ ρ}

noncomputable def Law.core (p : Law α) (v : α → V) (ρ : ℝ) : Submodule K V :=
  (Submodule.span K (p.tests (K:=K) v ρ)).dualCoannihilator

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

def Law.condSnd (p : Law (A × B)) (a : A) : Law B :=
  (p.cond Prod.fst a).map Prod.snd

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ProdRectangleEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def firstCore (p : Law (A × B)) (v : B → V) (ρ : ℝ) (a : A) : Submodule K V :=
  (p.condSnd a).core v ρ

def secondCore (p : Law (A × B)) (w : A → Module.Dual K V) (ρ : ℝ) (y : B) :
    Submodule K (Module.Dual K V) := (p.condFst y).core w ρ

def coreContained (p q : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    (ρ : ℝ) (a : A) (y : B) : Prop :=
  secondCore q w ρ y ≤ (firstCore (K := K) p v ρ a).dualAnnihilator

def coreCollision (p q : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    (ρ : ℝ) (goodA : A → Prop) (goodB : B → Prop) (z : (A × B) × (A × B)) : Prop :=
  goodA z.1.1 ∧ goodB z.2.2 ∧ w z.1.1 (v z.2.2) = 0 ∧
    coreContained p q v w ρ z.1.1 z.2.2 ∧
    v z.1.2 ∈ firstCore (K := K) p v ρ z.1.1 ∧ w z.2.1 ∈ secondCore q w ρ z.2.2

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]

lemma Law.event_map (p : Law Ω) (f : Ω → A) (E : Finset A) :
    (p.map f).event E = p.event (univ.filter (fun x => f x ∈ E)) := by
  have h := p.sum_map f (fun a => if a ∈ E then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, ← sum_filter, filter_mem_eq_inter, univ_inter,
    Law.event] using h

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalActualCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {A B ι : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def rectangleBound (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V) (M : ℝ) : Prop :=
  ∀ x,p.mass x≠0 → ∀ W : Submodule K V,
    ((univ.filter (fun i => x i∈orthogonalRectangle v w W)).card:ℝ)≤M

def tupleFlags (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V) : Prop :=
  ∀ x,p.mass x≠0 → ∀ i,w (x i).1 (v (x i).2)=0

def rankCollision (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (ρ : ℝ) (r s : ℕ) (i j : ι) (x : ι→A×B) : Prop :=
  coreCollision (p.marginal i) (p.marginal j) v w ρ
    (fun a => r≤Module.finrank K (firstCore (K:=K) (p.marginal i) v ρ a))
    (fun y => s≤Module.finrank K (secondCore (p.marginal j) w ρ y)) (x i,x j)

def directedCollision (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (ρ : ℝ) (r s : ℕ) (i j : ι) : ℝ≥0 :=
  ⟨p.event (univ.filter (rankCollision p v w ρ r s i j)),p.event_nonneg _⟩

def reciprocalCharges (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (ρ : ℝ) (r s : ℕ) (i j : ι) : ℝ≥0 :=
  directedCollision p v w ρ r s i j+directedCollision p v w ρ r s j i

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalChargeHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

def Law.revealRest (p : Law (ι→α)) (E : Finset ι) (z : E→α) : Law (↥(Eᶜ)→α) :=
  (p.cond (fun x (i:E) => x i) z).restrict Eᶜ

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ExposureReciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
universe u v w
variable {C : Type v} {A B : Type w} [Fintype C] [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def chargedBad (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (n : ℕ) (J D a : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → A×B) → (C × Fin (n+k) ↪ ι) →
    (ι → Option C) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases
      (roundBad p e own (reciprocalCharges p v w ρ r s) J D a)
      (fun t => (∑ f : C → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          chargedBad v w ρ r s n J D a k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (C → Fin (n+k+1))) j

def chargedSelectedBad (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (n : ℕ) (J D a : ℝ) : (k : ℕ) → {ι : Type u} → [Fintype ι] →
    [DecidableEq ι] → Law (ι → A×B) → (C × Fin (n+k) ↪ ι) →
    (ι → Option C) → Fin k → ℝ
  | 0, _, _, _, _, _, _, j => Fin.elim0 j
  | k+1, _, _, _, p, e, own, j => Fin.cases
      (roundSelectedBad p e own (reciprocalCharges p v w ρ r s) J D a)
      (fun t => (∑ f : C → Fin (n+k+1),
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z *
          chargedSelectedBad v w ρ r s n J D a k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) t) /
          Fintype.card (C → Fin (n+k+1))) j

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureContexts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
universe u v w z
variable {Θ : Type z} {C : Type v} {β : Type w} {ι : Type u}
variable [Fintype Θ] [Fintype C] [Fintype β] [Fintype ι] [DecidableEq ι]

def contextAverage (μ : Law Θ) (f : Θ → ℝ) : ℝ := ∑ θ, μ.mass θ*f θ

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_EndpointCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

def conditionalHeavy (p : Law (α × β)) (L K : ℝ) (b : β) : ℝ :=
  (p.condFst b).event (univ.filter (fun a => Real.exp (K-L) < p.mass (a,b)))

def goodSecond (p : Law (α × β)) (M L K ρ : ℝ) (b : β) : Prop :=
  Real.exp (-K)/M ≤ p.snd.mass b ∧ conditionalHeavy p L K b ≤ ρ

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_Reciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

def goodFirst (p : Law (A×B)) (M L κ ε : ℝ) (a : A) : Prop :=
  exp (-κ)/M ≤ p.fst.mass a ∧
  (p.condSnd a).event (univ.filter (fun b => exp (κ-L)<p.mass (a,b)))≤ε

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_LevelLosses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def positiveSupport (p : Law α) : Finset α := univ.filter (fun a => 0<p.mass a)

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Marking

section FinitePotential
variable {Y : Type*} [Fintype Y]

noncomputable def potential (D : ℕ) (r : Y → ℕ) : ℝ :=
  ∑ l ∈ range (D+1), Real.log ((below r l).card + 1 : ℝ)

end FinitePotential

section State
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]

noncomputable def scan (q : ℝ) : State (K:=K) (V:=V) →
    List (Module.Dual K V × Points (K:=K) (V:=V)) → ℕ × State (K:=K) (V:=V)
  | W, [] => (0,W)
  | W, f :: fs =>
    if IsExpensive W q f then
      let p := scan q (update W f.1 f.2) fs
      (p.1+1,p.2)
    else scan q W fs

end State
end SharpLogRamsey.Marking

namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem poor_marginal_product {n : ℕ} (hdim : Module.finrank K V = n+3)
    (W : State (K:=K) (V:=V)) (l : ℕ) :
    ((level (ranks W) l).card:ℝ)*(poorDomain W l).card ≤
      16*(Nat.card K:ℝ)^(n+3) := by
  apply sparse_product_bound hdim
  have hq : (0:ℝ) < Nat.card K := by
    exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  calc
    (incidenceCount (level (ranks W) l) (poorDomain W l):ℝ) ≤
        ∑ _a ∈ poorDomain W l, ((level (ranks W) l).card:ℝ)/(8*Nat.card K) := by
      rw [incidenceCount, Nat.cast_sum]
      apply sum_le_sum
      intro a ha
      have h := (mem_filter.mp ha).2
      exact h
    _ = ((level (ranks W) l).card:ℝ)*(poorDomain W l).card/(8*Nat.card K) := by
      simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((level (ranks W) l).card:ℝ)*(poorDomain W l).card/(4*Nat.card K) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith

end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_Popular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
omit [Fintype (Projectivization K (Module.Dual K V))] in
theorem popular_zero (W : State (K:=K) (V:=V))
    (hZ : (level (ranks W) 0).Nonempty) : popularDomain W 0 = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hp := (mem_filter.mp hb).2
  have hempty : (level (ranks W) 0).filter (fun y => b.submodule ≤ W y) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hr : Module.finrank K (W y) = 0 := by simpa [level,ranks] using (mem_filter.mp hy).1
    have hz : W y = ⊥ := Submodule.finrank_eq_zero.mp hr
    have hh := (mem_filter.mp hy).2
    rw [hz] at hh
    apply b.rep_nonzero
    have hm : b.rep ∈ b.submodule := by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    exact hh hm
  unfold Popular at hp
  rw [hempty, card_empty, Nat.cast_zero] at hp
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  have hn : (0:ℝ) < (level (ranks W) 0).card := by exact_mod_cast card_pos.mpr hZ
  exact (not_le_of_gt (div_pos hn (by positivity))) hp

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))] in
theorem popular_card (W : State (K:=K) (V:=V)) (l : ℕ)
    (hZ : (level (ranks W) (l+1)).Nonempty) :
    ((popularDomain W (l+1)).card:ℝ) ≤ 32*(Nat.card K:ℝ)^(l+1) := by
  let Z := level (ranks W) (l+1)
  let B := popularDomain W (l+1)
  let q : ℝ := Nat.card K
  have hq : 0 < q := by
    change (0:ℝ) < Nat.card K
    exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  have hZpos : (0:ℝ) < Z.card := by exact_mod_cast card_pos.mpr hZ
  have hdouble : ∑ b ∈ B, ((Z.filter (fun y => b.submodule ≤ W y)).card:ℝ) =
      ∑ y ∈ Z, ((B.filter (fun b => b.submodule ≤ W y)).card:ℝ) := by
    simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact sum_comm
  have hcount : (B.card:ℝ) * ((Z.card:ℝ)/(16*q)) ≤ (Z.card:ℝ)*(2*q^l) := by
    calc
      _ = ∑ _b ∈ B, ((Z.card:ℝ)/(16*q)) := by simp
      _ ≤ ∑ b ∈ B, ((Z.filter (fun y => b.submodule ≤ W y)).card:ℝ) := by
        apply sum_le_sum
        intro b hb
        exact (mem_filter.mp hb).2
      _ = ∑ y ∈ Z, ((B.filter (fun b => b.submodule ≤ W y)).card:ℝ) := hdouble
      _ ≤ ∑ _y ∈ Z, 2*q^l := by
        apply sum_le_sum
        intro y hy
        have hr : Module.finrank K (W y) = l+1 := by
          change y ∈ level (ranks W) (l+1) at hy
          exact (mem_filter.mp hy).2
        have hc := card_subspace_points_le (W y) hr
        exact (show ((B.filter (fun b => b.submodule ≤ W y)).card:ℝ) ≤
          ((univ.filter (fun b : Points (K:=K) (V:=V) => b.submodule ≤ W y)).card:ℝ) by
            exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ B))).trans hc
      _ = _ := by simp
  have hm := (mul_le_mul_of_nonneg_right hcount (show 0 ≤ 16*q by positivity))
  have he : (B.card:ℝ)*((Z.card:ℝ)/(16*q))*(16*q) = (B.card:ℝ)*Z.card := by
    field_simp
  rw [he] at hm
  change (B.card:ℝ) ≤ 32*q^(l+1)
  rw [pow_succ]
  have hh : (B.card:ℝ)*Z.card ≤ (32*(q^l*q))*Z.card := by nlinarith
  nlinarith

omit [Fintype (Projectivization K V)] in
theorem partner_card {d r : ℕ} (hdim : Module.finrank K V = d+1)
    (W : Submodule K V) (hW : Module.finrank K W = r) (hr : r ≤ d) :
    ((partnerDomain W).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-r) := by
  have he : partnerDomain W = univ.filter (fun a => a.submodule ≤ W.dualAnnihilator) := by
    ext a
    simp only [partnerDomain, mem_filter, mem_univ, true_and,
      Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_dualAnnihilator]
    rfl
  rw [he]
  apply card_subspace_points_le
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

def flagKind (q : ℝ) (W : State (K:=K) (V:=V)) (f : ScanFlag (K:=K) (V:=V)) : ScanKind :=
  if Popular W q (chosenLevel W f.2) f.2 then .popular
  else if Poor W q (chosenLevel W f.2) f.1 then .poor else .expensive

def maskAt (q : ℝ) (W : State (K:=K) (V:=V)) (f : ScanFlag (K:=K) (V:=V)) :
    RankMask (K:=K) (V:=V) :=
  (⟨ranks W f.2, Nat.lt_succ_of_le (Submodule.finrank_le _)⟩, flagKind q W f)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped Classical BigOperators
open Finset
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

def pairCode (q : ℝ) : State (K:=K) (V:=V) → List (ProjectivePair (K:=K) (V:=V)) →
    List (RankMask (K:=K) (V:=V) × Option (ProjectivePair (K:=K) (V:=V)))
  | _,[] => []
  | W,f::fs =>
    let s := if IsExpensive W q (toScan f) then some f else none
    (maskAt q W (toScan f),s)::pairCode q (pairStep W s) fs

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma pairCode_length (q : ℝ) (W : State (K:=K) (V:=V))
    (fs : List (ProjectivePair (K:=K) (V:=V))) : (pairCode q W fs).length=fs.length := by
  induction fs generalizing W with
  | nil => rfl
  | cons f fs ih => simp only [pairCode,List.length_cons,ih]

def codeTuple {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (i : Fin N) : RankMask (K:=K) (V:=V) × Option (ProjectivePair (K:=K) (V:=V)) :=
  (pairCode q (fun _ => ⊥) (List.ofFn F))[i.val]'(by rw [pairCode_length,List.length_ofFn]; exact i.isLt)

def tupleMask {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    Fin N → RankMask (K:=K) (V:=V) := fun i => (codeTuple q F i).1

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_FinalMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey
open scoped Classical BigOperators
open Finset
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma flagPair_injective : Function.Injective (flagPair (K:=K) (V:=V)) := by
  intro a b h
  cases a; cases b
  cases h
  rfl

end
end SharpLogRamsey

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingTwoScans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
open Finset ProjectiveDuality
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def reversedPairs {N : ℕ} (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    Fin N → ProjectivePair (K:=K) (V:=Module.Dual K V) := fun i => pairDuality (F i.rev)

def twoMask {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) : TwoMask (K:=K) (V:=V) N :=
  (tupleMask q F,tupleMask q (reversedPairs F))

def secondMessage {Γ : Type*} {N : ℕ} (z : TwoMessage (K:=K) (V:=V) Γ N) :
    (Fin N → Option (ProjectivePair (K:=K) (V:=Module.Dual K V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=Module.Dual K V))) :=
  (fun i => if i∈expensiveMask z.2.2.2 then (z.1 i.rev).map pairDuality else none,(z.2.1,z.2.2.2))

def cheapBoth {Γ : Type*} {N : ℕ} (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N) :
    Finset (ProjectivePair (K:=K) (V:=V)) :=
  cheapTuple (firstMessage z) i ∩ (cheapTuple (secondMessage z) i.rev).map pairDuality.symm.toEmbedding

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_MarkingTwoEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
noncomputable section
variable {Ω Γ α ι : Type*} [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype ι]

def selectedDeficit (p : Law Ω) (θ : Ω → Γ) (F : Ω → ι → α)
    (S : Γ → Finset ι) (J : ℝ) : ℝ :=
  ∑ z, (p.map θ).mass z*((S z).card*J-entropy (((p.cond θ z).map F).restrict (S z)))
end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

def sourceMessage {Ω Γ : Type*} {N : ℕ} (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) :
    Ω → TwoMessage (K:=K) (V:=V) Γ N :=
  Selection.markingMessage C (fun x => twoMask (Nat.card K) (F x)) bothExpensive F

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def excessCost {N : ℕ} (p : Selection.Law Ω) (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) (Jprev J₀ : ℝ) : ℝ :=
  Selection.entropy (p.map C)+Real.log (Fintype.card (TwoMask (K:=K) (V:=V) N))+
    N*J₀-Selection.entropy (p.map F)+
    (∑ x, p.mass x*((bothExpensive (twoMask (Nat.card K) (F x))).card:ℝ))*(Jprev-J₀)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {Ω Γ α ι : Type*} [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype ι]

omit [Fintype α] [Fintype ι] in
def Law.onContextEvent (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) : Law Ω where
  mass x := if θ x∈E then p.mass x/(p.map θ).event E else 0
  nonneg x := by
    split_ifs
    · exact div_nonneg (p.nonneg x) (le_of_lt hE)
    · exact le_refl 0
  total := by
    simp only [←sum_filter,←sum_div]
    change p.event (univ.filter (fun x=>θ x∈E))/(p.map θ).event E=1
    rw [←Law.event_map]
    exact div_self (ne_of_gt hE)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingClassSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

def expensiveBudget (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype (Projectivization K V)] : ℝ :=
  32*(Module.finrank K V+1)^2*(Nat.card K:ℝ)*
    Real.log (Fintype.card (Points (K:=K) (V:=V))+1:ℝ)

variable {Ω Γ κ : Type*} [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ]

omit [Fintype κ] [Nonempty κ] in

def conditionedDeficit {N : ℕ} (p : Selection.Law Ω) (C : Ω→Γ)
    (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
    (hE : 0<(p.map (sourceMessage C F)).event E)
    (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)) (J : ℝ) : ℝ :=
  Selection.selectedDeficit (p.onContextEvent (sourceMessage C F) E hE)
    (sourceMessage C F) F S J

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
open Finset ProjectiveDuality
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma popularJoint_mem {W : State (K:=K) (V:=V)} {l r : ℕ}
    {f : ProjectivePair (K:=K) (V:=V)} (hf : f∈popularJoint W l r) :
    f.1∈popularDomain W l ∧ ranks W f.1=r ∧ f.2∈partnerDomain (W f.1) := by
  obtain ⟨b,hb,hf⟩ := mem_biUnion.mp hf
  split_ifs at hf with hr
  · obtain ⟨a,ha,he⟩ := mem_image.mp hf
    subst f
    exact ⟨hb,hr,ha⟩
  · exact False.elim (notMem_empty _ hf)

lemma popularJoint_rank_pos {W : State (K:=K) (V:=V)} {l r : ℕ}
    (hl : l ≤ r) (hmax : (level (ranks W) r).card≤(level (ranks W) l).card)
    (h : (popularJoint W l r).Nonempty) : 1 ≤ r := by
  obtain ⟨f,hf⟩ := h
  obtain ⟨hp,hr,_⟩ := popularJoint_mem hf
  have hZ : (level (ranks W) l).Nonempty := by
    apply card_pos.mp
    apply (card_pos.mpr (show (level (ranks W) r).Nonempty from ⟨f.1,by simp [level,hr]⟩)).trans_le hmax
  by_contra hh
  have hr0 : r=0 := by omega
  have hl0 : l=0 := by omega
  subst l
  rw [popular_zero W hZ] at hp
  exact notMem_empty _ hp

lemma popularJoint_first_card (W : State (K:=K) (V:=V)) (l r : ℕ)
    (hl : l ≤ r) (hmax : (level (ranks W) r).card≤(level (ranks W) l).card) :
    (((popularJoint W l r).image Prod.fst).card:ℝ) ≤ 32*(Nat.card K:ℝ)^r := by
  by_cases he : popularJoint W l r=∅
  · rw [he,image_empty,card_empty,Nat.cast_zero]; positivity
  have hsub : (popularJoint W l r).image Prod.fst ⊆ popularDomain W l := by
    intro b hb
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hb
    exact (popularJoint_mem hf).1
  have hZ : (level (ranks W) l).Nonempty := by
    obtain ⟨f,hf⟩ := nonempty_iff_ne_empty.mpr he
    have hr := (popularJoint_mem hf).2.1
    exact card_pos.mp ((card_pos.mpr ⟨f.1,by simp [level,hr]⟩).trans_le hmax)
  have hc : ((popularDomain W l).card:ℝ) ≤ 32*(Nat.card K:ℝ)^l := by
    cases l with
    | zero => rw [popular_zero W hZ,card_empty,Nat.cast_zero]; norm_num
    | succ l => exact popular_card W l hZ
  exact (show (((popularJoint W l r).image Prod.fst).card:ℝ) ≤ (popularDomain W l).card by
    exact_mod_cast card_le_card hsub).trans (hc.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (show (1:ℝ)≤Nat.card K by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le) hl)
      (by norm_num)))

lemma popularJoint_fiber_card {d r : ℕ} (hdim : Module.finrank K V=d+1)
    (W : State (K:=K) (V:=V)) (l : ℕ) (hr : r≤d) (b : Projectivization K V) :
    (((popularJoint W l r).filter (fun f => f.1=b)).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-r) := by
  by_cases hb : ranks W b=r
  · have hsub : (popularJoint W l r).filter (fun f => f.1=b) ⊆
        (partnerDomain (W b)).image (Prod.mk b) := by
      intro f hf
      obtain ⟨hf,hfb⟩ := mem_filter.mp hf
      have hm := (popularJoint_mem hf).2.2
      exact mem_image.mpr ⟨f.2,by simpa only [hfb] using hm,by cases f; simp_all⟩
    have hc := card_le_card hsub
    rw [card_image_of_injective _ (by intro a a' h; exact Prod.mk.inj h |>.2)] at hc
    exact (show (((popularJoint W l r).filter (fun f => f.1=b)).card:ℝ) ≤
      (partnerDomain (W b)).card by exact_mod_cast hc).trans (partner_card hdim (W b) hb hr)
  · have he : (popularJoint W l r).filter (fun f => f.1=b)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro f hf
      obtain ⟨hf,hfb⟩ := mem_filter.mp hf
      exact hb (hfb ▸ (popularJoint_mem hf).2.1)
    rw [he,card_empty,Nat.cast_zero]; positivity

lemma cheapPopular_first_card (W : State (K:=K) (V:=V))
    (m : RankMask (K:=K) (V:=V)) (hm : m.2=.popular) :
    (((projectiveCheapDomain W m).image Prod.fst).card:ℝ) ≤ 32*(Nat.card K:ℝ)^m.1.val := by
  unfold projectiveCheapDomain
  split_ifs
  · rw [hm]
    exact popularJoint_first_card W _ _ (levelFromRank_spec W m.1.val).1
      ((levelFromRank_spec W m.1.val).2 _ le_rfl)
  · simp

lemma cheapPopular_fiber_card {d : ℕ} (hdim : Module.finrank K V=d+1)
    (W : State (K:=K) (V:=V)) (m : RankMask (K:=K) (V:=V)) (hm : m.2=.popular)
    (b : Projectivization K V) :
    (((projectiveCheapDomain W m).filter (fun f => f.1=b)).card:ℝ) ≤
      2*(Nat.card K:ℝ)^(d-m.1.val) := by
  unfold projectiveCheapDomain
  split_ifs with hr
  · rw [hm]
    exact popularJoint_fiber_card hdim W _ (by omega) b
  · simp

lemma cheapPopular_rank_pos (W : State (K:=K) (V:=V))
    (m : RankMask (K:=K) (V:=V)) (hm : m.2=.popular)
    (h : (projectiveCheapDomain W m).Nonempty) :
    1 ≤ m.1.val ∧ m.1.val < Module.finrank K V := by
  unfold projectiveCheapDomain at h
  split_ifs at h with hr
  · rw [hm] at h
    exact ⟨popularJoint_rank_pos (levelFromRank_spec W m.1.val).1
      ((levelFromRank_spec W m.1.val).2 _ le_rfl) h,hr⟩
  · exact False.elim (not_nonempty_empty h)

lemma cheapPoor_product {n : ℕ} (hdim : Module.finrank K V=n+3)
    (W : State (K:=K) (V:=V)) (m : RankMask (K:=K) (V:=V)) (hm : m.2=.poor) :
    (((projectiveCheapDomain W m).image Prod.fst).card:ℝ)*
      ((projectiveCheapDomain W m).image Prod.snd).card ≤ 16*(Nat.card K:ℝ)^(n+3) := by
  unfold projectiveCheapDomain
  split_ifs
  · rw [hm]
    have h₁ : (incidentPairs (level (ranks W) m.1.val)
        (poorDomain W (levelFromRank W m.1.val))).image Prod.fst ⊆ level (ranks W) m.1.val := by
      intro b hb
      obtain ⟨f,hf,rfl⟩ := mem_image.mp hb
      exact (mem_product.mp (mem_filter.mp hf).1).1
    have h₂ : (incidentPairs (level (ranks W) m.1.val)
        (poorDomain W (levelFromRank W m.1.val))).image Prod.snd ⊆
        poorDomain W (levelFromRank W m.1.val) := by
      intro a ha
      obtain ⟨f,hf,rfl⟩ := mem_image.mp ha
      exact (mem_product.mp (mem_filter.mp hf).1).2
    have h₁' : (((incidentPairs (level (ranks W) m.1.val)
        (poorDomain W (levelFromRank W m.1.val))).image Prod.fst).card:ℝ) ≤
        (level (ranks W) (levelFromRank W m.1.val)).card := by
      exact_mod_cast (card_le_card h₁).trans ((levelFromRank_spec W m.1.val).2 _ le_rfl)
    have h₂' : (((incidentPairs (level (ranks W) m.1.val)
        (poorDomain W (levelFromRank W m.1.val))).image Prod.snd).card:ℝ) ≤
        (poorDomain W (levelFromRank W m.1.val)).card := by exact_mod_cast card_le_card h₂
    exact (mul_le_mul h₁' h₂' (by positivity) (by positivity)).trans (poor_marginal_product hdim W _)
  · simp

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingTwoCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
open Finset ProjectiveDuality
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def twoDomain (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V)) :
    Finset (ProjectivePair (K:=K) (V:=V)) :=
  projectiveCheapDomain W m ∩ (projectiveCheapDomain W' m').map pairDuality.symm.toEmbedding

omit [Finite K] in
lemma twoDomain_forward (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V)) :
    twoDomain W W' m m' ⊆ projectiveCheapDomain W m := inter_subset_left

omit [Finite K] in
lemma twoDomain_reverse (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V)) :
    (twoDomain W W' m m').map pairDuality.toEmbedding ⊆ projectiveCheapDomain W' m' := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
  obtain ⟨h,h',he⟩ := mem_map.mp (mem_inter.mp hg).2
  have he' : pairDuality g=h := by rw [←he]; exact pairDuality.apply_symm_apply h
  simpa only [Equiv.coe_toEmbedding,he'] using h'

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma shadow_reverse_first (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (D.map pairDuality.toEmbedding).image Prod.fst = D.image Prod.snd := by
  ext a
  simp only [mem_image,mem_map]
  constructor
  · rintro ⟨f,⟨g,hg,hgf⟩,he⟩
    subst f
    exact ⟨g,hg,he⟩
  · rintro ⟨g,hg,rfl⟩
    exact ⟨pairDuality g,⟨g,hg,rfl⟩,rfl⟩

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma shadow_reverse_second_card (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    ((D.map pairDuality.toEmbedding).image Prod.snd).card = (D.image Prod.fst).card := by
  have he : (D.map pairDuality.toEmbedding).image Prod.snd =
      (D.image Prod.fst).map bidual.toEmbedding := by
    ext b
    simp only [mem_image,mem_map]
    constructor
    · rintro ⟨f,⟨g,hg,hgf⟩,he⟩
      subst f
      exact ⟨g.1,⟨g,hg,rfl⟩,he⟩
    · rintro ⟨a,⟨g,hg,hga⟩,he⟩
      subst a
      refine ⟨pairDuality g,⟨g,hg,rfl⟩,he⟩
  rw [he,card_map]

theorem twoPopular_caps {d : ℕ} (hdim : Module.finrank K V=d+1)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (hm : m.2=.popular) (hm' : m'.2=.popular) :
    let D := twoDomain W W' m m'
    ((D.image Prod.fst).card:ℝ) ≤ 32*(Nat.card K:ℝ)^m.1.val ∧
    ((D.image Prod.snd).card:ℝ) ≤ 32*(Nat.card K:ℝ)^m'.1.val ∧
    (∀ b,((D.filter (fun f => f.1=b)).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-m.1.val)) ∧
    (∀ a,((D.filter (fun f => f.2=a)).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-m'.1.val)) := by
  dsimp only
  have hd' : Module.finrank K (Module.Dual K V)=d+1 := by rwa [Subspace.dual_finrank_eq]
  refine ⟨?_,?_,?_,?_⟩
  · exact (show (((twoDomain W W' m m').image Prod.fst).card:ℝ) ≤
      ((projectiveCheapDomain W m).image Prod.fst).card by
        exact_mod_cast card_le_card (image_subset_image (twoDomain_forward W W' m m'))).trans
      (cheapPopular_first_card W m hm)
  · rw [←shadow_reverse_first]
    exact (show ((((twoDomain W W' m m').map pairDuality.toEmbedding).image Prod.fst).card:ℝ) ≤
      ((projectiveCheapDomain W' m').image Prod.fst).card by
        exact_mod_cast card_le_card (image_subset_image (twoDomain_reverse W W' m m'))).trans
      (cheapPopular_first_card W' m' hm')
  · intro b
    exact (show (((twoDomain W W' m m').filter (fun f => f.1=b)).card:ℝ) ≤
      ((projectiveCheapDomain W m).filter (fun f => f.1=b)).card by
        exact_mod_cast card_le_card (filter_subset_filter _ (twoDomain_forward W W' m m'))).trans
      (cheapPopular_fiber_card hdim W m hm b)
  · intro a
    have hsub : ((twoDomain W W' m m').filter (fun f => f.2=a)).map pairDuality.toEmbedding ⊆
        (projectiveCheapDomain W' m').filter (fun f => f.1=a) := by
      intro f hf
      obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
      obtain ⟨hg,hga⟩ := mem_filter.mp hg
      exact mem_filter.mpr ⟨twoDomain_reverse W W' m m' (mem_map.mpr ⟨g,hg,rfl⟩),hga⟩
    have hc := card_le_card hsub
    rw [card_map] at hc
    exact (show (((twoDomain W W' m m').filter (fun f => f.2=a)).card:ℝ) ≤
      ((projectiveCheapDomain W' m').filter (fun f => f.1=a)).card by exact_mod_cast hc).trans
      (cheapPopular_fiber_card hd' W' m' hm' a)

theorem twoPoor_product {n : ℕ} (hdim : Module.finrank K V=n+3)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (hm : m.2=.poor ∨ m'.2=.poor) :
    (((twoDomain W W' m m').image Prod.fst).card:ℝ)*
    ((twoDomain W W' m m').image Prod.snd).card ≤ 16*(Nat.card K:ℝ)^(n+3) := by
  have hf : (((twoDomain W W' m m').image Prod.fst).card:ℝ) ≤
      ((projectiveCheapDomain W m).image Prod.fst).card := by
    exact_mod_cast card_le_card (image_subset_image (twoDomain_forward W W' m m'))
  have hs : (((twoDomain W W' m m').image Prod.snd).card:ℝ) ≤
      ((projectiveCheapDomain W m).image Prod.snd).card := by
    exact_mod_cast card_le_card (image_subset_image (twoDomain_forward W W' m m'))
  rcases hm with hm|hm
  · exact (mul_le_mul hf hs (by positivity) (by positivity)).trans (cheapPoor_product hdim W m hm)
  · have hd' : Module.finrank K (Module.Dual K V)=n+3 := by rwa [Subspace.dual_finrank_eq]
    have hf' : ((((twoDomain W W' m m').map pairDuality.toEmbedding).image Prod.fst).card:ℝ) ≤
      ((projectiveCheapDomain W' m').image Prod.fst).card := by
      exact_mod_cast card_le_card (image_subset_image (twoDomain_reverse W W' m m'))
    have hs' : ((((twoDomain W W' m m').map pairDuality.toEmbedding).image Prod.snd).card:ℝ) ≤
      ((projectiveCheapDomain W' m').image Prod.snd).card := by
      exact_mod_cast card_le_card (image_subset_image (twoDomain_reverse W W' m m'))
    rw [shadow_reverse_first] at hf'
    rw [shadow_reverse_second_card] at hs'
    rw [mul_comm]
    exact (mul_le_mul hf' hs' (by positivity) (by positivity)).trans (cheapPoor_product hd' W' m' hm)

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma nonempty_cheap_not_expensive (W : State (K:=K) (V:=V))
    (m : RankMask (K:=K) (V:=V)) (h : (projectiveCheapDomain W m).Nonempty) : m.2≠.expensive := by
  intro hm
  unfold projectiveCheapDomain at h
  split_ifs at h
  · rw [hm] at h
    exact not_nonempty_empty h
  · exact not_nonempty_empty h

theorem twoDomain_cases {d : ℕ} (hdim : Module.finrank K V=d+1)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (h : (twoDomain W W' m m').Nonempty) :
    m.2=.poor ∨ m'.2=.poor ∨
      (m.2=.popular ∧ m'.2=.popular ∧ 1 ≤ m.1.val ∧ m.1.val≤d ∧ 1 ≤ m'.1.val ∧ m'.1.val≤d) := by
  have hf : (projectiveCheapDomain W m).Nonempty := h.mono (twoDomain_forward W W' m m')
  have hr : (projectiveCheapDomain W' m').Nonempty :=
    (h.map (f:=pairDuality.toEmbedding)).mono (twoDomain_reverse W W' m m')
  have hf' := nonempty_cheap_not_expensive W m hf
  have hr' := nonempty_cheap_not_expensive W' m' hr
  by_cases hp : m.2=.poor
  · exact Or.inl hp
  by_cases hp' : m'.2=.poor
  · exact Or.inr (Or.inl hp')
  have hpop : m.2=.popular := by cases h : m.2 <;> simp_all
  have hpop' : m'.2=.popular := by cases h : m'.2 <;> simp_all
  have h₁ := cheapPopular_rank_pos W m hpop hf
  have h₂ := cheapPopular_rank_pos W' m' hpop' hr
  have h₁' : m.1.val < d+1 := lt_of_lt_of_eq h₁.2 hdim
  have h₂' : m'.1.val < d+1 := lt_of_lt_of_eq h₂.2 (Subspace.dual_finrank_eq.trans hdim)
  exact Or.inr (Or.inr ⟨hpop,hpop',h₁.1,by omega,h₂.1,by omega⟩)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReciprocalBands
open Real
noncomputable section

theorem cover {d : ℕ} {σ K u : ℝ} (hσ : 0<σ) (hK : 0≤K)
    (hlo : σ≤u) (hhi : u≤(d:ℝ)*σ) :
    ∃ r : ℕ,1 ≤ r ∧ r≤d ∧ (IntegerBand r σ K u ∨ (2 ≤ r ∧ OpenBand r σ K u)) := by
  induction d with
  | zero => simp only [Nat.cast_zero,zero_mul] at hhi; linarith
  | succ d ih =>
    by_cases hprev : u≤(d:ℝ)*σ
    · obtain ⟨r,h₁,h₂,h₃⟩ := ih hprev
      exact ⟨r,h₁,h₂.trans (Nat.le_succ d),h₃⟩
    have hhi' : u≤((d:ℝ)+1)*σ := by simpa only [Nat.cast_add,Nat.cast_one] using hhi
    by_cases hnext : ((d:ℝ)+1)*σ-K≤u
    · refine ⟨d+1,by omega,le_rfl,Or.inl ?_⟩
      rw [IntegerBand,abs_le]
      simp only [Nat.cast_add,Nat.cast_one]
      constructor <;> linarith
    have hd : 1≤d := by
      by_contra hn
      have hz : d=0 := by omega
      simp only [hz,Nat.cast_zero,zero_add,one_mul] at hnext
      linarith
    by_cases hleft : u≤(d:ℝ)*σ+K
    · refine ⟨d,hd,by omega,Or.inl ?_⟩
      rw [IntegerBand,abs_le]
      constructor <;> linarith
    · refine ⟨d+1,by omega,le_rfl,Or.inr ⟨by omega,?_⟩⟩
      unfold OpenBand
      simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
      exact ⟨lt_of_not_ge hleft,lt_of_not_ge hnext⟩

end
end SharpLogRamsey.ReciprocalBands

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

theorem twoDomain_low_or_high {n : ℕ} (hdim : Module.finrank K V=n+3)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (h : (twoDomain W W' m m').Nonempty) :
    (((twoDomain W W' m m').image Prod.fst).card:ℝ)*
      ((twoDomain W W' m m').image Prod.snd).card ≤ 1024*(Nat.card K:ℝ)^(n+3) ∨
    (m.2=.popular ∧ m'.2=.popular ∧ 1 ≤ m.1.val ∧ m.1.val≤n+2 ∧
      1 ≤ m'.1.val ∧ m'.1.val≤n+2 ∧ n+3 < m.1.val+m'.1.val) := by
  have hdim' : Module.finrank K V=(n+2)+1 := by omega
  obtain hp|hp|⟨hp,hp',hr,hr',hs,hs'⟩ := twoDomain_cases hdim' W W' m m' h
  · left
    exact (twoPoor_product hdim W W' m m' (Or.inl hp)).trans (mul_le_mul_of_nonneg_right (by norm_num : (16:ℝ)≤1024) (by positivity))
  · left
    exact (twoPoor_product hdim W W' m m' (Or.inr hp)).trans (mul_le_mul_of_nonneg_right (by norm_num : (16:ℝ)≤1024) (by positivity))
  by_cases hsum : m.1.val+m'.1.val≤n+3
  · left
    obtain ⟨ha,hb,-,-⟩ := twoPopular_caps hdim' W W' m m' hp hp'
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le
    calc
      _ ≤ (32*(Nat.card K:ℝ)^m.1.val)*(32*(Nat.card K:ℝ)^m'.1.val) :=
        mul_le_mul ha hb (by positivity) (by positivity)
      _ = 1024*(Nat.card K:ℝ)^(m.1.val+m'.1.val) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hsum) (by norm_num)
  · exact Or.inr ⟨hp,hp',hr,hr',hs,hs',by omega⟩

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in

theorem twoDomain_reciprocal_caps {d : ℕ} (hd : 1≤d)
    (hdim : Module.finrank K V=d+1)
    (D : Finset (ProjectivePair (K:=K) (V:=V))) (hD : D.Nonempty)
    (hp : ((D.image Prod.fst).card:ℝ)*(D.image Prod.snd).card≤
      1024*(Nat.card K:ℝ)^(d+1)) :
    let σ := Real.log (Nat.card K:ℝ)
    let u := ReciprocalBands.clamp d σ (Real.log (D.image Prod.snd).card)
    σ≤u ∧ u≤(d:ℝ)*σ ∧
      ((D.image Prod.fst).card:ℝ)≤1024*Real.exp (((d:ℝ)+1)*σ-u) ∧
      ((D.image Prod.snd).card:ℝ)≤1024*Real.exp u := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le
  have hdim' : Module.finrank K (Module.Dual K V)=d+1 := by
    rwa [Subspace.dual_finrank_eq]
  have ha := ambient_point_bound hdim (D.image Prod.fst)
  have hb := ambient_point_bound hdim' (D.image Prod.snd)
  have hbp : (0:ℝ)<(D.image Prod.snd).card := by
    exact_mod_cast card_pos.mpr (hD.image Prod.snd)
  apply ReciprocalBands.clamped_caps hd (Real.log_nonneg hq1) hbp (by norm_num)
  · rw [exp_nat_log hq]
    exact ha.trans (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤1024) (by positivity))
  · rw [exp_nat_log hq]
    exact hb.trans (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤1024) (by positivity))
  · convert hp using 1
    all_goals try with_reducible_and_instances rfl
    rw [←Nat.cast_add_one,exp_nat_log hq]

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingFiniteClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset ReciprocalBands
open scoped Classical
noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

theorem exists_valid_slot_class {n : ℕ} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (h : (twoDomain W W' m m').Nonempty) :
    ∃ c : SlotClass (n+2),ValidSlotClass (n+2) gap (twoDomain W W' m m') c := by
  obtain hlow|⟨hm,hm',hr,hr',hs,hs',hsum⟩ := twoDomain_low_or_high hdim W W' m m' h
  · have hd : Module.finrank K V=(n+2)+1 := by omega
    obtain ⟨hu,hu',ha,hb⟩ := twoDomain_reciprocal_caps (by omega : 1≤n+2) hd _ h hlow
    have hq : (1:ℝ)<Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K)
    obtain ⟨r,hr,hr',hband⟩ := ReciprocalBands.cover (Real.log_pos hq) hgap hu hu'
    rcases hband with hi|ho
    · refine ⟨.inl (true,⟨r,by omega⟩),_,hu,hu',ha,hb,hr,?_⟩
      exact hi
    · refine ⟨.inl (false,⟨r,by omega⟩),_,hu,hu',ha,hb,hr,?_⟩
      exact ho
  · have hd : Module.finrank K V=(n+2)+1 := by omega
    obtain ⟨ha,hb,ha',hb'⟩ := twoPopular_caps hd W W' m m' hm hm'
    exact ⟨.inr (⟨m.1.val,by omega⟩,⟨m'.1.val,by omega⟩),hr,hs,by omega,ha,hb,ha',hb'⟩

theorem cheapBoth_valid_slot_class {n N : ℕ} {Γ : Type*}
    (hdim : Module.finrank K V=n+3) {gap : ℝ} (hgap : 0≤gap)
    (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N)
    (h : (cheapBoth z i).Nonempty) :
    ∃ c : SlotClass (n+2),ValidSlotClass (n+2) gap (cheapBoth z i) c := by
  unfold cheapBoth cheapTuple at h ⊢
  exact exists_valid_slot_class hdim hgap _ _ _ _ h

def messageClass {n N : ℕ} {Γ : Type*} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap) (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N) :
    SlotClass (n+2) :=
  if h : (cheapBoth z i).Nonempty then
    (cheapBoth_valid_slot_class hdim hgap z i h).choose
  else .inl (false,0)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_SupportMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.SupportMixtures
noncomputable section
variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

 def mixture (w : I→ℝ) (S : I→Finset A) (a : A) : ℝ :=
  ∑ i, w i*kernel (S i) a

end
end SharpLogRamsey.SupportMixtures

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma quotient_rep_ne_zero (z p : Projectivization K V) (hp : p ≠ z) :
    z.submodule.mkQ p.rep ≠ 0 := by
  intro h
  have hm : p.rep ∈ LinearMap.ker z.submodule.mkQ := h
  rw [Submodule.ker_mkQ] at hm
  exact hp ((rep_mem_line_iff p z).mp hm)

def project (z : Projectivization K V) (p : {p : Projectivization K V // p ≠ z}) :
    Projectivization K (V ⧸ z.submodule) :=
  Projectivization.mk K (z.submodule.mkQ p.val.rep) (quotient_rep_ne_zero z p.val p.property)

lemma lift_covector_ne_zero (z : Projectivization K V)
    (t : Projectivization K (Module.Dual K V)) (ht : SharpLogRamsey.Incidence.Incident z t) :
    z.submodule.liftQ t.rep ((_root_.OAI.SharpLogRamsey.Incidence.incident_iff_submodule z t).mp ht) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : Module.Dual K (V ⧸ z.submodule) => f.comp z.submodule.mkQ) h
  rw [Submodule.liftQ_mkQ] at hc
  exact t.rep_nonzero hc

def projectDual (z : Projectivization K V)
    (t : {t : Projectivization K (Module.Dual K V) // SharpLogRamsey.Incidence.Incident z t}) :
    Projectivization K (Module.Dual K (V ⧸ z.submodule)) :=
  Projectivization.mk K (z.submodule.liftQ t.val.rep
    ((_root_.OAI.SharpLogRamsey.Incidence.incident_iff_submodule z t.val).mp t.property)) (lift_covector_ne_zero z t.val t.property)

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def Collides (z p q : Projectivization K V) : Prop := ∃ (hp : p ≠ z) (hq : q ≠ z),
    project z ⟨p,hp⟩ = project z ⟨q,hq⟩

def orderedCollisions (A : Finset (Projectivization K V)) (z : Projectivization K V) : ℕ :=
  (A.offDiag.filter (fun pq => Collides z pq.1 pq.2)).card

end
end SharpLogRamsey.Projection

namespace SharpLogRamsey.Projection
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def projected (A : Finset (Projectivization K V)) (z : Projectivization K V) :
    Finset (Projectivization K (V ⧸ z.submodule)) :=
  (A.subtype (· ≠ z)).image (project z)

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.Projection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def liftCap (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) : Finset (Projectivization K V) :=
  (((A.subtype (· ≠ z)).filter (fun p => project z p ∈ W)).image Subtype.val)

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ExternalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)

variable (color : V → C) (s : V → Finset D) (b : ℝ) (own : V → Fin R → Bool)

noncomputable def inside (c : C) (S : Finset D) : Finset (IntDir label c) :=
  Finset.univ.filter (fun d => d.val ∈ S)

noncomputable def unblock (c : C) (x : Block label R (some c) → ℕ) :
    Fin R → IntDir label c → ℕ := fun r d => x ⟨(r,d), d.property⟩

noncomputable def blockCoords (c : C) : (Fin R × IntDir label c) ≃ Block label R (some c) where
  toFun i := ⟨(i.1,i.2), i.2.property⟩
  invFun i := (i.1.1, ⟨i.1.2, i.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def unblockEquiv (c : C) :
    (Block label R (some c) → ℕ) ≃ᵐ (Fin R → IntDir label c → ℕ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Block label R (some c) => ℕ)
    (blockCoords label R c)).symm.trans (MeasurableEquiv.curry (Fin R) (IntDir label c) ℕ)

omit [Fintype D] [DecidableEq D] [Fintype C] [DecidableEq C] in
@[simp] lemma unblockEquiv_apply (c : C) (x : Block label R (some c) → ℕ) :
    unblockEquiv label R c x = unblock label R c x := rfl

end SharpRamseyFive.TupleComponents
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TruncatedTupleIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open Classical
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]
variable (R : ℕ) (s : H → Finset D) (b : ℝ) (own : H → Fin R → Bool)

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def absSplit (f : V → H) (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ) : ℝ := by
  let sf := s ∘ f
  let G := strongGraph weight sf t
  let label := componentLabel weight sf t
  exact ∫ z, blockTrunc label R J none z * ∏ c : G.ConnectedComponent,
    |∫ x, componentFactor label R G.connectedComponentMk sf b (own ∘ f) J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)|
      ∂batchMeasure (fun i : Block label R none => rate i.1.2)

end SharpRamseyFive.HighMoment

namespace SharpRamseyFive.AmbientDesignations
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations
open Classical
variable {D V : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)

variable (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (own : V → Fin R → Bool)

noncomputable def extraWeight (c : Components weight s t) : ℝ :=
  |delta weight s base (vertex weight s t c)| ^ (R / 2) +
    alpha weight s t (vertex weight s t c) ^ K +
    (if R < J then 0 else
      ∑ d ∈ inside (componentLabel weight s t) c (s (vertex weight s t c)),
        ((R : ℝ) * ((L * weight d : ℝ≥0) : ℝ)) ^ J)

noncomputable def isBad (c : Components weight s t)
    (z : Block (componentLabel weight s t) R none → ℕ) : Prop :=
  BAD (touched (componentLabel weight s t) R c (s (vertex weight s t c)) z)

noncomputable def componentAbs (c : Components weight s t)
    (z : Block (componentLabel weight s t) R none → ℕ) : ℝ :=
  |∫ x, componentFactor (componentLabel weight s t) R
      (strongGraph weight s t).connectedComponentMk s (Real.exp (-(L : ℝ) * base)) own J c z x
    ∂batchMeasure (fun i : Block (componentLabel weight s t) R (some c) => L * weight i.1.2)|

noncomputable def designatedBound : ℝ :=
  let S := simpleSet weight s t
  (Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) ^ S.card *
    Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) ^
      (Fintype.card (Components weight s t) - S.card)) *
    ∑ U ∈ S.powerset, (∏ c ∈ S \ U, extraWeight weight s t R J K L base c) *
      badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => L * weight i.1.2))
        (blockTrunc (componentLabel weight s t) R J none) (isBad weight s t R) U

end SharpRamseyFive.AmbientDesignations

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_CompleteProgramWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H C : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]

noncomputable def vertexBadMass (weight rate : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    (R J : ℕ) (A : Finset V) : ℝ :=
  badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => rate i.1.2))
    (blockTrunc (componentLabel weight s t) R J none)
    (fun v z => BAD (touched (componentLabel weight s t) R
      ((strongGraph weight s t).connectedComponentMk v) (s v) z)) A

end SharpRamseyFive.SelectionBridge

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_LargeCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.AmbientEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
open SharpRamseyFive.WeightedPrograms
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def vertexExpansion (weight : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (E : Finset V) (f : V → H) : ℝ :=
  badExpansion
    (fun u f => independentWeight weight (fun d => L * weight d) lines R J base (f u) +
      alpha weight (lines ∘ f) t u ^ K)
    (fun A f => vertexBadMass weight (fun d => L * weight d) (lines ∘ f) t R J A) E f

end SharpRamseyFive.AmbientEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScaleComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

def scaleK (σ η D : ℝ) : ℝ := D*σ^(3*beta η)

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestActualRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory LearningRow
open scoped BigOperators Classical NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedRow.flat_JoinedTestActualRow_2
attribute [local instance] OAI.SharpLogRamsey.PreparedRow.flat_JoinedTestActualRow_3
def rowTest (S : Finset (Projectivization K V)) (O : Projectivization K V→Finset (Projectivization K V))
    (E : Finset (Projectivization K (Module.Dual K V))) (b : Projectivization K V→ℝ)
    {R : ℕ} (ω : Schedule S R) : Finset (Projectivization K V) :=
  test (sample S ω) (fun x => score S (O x) (pencil x) inc (b x) ω)
    (emptySet S E inc ω).card (Nat.card K)

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.PreparedDecoder
open Finset SharpLogRamsey.PreparedRow SharpLogRamsey.PointScore
open SharpLogRamsey.GreedyPreparation
open scoped Classical BigOperators
noncomputable section
variable {A H B : Type*} [Fintype A] [Fintype H]

def decode (U : B → Finset A) (bs : List (B×ℕ)) (N z : ℕ)
    (T : A → Finset H) (inc : H → A → Prop) (L q : ℝ)
    {R : ℕ} (ω : Fin R×A → ℕ) : Finset A :=
  LearningRow.test (publicSample ω)
    (fun x => publicScore (fun y => y∈own univ U (bs.map Prod.fst) x)
      (T x) inc (Real.exp (-L*(1-(publicSize U bs x:ℝ)/(N:ℝ)))) ω) z q

end
end SharpLogRamsey.PreparedDecoder

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedProposals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.PublicTables
open MeasureTheory Finset
open scoped Classical BigOperators
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [Fintype Y]

def Law.fromMeasure (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y)
    (hf : ∀ y,MeasurableSet (f ⁻¹' {y})) : Law Y where
  mass y := μ.real (f ⁻¹' {y})
  nonneg _ := measureReal_nonneg
  total := by
    have h := sum_measureReal_preimage_singleton (μ:=μ) univ (fun y _ => hf y)
    simpa using h

end
end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.PreparedProposals
open MeasureTheory ProbabilityTheory Finset
open SharpLogRamsey.PoissonLikelihood SharpLogRamsey.FiniteSchedules SharpLogRamsey.PublicTables
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

def accepts (S : Finset ι) (M : ℕ) (P : (ι → ℕ) → Prop)
    (z : ι → Fin (M+2)) : Prop :=
  total (fun i => (z i:ℕ))≤M ∧ (∀ i,i∉S → (z i:ℕ)=0) ∧ P (fun i => (z i:ℕ))

def proposal (U : Finset ι) (a : ℝ≥0) (M : ℕ) : Law (ι → Fin (M+2)) :=
  Law.fromMeasure (law (uniformRate U a)) (clip M)
    (fun _ => (Set.to_countable _).measurableSet)

end
end SharpLogRamsey.PreparedProposals

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedDescription
open Finset MeasureTheory PreparedRow GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I B : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPreparedDescription_1_ra0f3f4_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PreparedDescription.flat_JoinedPreparedDescription_3
attribute [local instance] OAI.SharpLogRamsey.PreparedDescription.flat_JoinedPreparedDescription_4
def good (S : Finset (Projectivization K V))
    (plane : B→Finset (Projectivization K V)) (bs : List (B×ℕ)) (L cap size : ℝ)
    {R : ℕ} (ω : Fin R×Projectivization K V→ℕ) : Prop :=
  ∃ z≤Fintype.card (Projectivization K (Module.Dual K V)),
    let W := PreparedDecoder.decode plane bs S.card z pencil inc L (Nat.card K) ω
    cap≤(S∩W).card ∧ (W.card:ℝ)≤ size

end
end SharpLogRamsey.PreparedDescription

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_UniversalTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def rows : (n : ℕ) → Table Ω n → Finset Ω
  | 0, _ => ∅
  | n+1, z => insert z.1 (rows n z.2)

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_ValidationCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def CoverInput (W : Finset (Projectivization K V))
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ) (C b : ℝ)
    (z : Finset (Projectivization K V) × Finset (Projectivization K (Module.Dual K V))) : Prop :=
  z.1.Nonempty ∧ z.1 ⊆ W ∧ (N:ℝ) ≤ C*z.1.card ∧
  (W.card:ℝ) ≤ exp b*z.1.card ∧ z.2 ⊆ U ∧ z.2.card=t ∧
  (incidenceCount z.1 z.2:ℝ) ≤ (z.1.card:ℝ)*z.2.card/(10000*Nat.card K)

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_RawLowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.ProjectiveDuality
open SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Finite K]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
local instance flat_JoinedHighRankAssembly_5 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) :=
  Fintype.ofEquiv _ (bidual (K := K) (V := V))

end
end SharpLogRamsey.ProjectiveDuality

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

def highGoodFirst (p : Law (A×B)) (M L κ U : ℝ) (a : A) : Prop :=
  goodFirst p M L κ (1/50) a ∧ p.fst.mass a≤U

def highGoodSecond (p : Law (A×B)) (M L κ U : ℝ) (b : B) : Prop :=
  goodSecond p M L κ (1/50) b ∧ p.snd.mass b≤U

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionCenterTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence SharpLogRamsey.ProjectiveDuality Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cut (T : Finset (Projectivization K (Module.Dual K V))) (z : Projectivization K V) :
    Finset (Projectivization K (Module.Dual K V)) := T.filter (SharpLogRamsey.Incidence.Incident z)

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

local instance flat_JoinedProjectionCenterTools_1 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) :=
  Fintype.ofEquiv _ (bidual (K:=K) (V:=V))

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_QuotientSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def quotientCut (T : Finset (Projectivization K (Module.Dual K V)))
    (z : Projectivization K V) : Finset (Projectivization K (Module.Dual K (V ⧸ z.submodule))) :=
  (T.subtype (SharpLogRamsey.Incidence.Incident z)).image (projectDual z)

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Real Incidence CapComposition
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.Projection.flat_JoinedProjectionPublic_1
local instance flat_JoinedProjectionPublic_3_ra0f3f4_1 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
def liftedLibrary (U : Finset (Projectivization K V))
    (F : ∀ z : Projectivization K V, Finset (Finset (Projectivization K (V ⧸ z.submodule)))) :
    Finset (Finset (Projectivization K V)) :=
  univ.biUnion (fun z => (F z).image (liftCap U z))

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical PreparedVariance RegularPencils GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedGeometry.flat_JoinedPreparedGeometry_2
local instance flat_JoinedPreparedGeometry_3_ra0f3f4_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
def badHyperplanes (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0) :
    Finset (Projectivization K (Module.Dual K V)) :=
  exceptional (mass S c) (fun i : Fin bs.length => mass (indexedCell S U bs i) c)
    (fun i => ((indexedCell S U bs i).card:ℝ)/(S.card:ℝ))

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_TotalDegreeCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid

namespace SharpLogRamsey.NonplaneCertificate
open MvPolynomial FlatnessCore
variable {K : Type*} [Field K]
noncomputable section

noncomputable def flatFamily (G : MvPolynomial (Fin 3) K) (i : Index) :
    MvPolynomial (Fin 3) K :=
  renameEquiv K i.1 (flatnessPolynomial ((renameEquiv K i.1).symm G) i.2.1 i.2.2)

end
end SharpLogRamsey.NonplaneCertificate

open scoped BigOperators
open Finset MvPolynomial
end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real PreparedRow GreedyPreparation PreparedProjectiveGeometry SpatialLearning
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedSpatialPublic_1_ra0f3f4_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
def Input (U : Finset (Projectivization K V)) (N : ℕ)
    (plane : J→Finset (Projectivization K V)) (bs : List (J×ℕ))
    (σ P g b τ : ℝ) (c : ℝ≥0) (p : ℕ) (S : Finset (Projectivization K V)) : Prop :=
  S⊆U ∧ S.card=N ∧ (S.card:ℝ)≤exp (3*σ/2+g) ∧
    sized S plane (bs.map Prod.fst)=bs ∧
    (∀ i : Fin (bs.map Prod.fst).length,
      ((indexedCell S plane (bs.map Prod.fst) i).card:ℝ)/(S.card:ℝ)≤1/25) ∧
    (∃ T : Finset (Projectivization K (Module.Dual K V)),
      T.Nonempty ∧ S.card≤T.card ∧
      (Nat.card K:ℝ)^4*exp (-b)≤(S.card:ℝ)*T.card ∧
      (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K) ∧
    ∃ D₀ D₁ : Finset (Projectivization K V),
      (D₀.card:ℝ)≤S.card*exp (-P/200) ∧ (D₁.card:ℝ)≤S.card*exp (5*P) ∧
      (∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S.card+2),
        ((richRadials (S\(own S plane (bs.map Prod.fst) x∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
          (DyadicGrid.value i)^100≤exp (σ+P/100-2*g)) ∧
      (∀ x,x∉D₁ → (richRadials (S\(own S plane (bs.map Prod.fst) x∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
        2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P))

attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialPublic_3
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialPublic_4
def decode (U : Finset (Projectivization K V)) (N : ℕ) (L : ℝ)
    (plane : J→Finset (Projectivization K V)) (bs : List (J×ℕ))
    {R M : ℕ} (ω : (Fin R×Projectivization K V)→Fin (M+2))
    (z : Fin (Fintype.card (Projectivization K (Module.Dual K V))+1)) :
    Finset (Projectivization K V) :=
  U∩PreparedDecoder.decode plane bs N z pencil inc L (Nat.card K)
    (fun x => (ω x:ℕ))

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPlanarPublic_1_ra0f3f4_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
def Input (U : Finset (Projectivization K V)) (N : ℕ) (b τ : ℝ)
    (S : Finset (Projectivization K V)) : Prop :=
  S⊆U ∧ S.card=N ∧ ∃ T : Finset (Projectivization K (Module.Dual K V)),
    T.Nonempty ∧ S.card≤T.card ∧
    (Nat.card K:ℝ)^3*exp (-b)≤(S.card:ℝ)*T.card ∧
    (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K

attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarPublic_3
attribute [local instance] OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarPublic_4
def decode (U : Finset (Projectivization K V)) (N : ℕ) (L : ℝ)
    {R M : ℕ} (ω : (Fin R×Projectivization K V)→Fin (M+2))
    (z : Fin (Fintype.card (Projectivization K (Module.Dual K V))+1)) :
    Finset (Projectivization K V) :=
  U∩PreparedDecoder.decode (fun _ : Unit => ∅) [] N z pencil inc L (Nat.card K)
    (fun x => (ω x:ℕ))

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_GeometricInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Filter SourceScales Incidence ProjectiveDuality Validation Projection
open scoped Classical Topology
noncomputable section

def Description {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (q P J : ℝ) (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ) (τ : ℝ) : Prop :=
  ∃ F : Finset (Finset (Projectivization K V)),
    (∀ W∈F,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
    (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
      (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
      ∃ W∈F,(n:ℝ)/100≤(S∩W).card) ∧
    log ((F.card:ℝ)+1)≤J*q*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreeDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeDecoder
open BinaryTree List
open scoped Classical
noncomputable section
variable {A B I C : Type*}

def decode (R : A → B → Prop) (read : CapReader A B C) :
    BinaryTree (C×ℕ) → Domains A B → List (Finset (A×B))
  | .nil, _ => []
  | .node (c,n) l r, U =>
    let V := read U c
    decode R read l (V.1,U.2) ++ List.replicate n (flagDomain R V) ++
      decode R read r (U.1,V.2)

end
end SharpLogRamsey.TreeDecoder

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_FreshFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι→Type*} [∀ i,Fintype (α i)]

def outside (i : ι) (z : ∀ j,α j) : Outside (α:=α) i := fun j=>z j

def outsideLaw (p : ∀ i,Law (α i)) (i : ι) : Law (Outside (α:=α) i) :=
  piLaw (ι := {j : ι // j≠i}) (α := fun j=>α j.1) (fun j=>p j.1)

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_ReadyTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation SupportMixtures Selection
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def Call.loss {S : Finset (Projectivization K V)} (c : Call S) (n : ℕ)
    (y : Projectivization K (Module.Dual K V)) : ℝ :=
  let q : ℝ := Nat.card K
  let h := scheduleLength q c.domain.card c.target.card
  let m := scheduleCutoff q c.overhead h
  PublicTables.integral (rowLaw c.proposal (c.source_nonempty.mono c.source_proposal) h)
    (implementAccept c.source
      (GoodCap SharpLogRamsey.Incidence.Incident q c.domain c.target (2000*q^(n+3)/S.card)))
    (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m

end
end SharpLogRamsey.ReadyTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation Selection PivotGeometry GeometricCover ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def Call.production {S : Finset (Projectivization K V)} (c : Call S) (n : ℕ) : ℝ :=
  let q : ℝ := Nat.card K
  let h := scheduleLength q c.domain.card c.target.card
  let m := scheduleCutoff q c.overhead h
  PublicTables.integral (rowLaw c.proposal (c.source_nonempty.mono c.source_proposal) h)
    (implementAccept c.source
      (GoodCap SharpLogRamsey.Incidence.Incident q c.domain c.target (2000*q^(n+3)/S.card)))
    (fun _ => 1) m

end
end SharpLogRamsey.ReadyTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_NullFreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω : Type*} [Fintype Ω]

def Law.asPublic (μ : Law Ω) : PublicTables.Law Ω := ⟨μ.mass,μ.nonneg,μ.total⟩

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section

variable {β C ι : Type} [Fintype β] [Fintype C] [Fintype ι] [DecidableEq ι]

def Law.equiprobable (A : Type) [Fintype A] [Nonempty A] : Law A where
  mass _ := 1/(Fintype.card A:ℝ)
  nonneg _ := by positivity
  total := by simp [ne_of_gt (show (0:ℝ)<Fintype.card A by exact_mod_cast Fintype.card_pos)]

lemma Law.equiprobable_sum (A : Type) [Fintype A] [Nonempty A] (f : A→ℝ) :
    (∑ a,(Law.equiprobable A).mass a*f a)=(∑ a,f a)/Fintype.card A := by
  simp only [Law.equiprobable,one_div,←mul_sum]
  ring

lemma Law.restore_restrict (p : Law (ι→β)) (S : Finset ι) (f : (ι→β)→ℝ) :
    (∑ z,(p.restrict S).mass z*∑ x,((p.cond (fun y (i:S)=>y i) z).restrict Sᶜ).mass x*
      f (pasteTuple S z x))=∑ y,p.mass y*f y := by
  have h := p.history_sum (fun y (i:S)=>y i) f
  apply Eq.trans _ h
  apply sum_congr rfl
  intro z _
  by_cases hz : (p.restrict S).mass z=0
  · change (p.restrict S).mass z * _=(p.restrict S).mass z * _
    rw [hz,zero_mul,zero_mul]
  · congr 1
    rw [Law.restrict,Law.sum_map]
    apply sum_congr rfl
    intro y _
    by_cases hy : (p.cond (fun y (i:S)=>y i) z).mass y=0
    · simp only [hy,zero_mul]
    · have he := (p.cond_support (fun y (i:S)=>y i) z hz y hy).2
      congr 2
      funext i
      by_cases hi : i∈S
      · simp only [pasteTuple,dite_eq_left hi]
        exact (congrFun he ⟨i,hi⟩).symm
      · simp only [pasteTuple,dite_eq_right hi]

attribute [instance] ExposureModel.finiteHistory ExposureModel.finiteIndex ExposureModel.decIndex

namespace ExposureModel
variable (M : ExposureModel ι β C)

def expectation (f : (ι→β)→ℝ) : ℝ :=
  ∑ z,M.historyLaw.mass z*∑ x,(M.tupleLaw z).mass x*f (M.restore z x)

def initial (p : Law (ι→β)) {m : ℕ} (e : C×Fin m↪ι) (own : ι→Option C) :
    ExposureModel ι β C where
  History := Unit
  finiteHistory := inferInstance
  historyLaw := Law.equiprobable Unit
  Index _ := ι
  finiteIndex _ := inferInstance
  decIndex _ := inferInstance
  tupleLaw _ := p
  remaining _ := m
  embedding _ := e
  owner _ := own
  origin _ := Function.Embedding.refl ι
  restore _ := id
  restore_origin _ _ _ := rfl

omit [Fintype C] in
lemma initial_expectation (p : Law (ι→β)) {m : ℕ} (e : C×Fin m↪ι) (own : ι→Option C)
    (f : (ι→β)→ℝ) : (initial p e own).expectation f=∑ y,p.mass y*f y := by
  change (∑ _z : Unit,(1/(Fintype.card Unit:ℝ))*(∑ x,p.mass x*f x))=_
  simp

def join {m : ℕ} (p : Law (ι→β)) (e : C×Fin (m+1)↪ι)
    (child : ∀ f : C→Fin (m+1), (freshRepresentatives e f→β)→
      ExposureModel ↥((freshRepresentatives e f)ᶜ) β C) : ExposureModel ι β C where
  History := Σ f : C→Fin (m+1), Σ z : freshRepresentatives e f→β, (child f z).History
  finiteHistory := inferInstance
  historyLaw := (Law.equiprobable (C→Fin (m+1))).sigma (fun f=>
    (p.restrict (freshRepresentatives e f)).sigma (fun z=>(child f z).historyLaw))
  Index h := (child h.1 h.2.1).Index h.2.2
  finiteIndex _ := inferInstance
  decIndex _ := inferInstance
  tupleLaw h := (child h.1 h.2.1).tupleLaw h.2.2
  remaining h := (child h.1 h.2.1).remaining h.2.2
  embedding h := (child h.1 h.2.1).embedding h.2.2
  owner h := (child h.1 h.2.1).owner h.2.2
  origin h := ((child h.1 h.2.1).origin h.2.2).trans (Function.Embedding.subtype _)
  restore h x := pasteTuple (freshRepresentatives e h.1) h.2.1
    ((child h.1 h.2.1).restore h.2.2 x)
  restore_origin h x i := by
    change pasteTuple (freshRepresentatives e h.1) h.2.1
      ((child h.1 h.2.1).restore h.2.2 x) ((child h.1 h.2.1).origin h.2.2 i).val=x i
    rw [pasteTuple_compl]
    exact (child h.1 h.2.1).restore_origin h.2.2 x i

lemma join_expectation {m : ℕ} (p : Law (ι→β)) (e : C×Fin (m+1)↪ι)
    (child : ∀ f : C→Fin (m+1), (freshRepresentatives e f→β)→
      ExposureModel ↥((freshRepresentatives e f)ᶜ) β C)
    (φ : (ι→β)→ℝ) :
    (join p e child).expectation φ=
      (∑ f : C→Fin (m+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        (child f z).expectation (fun x=>φ (pasteTuple (freshRepresentatives e f) z x)))/
          Fintype.card (C→Fin (m+1)) := by
  unfold expectation
  change (∑ h,((Law.equiprobable (C→Fin (m+1))).sigma (fun f=>
    (p.restrict (freshRepresentatives e f)).sigma (fun z=>(child f z).historyLaw))).mass h*
      ∑ x,((child h.1 h.2.1).tupleLaw h.2.2).mass x*
        φ (pasteTuple (freshRepresentatives e h.1) h.2.1 ((child h.1 h.2.1).restore h.2.2 x)))=_
  rw [Law.sigma_sum]
  simp_rw [Law.sigma_sum]
  exact Law.equiprobable_sum _ _

lemma join_preserves {m : ℕ} (p : Law (ι→β)) (e : C×Fin (m+1)↪ι)
    (child : ∀ f : C→Fin (m+1), (freshRepresentatives e f→β)→
      ExposureModel ↥((freshRepresentatives e f)ᶜ) β C)
    (hchild : ∀ f z φ,(child f z).expectation φ=
      ∑ x,((p.cond (fun y (i:freshRepresentatives e f)=>y i) z).restrict
        (freshRepresentatives e f)ᶜ).mass x*φ x)
    (φ : (ι→β)→ℝ) : (join p e child).expectation φ=∑ y,p.mass y*φ y := by
  rw [join_expectation]
  simp_rw [hchild,p.restore_restrict]
  rw [sum_const,card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (ne_of_gt (show (0:ℝ)<Fintype.card (C→Fin (m+1)) by exact_mod_cast Fintype.card_pos))

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C : Type} [Fintype β] [Fintype C]
namespace ExposureModel

def atRound (n : ℕ) : (k : ℕ)→{ι : Type}→ [Fintype ι] →  [DecidableEq ι] →
    Law (ι→β)→(C×Fin (n+k)↪ι)→(ι→Option C)→Fin k→ExposureModel ι β C
  | 0,_,_,_,_,_,_,j => Fin.elim0 j
  | k+1,_,_,_,p,e,own,j => Fin.cases (initial p e own)
    (fun t=>join p e (fun f z=>
      atRound n k ((p.cond (fun y (i:freshRepresentatives e f)=>y i) z).restrict
        (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) (fun i=>own i) t)) j

theorem atRound_preserves (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k)
    (φ : (ι→β)→ℝ) : (atRound n k p e own t).expectation φ=∑ y,p.mass y*φ y := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · exact initial_expectation p e own φ
    · apply join_preserves
      intro f z ψ
      exact ih _ (remainingEmbedding e f) (fun i=>own i) j ψ

theorem atRound_remaining (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k)
    (z : (atRound n k p e own t).History) :
    n≤(atRound n k p e own t).remaining z := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => change n≤n+(k+1); omega
    | succ j => exact ih _ (remainingEmbedding e z.1) (fun i=>own i) j z.2.2

theorem atRound_unowned (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C)
    (hown : ∀ b x,own (e (b,x))=some b) (t : Fin k)
    (z : (atRound n k p e own t).History) (i : ι) (hi : own i=none) :
    ∃ j,(atRound n k p e own t).origin z j=i := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => exact ⟨i,rfl⟩
    | succ j =>
      have hn : i∉freshRepresentatives e z.1 := by
        intro hh
        obtain ⟨b,_,hb⟩:=mem_image.mp hh
        have hh:=hown b (z.1 b)
        rw [hb,hi] at hh
        cases hh
      obtain ⟨v,hv⟩ := ih _ (remainingEmbedding e z.1) (fun i=>own i)
        (remaining_own e z.1 own hown) j z.2.2 ⟨i,mem_compl.mpr hn⟩ hi
      exact ⟨v,congrArg Subtype.val hv⟩

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C : Type} [Fintype β] [Fintype C]

abbrev StateStatistic (β C : Type) [Fintype β] :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (m : ℕ),
    Law (I→β)→(C×Fin m↪I)→(I→Option C)→ℝ

namespace ExposureModel
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def mean (M : ExposureModel ι β C) (F : StateStatistic β C) : ℝ :=
  ∑ z,M.historyLaw.mass z*F (M.Index z) (M.remaining z) (M.tupleLaw z) (M.embedding z) (M.owner z)

end ExposureModel

def exposureAverage (F : StateStatistic β C) (n : ℕ) : (k : ℕ)→ {ι : Type}→
    [Fintype ι] → [DecidableEq ι] → Law (ι→β)→(C×Fin (n+k)↪ι)→(ι→Option C)→Fin k→ℝ
  | 0,_,_,_,_,_,_,j => Fin.elim0 j
  | k+1,I,_,_,p,e,own,j => Fin.cases (F I (n+(k+1)) p e own)
    (fun t=>(∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
      exposureAverage F n k ((p.cond (fun y (i:freshRepresentatives e f)=>y i) z).restrict
        (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) (fun i=>own i) t)/
      Fintype.card (C→Fin (n+k+1))) j

variable {A B K V : Type} [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def reciprocalBadStatistic (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ)
    (J D a : ℝ) : StateStatistic (A×B) C :=
  fun _ _ _ _ p e own=>roundBad p e own (reciprocalCharges p v w ρ r s) J D a

def reciprocalSelectedStatistic (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ)
    (J D a : ℝ) : StateStatistic (A×B) C :=
  fun _ _ _ _ p e own=>roundSelectedBad p e own (reciprocalCharges p v w ρ r s) J D a

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C ι Θ : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ]
namespace ExposureModel

def mix (ν : Law Θ) (M : Θ→ExposureModel ι β C) : ExposureModel ι β C where
  History := Σ z,(M z).History
  finiteHistory := inferInstance
  historyLaw := ν.sigma (fun z=>(M z).historyLaw)
  Index h := (M h.1).Index h.2
  finiteIndex _ := inferInstance
  decIndex _ := inferInstance
  tupleLaw h := (M h.1).tupleLaw h.2
  remaining h := (M h.1).remaining h.2
  embedding h := (M h.1).embedding h.2
  owner h := (M h.1).owner h.2
  origin h := (M h.1).origin h.2
  restore h := (M h.1).restore h.2
  restore_origin h := (M h.1).restore_origin h.2

abbrev Joint (M : ExposureModel ι β C) := Σ z : M.History,M.Index z→β

def joint (M : ExposureModel ι β C) : Law M.Joint :=
  M.historyLaw.sigma M.tupleLaw

def contextual (n k : ℕ) {Ω : Type} [Fintype Ω] (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k) :
    ExposureModel ι β C :=
  mix (p.map θ) (fun z=>atRound n k ((p.cond θ z).map G) (e z) (own z) t)

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_SourceCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {X Ω B : Type*} [Fintype X] [Fintype Ω] [Fintype B]

variable {β C ι Θ : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ]
namespace ExposureModel

theorem contextual_tagged (n k : ℕ) {Ω : Type} [Fintype Ω] (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (φ : Θ×(ι→β)→ℝ) :
    (∑ x,(contextual n k p θ G e own t).joint.mass x*
      φ (x.1.1,(contextual n k p θ G e own t).restore x.1 x.2))=
      ∑ ω,p.mass ω*φ (θ ω,G ω) := by
  rw [joint,Law.sigma_sum]
  change (∑ h,((p.map θ).sigma (fun z=>(atRound n k ((p.cond θ z).map G)
    (e z) (own z) t).historyLaw)).mass h*
      ∑ x,((atRound n k ((p.cond θ h.1).map G) (e h.1) (own h.1) t).tupleLaw h.2).mass x*
        φ (h.1,(atRound n k ((p.cond θ h.1).map G) (e h.1) (own h.1) t).restore h.2 x))=_
  rw [Law.sigma_sum]
  change (∑ z,(p.map θ).mass z*(atRound n k ((p.cond θ z).map G)
    (e z) (own z) t).expectation (fun x=>φ (z,x)))=_
  simp_rw [atRound_preserves]
  exact (p.history_observable_sum θ G (fun z x=>φ (z,x))).symm

theorem contextual_tagged_map (n k : ℕ) {Ω : Type} [Fintype Ω] (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k) :
    (contextual n k p θ G e own t).joint.map
      (fun x=>(x.1.1,(contextual n k p θ G e own t).restore x.1 x.2))=
        p.map (fun ω=>(θ ω,G ω)) := by
  ext y
  have he:=contextual_tagged n k p θ G e own t (fun x=>if x=y then 1 else 0)
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using he

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def conditionSuccess (p : Law Ω) (E : Ω→Prop) (h : 0<acceptProb p E) : Law Ω where
  mass x := if E x then p.mass x/acceptProb p E else 0
  nonneg x := by
    split_ifs
    · exact div_nonneg (p.nonneg x) h.le
    · exact le_rfl
  total := by
    have he : (∑ x,if E x then p.mass x/acceptProb p E else 0)=
        (∑ x,if E x then p.mass x else 0)/acceptProb p E := by
      rw [sum_div]
      apply sum_congr rfl
      intro x _
      split_ifs <;> simp only [zero_div]
    rw [he]
    have ht : (∑ x,if E x then p.mass x else 0)=acceptProb p E := by
      simp only [acceptProb,accepted,mul_one]
    rw [ht,div_self (ne_of_gt h)]

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TreeCodeEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeCodeEntropy
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B C : Type*}

def codes (allowed : Domains A B→Finset C) (read : CapReader A B C) :
    BinaryTree Unit→Domains A B→Finset (BinaryTree C)
  | .nil,_ => {.nil}
  | .node _ l r,U => (allowed U).biUnion (fun c=>
      ((codes allowed read l ((read U c).1,U.2)) ×ˢ
        (codes allowed read r (U.1,(read U c).2))).image
          (fun z=>.node c z.1 z.2))

def cost (allowed : Domains A B→Finset C) (read : CapReader A B C) :
    BinaryTree C→Domains A B→ℝ
  | .nil,_ => 0
  | .node c l r,U => log (allowed U).card+
      cost allowed read l ((read U c).1,U.2)+cost allowed read r (U.1,(read U c).2)

end
end SharpLogRamsey.TreeCodeEntropy

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
variable {Ω : Type*} [Fintype Ω]
def Law.ofPublic (p : PublicTables.Law Ω) : Law Ω := ⟨p.mass,p.nonneg,p.total⟩
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_FreshRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β C ι : Type} [Fintype β] [Fintype C] [Fintype ι] [DecidableEq ι]
namespace ExposureModel

abbrev FreshHistory (M : ExposureModel ι β C) := Σ z : M.History,C→Fin (M.remaining z)

def freshLaw (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z) : Law M.FreshHistory := by
  letI (z : M.History) : Nonempty (Fin (M.remaining z)) := ⟨⟨0,h z⟩⟩
  exact M.historyLaw.sigma (fun z=>Law.equiprobable (C→Fin (M.remaining z)))

omit [Fintype ι] [DecidableEq ι] in
lemma freshLaw_sum (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z)
    (φ : M.FreshHistory→ℝ) :
    (∑ x,(M.freshLaw h).mass x*φ x)=∑ z,M.historyLaw.mass z*
      ((∑ f : C→Fin (M.remaining z),φ ⟨z,f⟩)/Fintype.card (C→Fin (M.remaining z))) := by
  let (z : M.History) : Nonempty (Fin (M.remaining z)) := ⟨⟨0,h z⟩⟩
  unfold freshLaw
  rw [Law.sigma_sum]
  simp_rw [Law.equiprobable_sum]

omit [Fintype ι] [DecidableEq ι] in
lemma freshLaw_old (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z)
    (φ : M.History→ℝ) :
    (∑ x,(M.freshLaw h).mass x*φ x.1)=∑ z,M.historyLaw.mass z*φ z := by
  let (z : M.History) : Nonempty (Fin (M.remaining z)) := ⟨⟨0,h z⟩⟩
  rw [freshLaw_sum]
  apply sum_congr rfl
  intro z _
  congr 1
  change (∑ _f : C→Fin (M.remaining z),φ z)/_=φ z
  rw [sum_const,card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (ne_of_gt (show (0:ℝ)<Fintype.card (C→Fin (M.remaining z)) by exact_mod_cast Fintype.card_pos))

def afterDraw (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z) : ExposureModel ι β C where
  History := M.FreshHistory
  finiteHistory := inferInstance
  historyLaw := M.freshLaw h
  Index x := M.Index x.1
  finiteIndex _ := inferInstance
  decIndex _ := inferInstance
  tupleLaw x := M.tupleLaw x.1
  remaining x := M.remaining x.1
  embedding x := M.embedding x.1
  owner x := M.owner x.1
  origin x := M.origin x.1
  restore x := M.restore x.1
  restore_origin x := M.restore_origin x.1

def freshBad (M : ExposureModel ι β C)
    (charge : ∀ z,M.Index z→M.Index z→NNReal) (J D a : ℝ) (x : M.FreshHistory) :
    Finset (M.Index x.1) :=
  badIndices (M.tupleLaw x.1) (M.embedding x.1) (M.owner x.1) (charge x.1) J D a x.2

def freshSelected (M : ExposureModel ι β C) (x : M.FreshHistory) : Finset (M.Index x.1) :=
  freshRepresentatives (M.embedding x.1) x.2

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_SourceExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Θ Ω C ι A B K V : Type} [Fintype Θ] [Fintype Ω] [Fintype C]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace ExposureModel

lemma contextual_remaining (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (z : (contextual n k p θ G e own t).History) :
    n≤(contextual n k p θ G e own t).remaining z :=
  atRound_remaining n k ((p.cond θ z.1).map G) (e z.1) (own z.1) t z.2

lemma contextual_positive (n k : ℕ) (hn : 0<n) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (z : (contextual n k p θ G e own t).History) :
    0<(contextual n k p θ G e own t).remaining z :=
  hn.trans_le (contextual_remaining n k p θ G e own t z)

end ExposureModel
open ExposureModel

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_WindowLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section

lemma embedding_owner (w n : ℕ) (b : Block w) (x : Fin n) :
    owner w n (embedding w n (b,x))=some b := by
  rcases b with ⟨i,b⟩
  cases b
  · change (if x.val < n then some (i,false) else
      if 3*n ≤ x.val then some (i,true) else none) = some (i,false)
    rw [ite_eq_left x.isLt]
  · change (if 3*n+x.val < n then some (i,false) else
      if 3*n ≤ 3*n+x.val then some (i,true) else none) = some (i,true)
    rw [ite_eq_right (by omega),ite_eq_left (by omega)]

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_ExposureWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {ι β C X : Type} [Fintype β]
namespace ExposureModel

def lift (M : ExposureModel ι β C) (z : M.History) (e : X↪ι)
    (h : ∀ x,∃ i,M.origin z i=e x) : X↪M.Index z where
  toFun x := (h x).choose
  inj' := by
    intro x y he
    apply e.injective
    rw [←(h x).choose_spec,←(h y).choose_spec]
    exact congrArg (M.origin z) he

def representative (M : ExposureModel ι β C) (x : M.FreshHistory) : C↪M.Index x.1 where
  toFun b := M.embedding x.1 (b,x.2 b)
  inj' := by
    intro b c h
    exact congrArg Prod.fst ((M.embedding x.1).injective h)

end ExposureModel

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_PreparedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]

abbrev model (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k) :=
  contextual n k p θ G (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t

variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualPreparedWindows_1
lemma target_exists (z : (model w n k p θ G t).History) (x : Fin w×Fin (2*(n+k))) :
    ∃ i,(model w n k p θ G t).origin z i=middle w (n+k) x :=
  atRound_unowned n k ((p.cond θ z.1).map G) (embedding w (n+k)) (owner w (n+k))
    (embedding_owner w (n+k)) t z.2 _ (middle_unowned w (n+k) x.1 x.2)

def target (z : (model w n k p θ G t).History) : Fin w×Fin (2*(n+k)) ↪ (model w n k p θ G t).Index z :=
  (model w n k p θ G t).lift z (middle w (n+k)) (target_exists w n k p θ G t z)

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_GoodPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.finDecC
local instance indexDecC (z : (model w n k p θ G t).FreshHistory) :
    DecidableEq ((model w n k p θ G t).Index z.1) := Classical.decEq _

abbrev goodMiddle (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w) : Finset (Fin (2*(n+k))) :=
  univ.filter (fun x=>target w n k p θ G t z.1 (i,x)∉bad)

def goodTarget (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w) :
    Fin (goodMiddle w n k p θ G t z bad i).card ↪ (model w n k p θ G t).Index z.1 :=
  { toFun := fun j=>target w n k p θ G t z.1 (i,(goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl j)
    inj' := by
      intro a b h
      exact ((goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl).injective
        (congrArg Prod.snd ((target w n k p θ G t z.1).injective h)) }

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance goodBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_MixtureRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Selection.ExposureModel
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C ι Θ Ω : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ] [Fintype Ω]

lemma afterDraw_tagged_map (n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z) :
    ((contextual n k p θ G e own t).afterDraw hp).joint.map
      (fun x=>(x.1.1.1,(contextual n k p θ G e own t).restore x.1.1 x.2))=
        p.map (fun ω=>(θ ω,G ω)) := by
  rw [←contextual_tagged_map n k p θ G e own t]
  apply Law.eq_of_integrals
  intro f
  rw [Law.sum_map,Law.sum_map]
  let M:=contextual n k p θ G e own t
  change (∑ x,((M.freshLaw hp).sigma (fun z=>M.tupleLaw z.1)).mass x*
      f (x.1.1.1,M.restore x.1.1 x.2))=
        ∑ x,(M.historyLaw.sigma M.tupleLaw).mass x*f (x.1.1,M.restore x.1 x.2)
  rw [Law.sigma_sum,Law.sigma_sum]
  exact M.freshLaw_old hp (fun z=>∑ y,(M.tupleLaw z).mass y*f (z.1,M.restore z y))
end
end SharpLogRamsey.Selection.ExposureModel

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_OutputComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω F A : Type} [Fintype Ω] [Fintype F] [Fintype A]
  {N ℓ m : ℕ} {p : Law Ω} {G : Ω→Fin ℓ→F} {B C L : ℝ}

def ContextOutput.transport (e : ContextOutput p G m B C L)
    (φ : F≃A) (G₀ : Ω→Fin N→A) (j : Ω→Fin ℓ↪o Fin N)
    (h : ∀ x i,φ (G x i)=G₀ x (j x i)) :
    ContextOutput p G₀ m B C L where
  X:=e.X
  Γ:=e.Γ
  finiteX:=e.finiteX
  finiteΓ:=e.finiteΓ
  μ:=e.μ
  source:=e.source
  msg:=e.msg
  chosen:=fun x=>(e.chosen x).trans (j (e.source x))
  domains:=fun c i=>(e.domains c i).map φ.toEmbedding
  supported:=e.supported
  hit:=by
    intro x i
    change G₀ (e.source x) (j (e.source x) (e.chosen x i)) ∈ _
    rw [←h]
    exact mem_map.mpr ⟨_,e.hit x i,rfl⟩
  size:=by intro c i;simpa only [card_map] using e.size c i
  dominated:=e.dominated
  cost:=e.cost

def ContextOutput.compose (e : ContextOutput p G m B C L)
    {n : ℕ} {B' C' L' : ℝ}
    (f : ContextOutput e.μ (fun x i=>G (e.source x) (e.chosen x i)) n B' C' L')
    (hL' : 0≤L') : ContextOutput p G n B' C' (L'*L) where
  X:=f.X
  Γ:=f.Γ
  finiteX:=f.finiteX
  finiteΓ:=f.finiteΓ
  μ:=f.μ
  source:=e.source∘f.source
  msg:=f.msg
  chosen:=fun x=>(f.chosen x).trans (e.chosen (f.source x))
  domains:=f.domains
  supported:=fun x=>e.supported (f.source x)
  hit:=f.hit
  size:=f.size
  dominated:=by
    intro a
    rw [←Law.map_map]
    calc
      _ ≤ ∑ y ∈ univ.filter (fun y=>e.source y=a),L'*e.μ.mass y := by
        change (∑ y ∈ univ.filter (fun y=>e.source y=a),(f.μ.map f.source).mass y)≤_
        exact sum_le_sum (fun y _=>f.dominated y)
      _ = L'*(e.μ.map e.source).mass a := by
        simp only [Law.map,mul_sum]
      _ ≤ L'*(L*p.mass a) := mul_le_mul_of_nonneg_left (e.dominated a) hL'
      _ = _ := by ring
  cost:=f.cost
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_OutputRebase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω F : Type} [Fintype Ω] [Fintype F]
  {ℓ m : ℕ} {p : Law Ω} {G : Ω→Fin ℓ→F} {B C L : ℝ}

def ContextOutput.mono (e : ContextOutput p G m B C L)
    {B' C' L' : ℝ} (hB : B ≤ B') (hC : C ≤ C') (hL : L ≤ L') :
    ContextOutput p G m B' C' L' where
  X:=e.X
  Γ:=e.Γ
  finiteX:=e.finiteX
  finiteΓ:=e.finiteΓ
  μ:=e.μ
  source:=e.source
  msg:=e.msg
  chosen:=e.chosen
  domains:=e.domains
  supported:=e.supported
  hit:=e.hit
  size:=fun c i=>(e.size c i).trans hB
  dominated:=fun a=>(e.dominated a).trans (mul_le_mul_of_nonneg_right hL (p.nonneg a))
  cost:=e.cost.trans hC

def ContextOutput.rebase (e : ContextOutput p G m B C L)
    (p₀ : Law Ω) {L₀ : ℝ} (hL : 0 ≤ L)
    (hp : ∀ x,p.mass x ≤ L₀*p₀.mass x) : ContextOutput p₀ G m B C (L*L₀) where
  X:=e.X
  Γ:=e.Γ
  finiteX:=e.finiteX
  finiteΓ:=e.finiteΓ
  μ:=e.μ
  source:=e.source
  msg:=e.msg
  chosen:=e.chosen
  domains:=e.domains
  supported:=by
    intro x hz
    have h:=hp (e.source x)
    rw [hz,mul_zero] at h
    exact e.supported x (le_antisymm h (p.nonneg _))
  hit:=e.hit
  size:=e.size
  dominated:=by
    intro x
    exact (e.dominated x).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hp x) hL)
  cost:=e.cost

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Marking
open Finset Selection ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def covectorTuple {ι : Type*} (F : ι→ProjectivePair (K:=K) (V:=V)) :
    ι → (CovectorPair (K:=K) (V:=V)) := fun i => (F i).swap

def covectorDomain (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    Finset (CovectorPair (K:=K) (V:=V)) := D.map (Equiv.prodComm _ _).toEmbedding

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ZeroExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C : Type} [Fintype β] [Fintype C]

def zeroBadStatistic (J D a : ℝ) : StateStatistic β C :=
  fun _ _ _ _ p e own=>roundBad p e own (fun _ _=>0) J D a

def zeroSelectedStatistic (J D a : ℝ) : StateStatistic β C :=
  fun _ _ _ _ p e own=>roundSelectedBad p e own (fun _ _=>0) J D a

namespace ExposureModel
variable {ι Θ Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Θ] [Fintype Ω]

lemma contextual_positive_general (n k : ℕ) (hn : 0<n) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (z : (contextual n k p θ G e own t).History) :
    0<(contextual n k p θ G e own t).remaining z :=
  hn.trans_le (atRound_remaining n k ((p.cond θ z.1).map G) (e z.1) (own z.1) t z.2)

end ExposureModel
open ExposureModel

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_PreparedMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b : ℝ}
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.mixBlockDec
variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
local notation "M" => model w n k p θ G t

abbrev PositiveHistory := {z : (M).FreshHistory // ((M).freshLaw hp).mass z≠0}

variable (e : ∀ z : PositiveHistory w n k p θ G t hp,
  Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))

def mixedPrepared := Realization.mix (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) ((M).freshLaw hp) (fun z=>(M).tupleLaw z.1) e

def attachedPrepared :=
  (mixedPrepared w n k p θ G t hp e).attach p
    (fun x=>(x.1.1.1,(M).restore x.1.1 x.2)) (fun ω=>(θ ω,G ω))
    (afterDraw_tagged_map n k p θ G (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp)

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_PreparedOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance prepOutBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.prepOutFinDec
local instance prepOutBlockDec_ra0f3f4_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→ActualPivot.Flag (K:=K) (V:=V)) (t : Fin k)
  (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (e : ∀ z : PositiveHistory w n k p θ G t hp,
    Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
      (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))
  (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1))
  (live : (model w n k p θ G t).FreshHistory→Finset (Fin w)) (fallback : Fin w)

abbrev preparedTargets (y : (mixedPrepared w n k p θ G t hp e).Ω) : Fin w→List (ActualPivot.Flag (K:=K) (V:=V)) :=
  fun i=>List.ofFn (fun j=>(e y.1).source y.2 (goodTarget w n k p θ G t y.1.val (bad y.1.val) i j))

abbrev preparedTree (y : (mixedPrepared w n k p θ G t hp e).Ω) := liveTree (live y.1.val) fallback

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance intBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_UniformInteger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance uniformIntBanks {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
    [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
    (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance experimentBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.experimentFinDec
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.experimentSlotDec
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.experimentBlockDec
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)

def integerBad (r : ℕ) (J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) :=
  badIndices ((model w n k p θ G t).tupleLaw z.1) ((model w n k p θ G t).embedding z.1)
    ((model w n k p θ G t).owner z.1)
    (reciprocalCharges ((model w n k p θ G t).tupleLaw z.1) Projectivization.rep Projectivization.rep
      (1/(100*((d:ℝ)+3))) r (d+3-r)) J D a z.2

def integerLive (r : ℕ) (J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) :=
  univ\badWindows ((model w n k p θ G t).representative z) (integerBad (d:=d) w n k p θ G t r J D a z)

def integerPop (r : ℕ) (J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) : ℕ :=
  ∑ i∈integerLive (d:=d) w n k p θ G t r J D a z,
    (goodMiddle w n k p θ G t z (integerBad (d:=d) w n k p θ G t r J D a z) i).card

variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (e : ∀ z : PositiveHistory w n k p θ G t hp,
    Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
      (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))

def integerTargets (r : ℕ) (J D a : ℝ) (y : (mixedPrepared w n k p θ G t hp e).Ω) :
    Fin w→List (Projectivization K (Module.Dual K V)×Projectivization K V) := fun i=>
  List.ofFn (fun j=>(e y.1).source y.2
    (goodTarget w n k p θ G t y.1.val (integerBad (d:=d) w n k p θ G t r J D a y.1.val) i j))

def integerTree (r : ℕ) (J D a : ℝ) (fallback : Fin w)
    (y : (mixedPrepared w n k p θ G t hp e).Ω) :=
  liveTree (integerLive (d:=d) w n k p θ G t r J D a y.1.val) fallback

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerQuarter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}
local instance quarterBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_OpenRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance openBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_UniformOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance uniformIntOpenBanks {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
    [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
    (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_OpenExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance openExpBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.openExpFinDec
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.openExpSlotDec
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.openExpBlockDec
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)

def openBad (J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) :=
  badIndices ((model w n k p θ G t).tupleLaw z.1) ((model w n k p θ G t).embedding z.1)
    ((model w n k p θ G t).owner z.1) (fun _ _=>0) J D a z.2

def openKeep (u : Θ→Slot w (n+k)→ℝ) (gap : ℝ) (z : (model w n k p θ G t).FreshHistory) (i : Fin w) : Prop :=
  u z.1.1 ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,false)))-
    u z.1.1 ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,true)))≤gap

def openLive (u : Θ→Slot w (n+k)→ℝ) (gap J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) :=
  (univ\badWindows ((model w n k p θ G t).representative z) (openBad w n k p θ G t J D a z)).filter
    (openKeep w n k p θ G t u gap z)

def openPop (u : Θ→Slot w (n+k)→ℝ) (gap J D a : ℝ) (z : (model w n k p θ G t).FreshHistory) : ℕ :=
  ∑ i∈openLive w n k p θ G t u gap J D a z,
    (goodMiddle w n k p θ G t z (openBad w n k p θ G t J D a z) i).card

variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (e : ∀ z : PositiveHistory w n k p θ G t hp,
    Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
      (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))

def openTargets (J D a : ℝ) (y : (mixedPrepared w n k p θ G t hp e).Ω) :
    Fin w→List (Projectivization K (Module.Dual K V)×Projectivization K V) := fun i=>
  List.ofFn (fun j=>(e y.1).source y.2
    (goodTarget w n k p θ G t y.1.val (openBad w n k p θ G t J D a y.1.val) i j))

def openTree (u : Θ→Slot w (n+k)→ℝ) (gap J D a : ℝ) (fallback : Fin w)
    (y : (mixedPrepared w n k p θ G t hp e).Ω) :=
  liveTree (openLive w n k p θ G t u gap J D a y.1.val) fallback

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_OpenQuarter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}
local instance openQuarterBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section

def stepPrefactor (d : ℕ) : ℝ:=max 8000000 (highPrefactor d)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_StageBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

def stageD (σ η : ℝ) (k : ℕ) (Λ Δ : ℝ) : ℝ :=
  σ^beta η*(1+Λ/(k:ℝ)+Δ*σ^(-η))

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_InitialTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey
open Finset Real Selection Marking
open scoped Classical BigOperators
noncomputable section

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def initial_context {Ω : Type} [Fintype Ω] {k : ℕ} (p : Law Ω)
    (F : Ω→Fin k→Flag K V) (B : ℝ) (hB : (Fintype.card (Flag K V):ℝ) ≤ B) :
    ContextOutput p (fun x j=>flagPair (F x j)) k B 0 1 where
  X:={x // p.mass x≠0}
  Γ:=Unit
  finiteX:=inferInstance
  finiteΓ:=inferInstance
  μ:=p.nullFree
  source:=Subtype.val
  msg:=fun _=>()
  chosen:=fun _=>OrderEmbedding.ofStrictMono id (fun _ _ h=>h)
  domains:=fun _ _=>univ.map ⟨flagPair,flagPair_injective⟩
  supported:=fun x=>x.property
  hit:=fun x j=>mem_map.mpr ⟨F x.val j,mem_univ _,rfl⟩
  size:=by intro _ _;simpa only [card_map,card_univ] using hB
  dominated:=by
    intro x
    have hh:=p.nullFree_map id
    rw [Law.map_id] at hh
    have he : p.nullFree.map (Subtype.val : {x // p.mass x≠0}→Ω)=p:=by
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr!
    rw [he,one_mul]
  cost:=by
    have hh:=entropy_le_log_card (p.nullFree.map (fun _=>())) univ (by simp)
    simpa using hh

end
end SharpLogRamsey

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_IterationScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

def evenScale (σ η : ℝ) : ℕ:=2*⌈σ^beta η/2⌉₊

def nextD (σ η D : ℝ) : ℝ:=σ^beta η*(1+D*σ^(-η/3)+16*D*σ^(6*beta η)*σ^(-η))

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_NumericalIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

def iterationBudgets (d : ℕ) (σ η : ℝ) (k : ℕ) : ℕ→ℝ×ℝ
  | 0 => (0,((d-1:ℕ):ℝ)*σ)
  | n+1 => let b:=iterationBudgets d σ η k n
           let D:=stageD σ η k b.1 b.2
           (D*σ^(-η/3)*k,16*scaleKstar σ η D)

def iterationD (d : ℕ) (σ η : ℝ) (k n : ℕ) : ℝ:=
  stageD σ η k (iterationBudgets d σ η k n).1 (iterationBudgets d σ η k n).2

end
end SharpLogRamsey.SourceScales

end

end OAI
end


