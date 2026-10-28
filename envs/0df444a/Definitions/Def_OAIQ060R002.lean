-- Prove2me | Definitions.Def_OAIQ060R002
-- name    : OAIQ060R002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:50:22.851997+00:00
-- url     : https://prove2.me/theorems/ae11ba4d-2dbe-4c71-a741-406ca312839c
-- title:
--   Definitions bundle OAIQ060R002 of the split of OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 182 declarations of OpenAI's Lean: 79 definitions, 6 inductive types or structures and 97 theorems. The definitions and types are `OAI.SharpRamseyFive.FiniteEntropy.unionMessage`, `OAI.SharpRamseyFive.FiniteEntropy.unionRecord`, `OAI.SharpRamseyFive.FiniteEntropy.windowReady`, `OAI.SharpRamseyFive.FlagConstruction.encodeRaw`, `OAI.SharpRamseyFive.FlatAtlas.flatCode`, `OAI.SharpRamseyFive.HighMoment.absSplit`, `OAI.SharpRamseyFive.HighMoment.allTrunc`, `OAI.SharpRamseyFive.HighSamples.SampleConflict`, `OAI.SharpRamseyFive.HighSamples.growSpan`, `OAI.SharpRamseyFive.HighSamples.highDomain`, `OAI.SharpRamseyFive.HighSamples.newHits`, `OAI.SharpRamseyFive.HighSamples.sampleSpan`, `OAI.SharpRamseyFive.LowConflict.capturedEvent`, `OAI.SharpRamseyFive.LowConflict.reverseMiss`, `OAI.SharpRamseyFive.LowConflict.tupleCapture`, `OAI.SharpRamseyFive.LowConflict.tupleCollision`, `OAI.SharpRamseyFive.LowConflict.tupleMarginal`, `OAI.SharpRamseyFive.Marking.DomainClass`, `OAI.SharpRamseyFive.Marking.ForwardCaps`, `OAI.SharpRamseyFive.Marking.HighCaps`, `OAI.SharpRamseyFive.Marking.ReciprocalCaps`, `OAI.SharpRamseyFive.Marking.ReciprocalLevels`, `OAI.SharpRamseyFive.Marking.ReciprocalWindows`, `OAI.SharpRamseyFive.Marking.ReciprocalWindows.firstReference`, `OAI.SharpRamseyFive.Marking.ReciprocalWindows.firstSupport`, `OAI.SharpRamseyFive.Marking.ReciprocalWindows.secondReference`, `OAI.SharpRamseyFive.Marking.ReciprocalWindows.secondSupport`, `OAI.SharpRamseyFive.Marking.ReverseCaps`, `OAI.SharpRamseyFive.Marking.WindowHistory`, `OAI.SharpRamseyFive.Marking.WindowLevelsData`, `OAI.SharpRamseyFive.Marking.actualWindowSet`, `OAI.SharpRamseyFive.Marking.actualWindows`, `OAI.SharpRamseyFive.Marking.allHistIDE`, `OAI.SharpRamseyFive.Marking.backwardDomain`, `OAI.SharpRamseyFive.Marking.backwardRecord`, `OAI.SharpRamseyFive.Marking.cheapDomain`, `OAI.SharpRamseyFive.Marking.classStream`, `OAI.SharpRamseyFive.Marking.classValid`, `OAI.SharpRamseyFive.Marking.decodeState`, `OAI.SharpRamseyFive.Marking.finiteDecodeRecord` and 45 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `RamseyFive_Bounds_DensityUpper`, `RamseyFive_Bounds_UpperSet`, `RamseyFive_Decoding_HighSampleDecoder`, `RamseyFive_Entropy_ConditionPullback`, `RamseyFive_Entropy_OrderedReciprocalLaw`, `RamseyFive_Entropy_SubsetDeficit`, `RamseyFive_Entropy_UnionMarking`, `RamseyFive_Entropy_WindowReadiness`, `RamseyFive_Geometry_FlagGraph`, `RamseyFive_Geometry_FlatAtlas`, `RamseyFive_Geometry_HighPairVariance`, `RamseyFive_Geometry_HighSampleGrowth`, `RamseyFive_Geometry_IncidencesDegrees`, `RamseyFive_Geometry_ProjectiveExpectedLevelLoss`, `RamseyFive_Geometry_Q`, `RamseyFive_Geometry_SubspacePointsEquiv`, `RamseyFive_Iteration_StageState`, `RamseyFive_Marking_AllHistoryWindowLoss`, `RamseyFive_Marking_ChooseLevel`, `RamseyFive_Marking_ClassPrepared`, `RamseyFive_Marking_ClassifiedStream`, `RamseyFive_Marking_Collisions`, `RamseyFive_Marking_DomainTransport`, `RamseyFive_Marking_HighSampleRetention`, `RamseyFive_Marking_MarkedStreamExtraction`, `RamseyFive_Marking_MarkingClassDomains`, `RamseyFive_Marking_MarkingClasses`, `RamseyFive_Marking_MarkingEndpoints`, `RamseyFive_Marking_ReciprocalBands`, `RamseyFive_Marking_ReciprocalDomainCaps`, `RamseyFive_Marking_ReciprocalGoodReference`, `RamseyFive_Marking_ReciprocalLevelProducer`, `RamseyFive_Marking_ReciprocalLowConflict`, `RamseyFive_Marking_ReverseMiss`, `RamseyFive_Marking_ScanChoice`, `RamseyFive_Marking_ScanRecord`, `RamseyFive_Marking_ScanRecordPresent`, `RamseyFive_Marking_State`, `RamseyFive_Marking_SurvivingWindowCode`, `RamseyFive_Marking_TwoScan`, `RamseyFive_Marking_TwoScanContext`, `RamseyFive_Marking_WindowCaps`, `RamseyFive_Marking_WindowDeletionCount`, `RamseyFive_Marking_WindowLevels`, `RamseyFive_Marking_WindowReciprocalScores`, `RamseyFive_Streams_PreparedStream`, `RamseyFive_Streams_SelectedExtraction`, `RamseyFive_Trees_Windows`, `SharpRamsey_Entropy_ComponentLabelWitness`, `SharpRamsey_Entropy_TruncatedTupleIntegrable`.
--
--   **Imports.** It imports the bundles `OAIQ060R000` and `OAIQ060R001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ060R004`; the statements `OAI.SharpRamseyFive.AmbientEnumeration.ambient_refined_truncated_moment`, `OAI_SharpRamseyFive_Marking_eventually_window_target_retention`, `OAI_SharpRamseyFive_ProjectiveIncidence_oriented_actual_target_loss`, `OAI_SharpRamseyFive_ProjectiveIncidence_oriented_original_tree_missing`, `OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec`, `OAI.SharpRamseyFive.ProjectiveIncidence.reverse_after_general_capture`, `OAI_SharpRamseyFive_ProjectiveRestriction_eventually_plane_public`, `OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor`, `OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_finite_predictor`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_public_law`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_protocol`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_low_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_coordinates_certified`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_three_finite_oriented`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_small_protocol`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_three_validation_tail`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_oriented`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_procedure`, `OAI_SharpRamseyFive_ScoreGeometry_literal_plane_radial_exceptions`, `OAI_SharpRamseyFive_ScoreGeometry_residual_global_trunc_exp_bound_dim`, `OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage`, `OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible`, `OAI.SharpRamseyFive.SelectedTuple.eventually_high_three_prepared_impossible`, `OAI.SharpRamseyFive.SelectedTuple.eventually_prepared_dispatch` and `OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage`; the proofs of `OAI.SharpRamseyFive.AmbientEnumeration.ambient_refined_truncated_moment`, `OAI.SharpRamseyFive.AmbientEnumeration.ambient_untruncated_moment`, `OAI_SharpRamseyFive_Marking_eventually_window_target_retention`, `OAI_SharpRamseyFive_ProjectiveIncidence_oriented_actual_target_loss`, `OAI_SharpRamseyFive_ProjectiveIncidence_oriented_original_tree_missing`, `OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec`, `OAI.SharpRamseyFive.ProjectiveIncidence.reverse_after_general_capture`, `OAI_SharpRamseyFive_ProjectiveRestriction_eventually_plane_public`, `OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor`, `OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_finite_predictor`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_public_law`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_score_integrals`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_low_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_peel_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_half_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_coordinates_certified`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_three_finite_oriented`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_three_validation_tail`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_oriented`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete`, `OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions_card`, `OAI_SharpRamseyFive_ScoreGeometry_literal_plane_radial_exceptions` and `OAI_SharpRamseyFive_ScoreGeometry_residual_global_trunc_exp_bound_dim`.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ060R000
import Definitions.Def_OAIQ060R001

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SubspacePointsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma incident_iff_dualAnnihilator (a : ℙ K V) (b : ℙ K (Module.Dual K V)) :
    Incident a b ↔ b.submodule ≤ a.submodule.dualAnnihilator := by
  rw [Projectivization.submodule_eq b, Submodule.span_singleton_le_iff_mem,
    Submodule.mem_dualAnnihilator]
  rfl

theorem card_points_on_hyperplane [Finite K] [FiniteDimensional K V]
    (b : ℙ K (Module.Dual K V)) :
    Nat.card {a : ℙ K V // Incident a b} =
      ∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  have hk : finrank K (LinearMap.ker b.rep) = finrank K V - 1 := by omega
  change Nat.card {a : ℙ K V // a.submodule ≤ LinearMap.ker b.rep} = _
  rw [card_subspacePoints, hk]

theorem card_hyperplanes_through_point [Finite K] [FiniteDimensional K V]
    (a : ℙ K V) :
    Nat.card {b : ℙ K (Module.Dual K V) // Incident a b} =
      ∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (incident_iff_dualAnnihilator a)),
    card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq a.submodule
  rw [a.finrank_submodule] at h
  congr 2
  omega

theorem card_hyperplanes_through_pair [Finite K] [FiniteDimensional K V]
    {a a' : ℙ K V} (haa : a ≠ a') :
    Nat.card {b : ℙ K (Module.Dual K V) // Incident a b ∧ Incident a' b} =
      ∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i := by
  have he (b : ℙ K (Module.Dual K V)) :
      Incident a b ∧ Incident a' b ↔
        b.submodule ≤ (a.submodule ⊔ a'.submodule).dualAnnihilator := by
    rw [incident_iff_dualAnnihilator, incident_iff_dualAnnihilator,
      Submodule.dualAnnihilator_sup_eq, le_inf_iff]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (a.submodule ⊔ a'.submodule)
  rw [finrank_sup_points haa] at h
  congr 2
  omega

open scoped Classical

variable [Finite K] [FiniteDimensional K V]
variable [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

noncomputable def incidenceEntry (a : ℙ K V) (b : ℙ K (Module.Dual K V)) : ℝ :=
  if Incident a b then 1 else 0

noncomputable def weightOnHyperplane (w : ℙ K V → ℝ) (b : ℙ K (Module.Dual K V)) : ℝ :=
  ∑ a, incidenceEntry a b * w a

omit [Fintype (ℙ K V)] in
lemma sum_entry (a : ℙ K V) :
    ∑ b, incidenceEntry a b =
      ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) := by
  classical
  unfold incidenceEntry
  rw [Finset.sum_boole, ← Fintype.card_subtype, Fintype.card_eq_nat_card,
    card_hyperplanes_through_point]

omit [Fintype (ℙ K V)] in
lemma sum_entry_mul_entry (a a' : ℙ K V) :
    ∑ b, incidenceEntry a b * incidenceEntry a' b =
      if a = a' then ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ)
      else ((∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ) : ℝ) := by
  classical
  by_cases haa : a = a'
  · subst a'
    simp only [ite_true]
    convert sum_entry a using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro b _
    simp [incidenceEntry]
  · rw [ite_eq_right haa]
    trans ∑ b : ℙ K (Module.Dual K V), if Incident a b ∧ Incident a' b then (1 : ℝ) else 0
    · apply Finset.sum_congr rfl
      intro b _
      simp only [incidenceEntry]
      split_ifs <;> simp_all
    · rw [Finset.sum_boole, ← Fintype.card_subtype, Fintype.card_eq_nat_card,
        card_hyperplanes_through_pair haa]

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Q
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
open scoped Classical
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem sum_weightOnHyperplane_sq (w : ℙ K V → ℝ) :
    ∑ b, weightOnHyperplane w b ^ 2 =
      (((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) -
        ((∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ) : ℝ)) *
          (∑ a, w a ^ 2) +
      ((∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ) : ℝ) * (∑ a, w a) ^ 2 := by
  classical
  let m : ℝ := (∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ)
  let l : ℝ := (∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ)
  have hentry (a a' : ℙ K V) : ∑ b, incidenceEntry a b * incidenceEntry a' b =
      (if a = a' then m - l else 0) + l := by
    rw [sum_entry_mul_entry]
    split_ifs <;> dsimp [m, l] <;> ring
  calc
    ∑ b, weightOnHyperplane w b ^ 2 =
        ∑ b, ∑ a, ∑ a', (incidenceEntry a b * incidenceEntry a' b) * (w a * w a') := by
      apply Finset.sum_congr rfl
      intro b _
      rw [weightOnHyperplane, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro a' _
      ring
    _ = ∑ a, ∑ a', ((if a = a' then m - l else 0) + l) * (w a * w a') := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a' _
      rw [← Finset.sum_mul, hentry]
    _ = (m - l) * (∑ a, w a ^ 2) + l * (∑ a, w a) ^ 2 := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      congr 1
      · simp_rw [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          ← pow_two, ← Finset.mul_sum]
      · rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]

omit [Fintype (ℙ K (Dual K V))] in
lemma sum_entry_column (b : ℙ K (Module.Dual K V)) :
    ∑ a, incidenceEntry a b =
      ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) := by
  classical
  unfold incidenceEntry
  rw [Finset.sum_boole, ← Fintype.card_subtype, Fintype.card_eq_nat_card,
    card_points_on_hyperplane]

theorem incidence_variance_eq {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (w : ℙ K V → ℝ) :
    ∑ b, (weightOnHyperplane w b -
        ((Q (Nat.card K) (d - 1) : ℝ) / Q (Nat.card K) d) * (∑ a, w a)) ^ 2 =
      (Nat.card K : ℝ) ^ (d - 1) *
        ((∑ a, w a ^ 2) - (∑ a, w a) ^ 2 / Q (Nat.card K) d) := by
  classical
  let n : ℝ := Q (Nat.card K) d
  let m : ℝ := Q (Nat.card K) (d-1)
  let s : ℝ := ∑ a, w a
  let u : ℙ K V → ℝ := fun a => w a - s / n
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast (Q_pos (Nat.card K) d).ne'
  have hc : (Fintype.card (ℙ K V) : ℝ) = n := by rw [card_points hdim]
  have hs : ∑ a, u a = 0 := by
    simp only [u, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    change s - n * (s / n) = 0
    field_simp
    ring
  have hd' : d - 1 + 1 = d := by omega
  have hd'' : d + 1 - 2 = d - 1 := by omega
  have hm : ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) = m := by
    simp only [hdim, Nat.add_sub_cancel, m, Q, hd']
  have hwu (b : ℙ K (Module.Dual K V)) :
      weightOnHyperplane u b = weightOnHyperplane w b - m / n * s := by
    simp only [weightOnHyperplane, u, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, sum_entry_column, hm]
    ring
  have hnorm : ∑ a, u a ^ 2 = (∑ a, w a ^ 2) - s ^ 2 / n := by
    calc
      ∑ a, u a ^ 2 = ∑ a, (w a ^ 2 - 2 * (s/n) * w a + (s/n)^2) := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp [u]
        ring
      _ = (∑ a, w a ^ 2) - 2 * (s/n) * s + n * (s/n)^2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, s]
      _ = (∑ a, w a ^ 2) - s ^ 2 / n := by field_simp; ring
  have hdiff :
      ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) -
        ((∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ) : ℝ) =
      (Nat.card K : ℝ) ^ (d - 1) := by
    rw [hdim, Nat.add_sub_cancel, hd'', ← hd', Finset.sum_range_succ]
    push_cast
    ring
  change ∑ b, (weightOnHyperplane w b - m / n * s) ^ 2 = _
  simp_rw [← hwu]
  rw [sum_weightOnHyperplane_sq, hs, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    hdiff, hnorm]

theorem incidence_variance {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (w : ℙ K V → ℝ) :
    ∑ b, (weightOnHyperplane w b -
        ((Q (Nat.card K) (d - 1) : ℝ) / Q (Nat.card K) d) * (∑ a, w a)) ^ 2 ≤
      (Nat.card K : ℝ) ^ (d - 1) * ∑ a, w a ^ 2 := by
  rw [incidence_variance_eq hdim hd]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sub_le_self _ (by positivity)

theorem incidence_weighted_mixing_sq {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (w : ℙ K V → ℝ) (B : Finset (ℙ K (Module.Dual K V))) :
    ((∑ b ∈ B, weightOnHyperplane w b) -
      ((Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d) * B.card * (∑ a, w a)) ^ 2 ≤
      (Nat.card K : ℝ) ^ (d-1) * (∑ a, w a ^ 2) * B.card := by
  classical
  let f (b : ℙ K (Module.Dual K V)) := weightOnHyperplane w b -
      ((Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d) * (∑ a, w a)
  have hsum : (∑ b ∈ B, f b) = (∑ b ∈ B, weightOnHyperplane w b) -
      ((Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d) * B.card * (∑ a, w a) := by
    simp only [f, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ)) f
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [← hsum]
  calc
    (∑ b ∈ B, f b) ^ 2 ≤ (B.card : ℝ) * ∑ b ∈ B, f b ^ 2 := hcs
    _ ≤ (B.card : ℝ) * ∑ b, f b ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_univ_sum_of_nonneg (fun b => sq_nonneg (f b)))
        (by positivity)
    _ ≤ (B.card : ℝ) * ((Nat.card K : ℝ) ^ (d-1) * ∑ a, w a ^ 2) :=
      mul_le_mul_of_nonneg_left (incidence_variance hdim hd w) (by positivity)
    _ = _ := by ring

noncomputable def incidences (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) : ℕ :=
  ((A ×ˢ B).filter fun ab => Incident ab.1 ab.2).card

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma incidences_eq_sum (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) :
    (incidences A B : ℝ) = ∑ b ∈ B, ∑ a ∈ A, incidenceEntry a b := by
  rw [incidences, ← Finset.sum_boole, Finset.sum_product, Finset.sum_comm]
  rfl

theorem incidence_mixing {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) :
    |(incidences A B : ℝ) -
      ((Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d) * A.card * B.card| ≤
      Real.sqrt ((Nat.card K : ℝ) ^ (d-1) * A.card * B.card) := by
  classical
  let w : ℙ K V → ℝ := fun a => if a ∈ A then 1 else 0
  have hw (b : ℙ K (Module.Dual K V)) :
      weightOnHyperplane w b = ∑ a ∈ A, incidenceEntry a b := by
    simp only [weightOnHyperplane, w, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_mem, Finset.univ_inter]
  have hsum : ∑ a, w a = (A.card : ℝ) := by
    simp [w, Finset.sum_ite_mem]
  have hsq : ∑ a, w a ^ 2 = (A.card : ℝ) := by
    simp [w, Finset.sum_ite_mem]
  have h := incidence_weighted_mixing_sq hdim hd w B
  rw [hsum, hsq] at h
  simp_rw [hw] at h
  rw [← incidences_eq_sum] at h
  simpa [mul_assoc, mul_left_comm, mul_comm] using Real.abs_le_sqrt h

theorem sparse_rectangle_size {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V)))
    (hsparse : (incidences A B : ℝ) ≤ (A.card : ℝ) * B.card / (4 * Nat.card K)) :
    (A.card : ℝ) * B.card ≤ 16 * (Nat.card K : ℝ) ^ (d+1) := by
  classical
  let q : ℝ := Nat.card K
  let v : ℝ := (A.card : ℝ) * B.card
  let p : ℝ := (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 1 / (2*q) ≤ p := density_lower hd
  have hpv := mul_le_mul_of_nonneg_right hp hv
  have hlow : v / (4*q) ≤ p*v - incidences A B := by
    change (incidences A B : ℝ) ≤ v / (4*q) at hsparse
    have he : (1 / (2*q)) * v = 2 * (v / (4*q)) := by field_simp; ring
    rw [he] at hpv
    linarith
  have hm : |(incidences A B : ℝ) - p*v| ≤ Real.sqrt (q^(d-1)*v) := by
    simpa only [p, q, v, mul_assoc] using incidence_mixing hdim hd A B
  have habs : |(incidences A B : ℝ) - p*v| = p*v - incidences A B := by
    rw [abs_of_nonpos (show (incidences A B : ℝ) - p*v ≤ 0 by
      have hnonneg : 0 ≤ v / (4*q) := by positivity
      linarith)]
    ring
  rw [habs] at hm
  have hs : v / (4*q) ≤ Real.sqrt (q^(d-1)*v) := hlow.trans hm
  have hs2 := (Real.le_sqrt (by positivity) (by positivity)).mp hs
  have he : (v / (4*q))^2 * (16*q^2) = v^2 := by field_simp; ring
  have hm2 := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ 16*q^2 by positivity)
  rw [he] at hm2
  have hexp : q^(d-1)*v*(16*q^2) = (16*q^(d+1))*v := by
    have hd' : d-1 + 2 = d+1 := by omega
    rw [← hd', pow_add]
    ring
  rw [hexp, pow_two] at hm2
  by_cases hv0 : v = 0
  · change v ≤ _
    rw [hv0]
    positivity
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hv (Ne.symm hv0))).mp hm2

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Bounds_DensityUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem incidence_rectangle_sqrt (hdim : finrank K V=5)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) (C : ℝ)
    (hC : 0 ≤ C) (hcap : (A.card:ℝ)*B.card ≤ C^2*(Nat.card K:ℝ)^5) :
    (incidences A B:ℝ) ≤ (C+1)*Real.sqrt ((Nat.card K:ℝ)^3*A.card*B.card) := by
  let q : ℝ := Nat.card K
  let z : ℝ := (A.card:ℝ)*B.card
  let s : ℝ := Real.sqrt (q^3*z)
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hz : 0 ≤ z := by dsimp [z];positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2=q^3*z := Real.sq_sqrt (by positivity)
  have hz2 : z^2 ≤ (C*q*s)^2 := by
    calc
      _ = z*z := by ring
      _ ≤ (C^2*q^5)*z := mul_le_mul_of_nonneg_right hcap hz
      _ = _ := by rw [mul_pow,mul_pow,hsq];ring
  have hzbound : z/q ≤ C*s := by
    apply (div_le_iff₀ hq).mpr
    simpa [mul_assoc,mul_left_comm,mul_comm] using (sq_le_sq₀ hz (by positivity)).mp hz2
  have hdens := mul_le_mul_of_nonneg_right (density_upper (K:=K) (d:=4) (by omega)) hz
  have hm := (abs_le.mp (incidence_mixing (d:=4) hdim (by omega) A B)).2
  change (incidences A B:ℝ)-(Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*A.card*B.card ≤ _ at hm
  have he : Real.sqrt ((Nat.card K:ℝ)^(4-1)*A.card*B.card)=s := by simp [s,q,z,mul_assoc]
  rw [he] at hm
  change (Q (Nat.card K) (4-1):ℝ)/Q (Nat.card K) 4*z ≤ 1/q*z at hdens
  have hdens' : (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*A.card*B.card ≤ z/q := by
    simpa [z,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hdens
  have hc : (incidences A B:ℝ) ≤ (C+1)*s := by nlinarith
  simpa [s,q,z,mul_assoc] using hc

theorem incidence_rectangle_log (hdim : finrank K V=5)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) (C : ℝ)
    (hC : 0 ≤ C) (hcap : (A.card:ℝ)*B.card ≤ C^2*(Nat.card K:ℝ)^5)
    (hA : 0 < A.card) (hB : 0 < B.card) (hI : 0 < incidences A B) :
    Real.log (incidences A B:ℝ) ≤ Real.log (C+1)+(3:ℝ)/2*Real.log (Nat.card K)+
      (Real.log (A.card:ℝ)+Real.log (B.card:ℝ))/2 := by
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hAr : (0:ℝ) < A.card := by exact_mod_cast hA
  have hBr : (0:ℝ) < B.card := by exact_mod_cast hB
  have hIr : (0:ℝ) < incidences A B := by exact_mod_cast hI
  have hs : (0:ℝ) < (Nat.card K:ℝ)^3*A.card*B.card := by positivity
  have hh := Real.log_le_log hIr (incidence_rectangle_sqrt hdim A B C hC hcap)
  rw [Real.log_mul (by linarith : C+1≠0) (Real.sqrt_pos.mpr hs).ne',Real.log_sqrt hs.le,
    Real.log_mul (mul_pos (pow_pos hq _) hAr).ne' hBr.ne',
    Real.log_mul (pow_pos hq _).ne' hAr.ne',Real.log_pow] at hh
  nlinarith

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Bounds_UpperSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

noncomputable def nextState (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b : ℙ K (Dual K V)) (y : ℙ K (Dual K V)) :=
  if Incident a y then b.submodule ⊔ W y else W y

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReverseMiss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

noncomputable def reverseMiss (p : Law β) (q : Law γ)
    (v : β → Module.Dual K V) (w : γ → V) : ℝ :=
  ∑ b,∑ c,if v b (w c)≠0 then p b*q c else 0

noncomputable def capturedEvent (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop)
    (a : α) (b : β) (c : γ) (y : δ) : Prop :=
  good a y ∧ reverseMiss (fiber p a) (fiber (swap q) y) v w≤(1/40000:ℝ) ∧
    v b∈core (K := K) (fiber p a) v (1/200) ∧
    w c∈core (K := K) (fiber (swap q) y) w (1/200)

end SharpRamseyFive.LowConflict

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma state_empty (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V)) (y : ℙ K (Dual K V)) :
    state a b ∅ y=⊥ := by
  apply le_antisymm ?_ bot_le
  apply iSup₂_le
  intro i hi
  exact False.elim (Finset.notMem_empty i hi)

lemma state_insert [DecidableEq ι] (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V))
    (E : Finset ι) (i : ι) (y : ℙ K (Dual K V)) :
    state a b (insert i E) y =
      (if Incident (a i) y then (b i).submodule else ⊥) ⊔ state a b E y := by
  simp only [state,Finset.mem_insert,iSup_or,iSup_sup_eq,iSup_iSup_eq_left]

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighPairVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def growSpan {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) : Submodule K (Dual K V) :=
  W ⊔ Marking.state (fun i=>(x i).1) (fun i=>(x i).2) Finset.univ y

def newHits (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V)) :
    Finset (SampleFlag (K:=K) (V:=V)) :=
  Finset.univ.filter fun z=>Incident z.1 y ∧ ¬z.2.submodule≤W

end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighSampleGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def sampleSpan {n t : ℕ} (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V))
    (y : ℙ K (Dual K V)) : Submodule K (Dual K V) :=
  runSamples (growSpan y) y.submodule x

end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_HighSampleDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def highDomain {n t : ℕ} (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V)) :
    Finset (SampleFlag (K:=K) (V:=V)) :=
  Finset.univ.filter fun z=>4≤finrank K (sampleSpan x z.2) ∧
    z.1.submodule≤(sampleSpan x z.2).dualCoannihilator

end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UnionMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.unionMarkingDecEq
def unionRecord (f : α → ι → β) (E₁ E₂ : α → Finset ι) (x : α) (i : ι) : Option β :=
  if i ∈ E₁ x ∪ E₂ x then some (f x i) else none

omit [Fintype α] [Fintype β] in
lemma unionRecord_present (f : α → ι → β) (E₁ E₂ : α → Finset ι) (x : α) :
    (∑ i,present (unionRecord f E₁ E₂ x i)) = ((E₁ x ∪ E₂ x).card:ℝ) := by
  have he (i : ι) : present (unionRecord f E₁ E₂ x i) =
      if i∈E₁ x ∪ E₂ x then (1:ℝ) else 0 := by
    simp only [unionRecord]
    split_ifs <;> rfl
  simp_rw [he]
  rw [Finset.sum_ite_mem,Finset.univ_inter]
  simp

theorem union_marking_entropy (p : Law (κ × α))
    (r : α → ι → RankTypes) (f : α → ι → β) (E₁ E₂ : α → Finset ι)
    (S : κ → ι → Finset β) (cap : ℝ) (hcap : 1 ≤ cap)
    (hS : ∀ c i,((S c i).card:ℝ) ≤ cap)
    (hsupp : ∀ c x,0<p (c,x) → ∀ i,f x i∈S c i) :
    (∑ c,first p c * entropy (pair (fiber p c)
      (unionMask r E₁ E₂) (unionRecord f E₁ E₂))) ≤
      (Fintype.card ι:ℝ)*Real.log 800 +
        (∑ x,second p x*((E₁ x ∪ E₂ x).card:ℝ))*Real.log cap := by
  have hh := conditional_marked_entropy p (unionMask r E₁ E₂)
    (unionRecord f E₁ E₂) S cap hcap hS (by
      intro c x hx i b hb
      dsimp [unionRecord] at hb
      split_ifs at hb with hi
      · cases hb
        exact hsupp c x hx i
      )
  apply hh.trans_eq
  simp only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Real.log_pow,unionRecord_present]
  have hlog : Real.log ((5*5*(2*2))*(2*2):ℝ)+Real.log 2=Real.log 800 := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  nlinarith

omit [Fintype α] [Fintype β] [Fintype ι] in
lemma unionRecord_decode_left (f : α → ι → β) (E₁ E₂ : α → Finset ι) (x : α) (i : ι) :
    (if i∈E₁ x then unionRecord f E₁ E₂ x i else none) =
      if i∈E₁ x then some (f x i) else none := by
  by_cases h : i∈E₁ x <;> simp [h,unionRecord]

omit [Fintype α] [Fintype β] [Fintype ι] in
lemma unionRecord_decode_right (f : α → ι → β) (E₁ E₂ : α → Finset ι) (x : α) (i : ι) :
    (if i∈E₂ x then unionRecord f E₁ E₂ x i else none) =
      if i∈E₂ x then some (f x i) else none := by
  by_cases h : i∈E₂ x <;> simp [h,unionRecord]

end

open scoped Classical BigOperators
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SubsetDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {ι β κ : Type*} [Fintype ι] [Fintype β] [Fintype κ]

def unionMessage (r : (ι → β) → ι → RankTypes)
    (E₁ E₂ : (ι → β) → Finset ι) (x : ι → β) : UnionTranscript ι β :=
  (unionMask r E₁ E₂ x,unionRecord id E₁ E₂ x)

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.unionPosteriorDecEq
omit [Fintype β] in
lemma unspecified_unionMessage (r : (ι → β) → ι → RankTypes)
    (E₁ E₂ : (ι → β) → Finset ι) (x : ι → β) :
    unspecified (unionMessage r E₁ E₂ x)=(E₁ x ∪ E₂ x)ᶜ := by
  ext i
  simp only [unspecified,Finset.mem_filter,Finset.mem_univ,true_and,unionMessage,
    unionRecord,Finset.mem_compl, id_eq]
  split_ifs <;> simp_all

omit [Fintype β] in
lemma unspecified_card (r : (ι → β) → ι → RankTypes)
    (E₁ E₂ : (ι → β) → Finset ι) (x : ι → β) :
    ((unspecified (unionMessage r E₁ E₂ x)).card:ℝ)+((E₁ x ∪ E₂ x).card:ℝ)=
      Fintype.card ι := by
  rw [unspecified_unionMessage]
  exact_mod_cast Finset.card_compl_add_card (E₁ x ∪ E₂ x)

lemma unionMessage_fixedOutside (p : Law (κ × (ι → β)))
    (r : (ι → β) → ι → RankTypes) (E₁ E₂ : (ι → β) → Finset ι)
    (c : κ) (m : UnionTranscript ι β)
    (hm : 0<first (withMessage p (unionMessage r E₁ E₂)) (c,m)) :
    FixedOutside (fiber (withMessage p (unionMessage r E₁ E₂)) (c,m)) (unspecified m) := by
  intro i hi
  have hn : m.2 i≠none := fun h=>hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  obtain ⟨b,hb⟩ := Option.ne_none_iff_exists'.mp hn
  refine ⟨b,?_⟩
  intro x hx
  have hmx := (fiber_withMessage_support p (unionMessage r E₁ E₂) c m hm x hx).2
  have hrec : unionRecord id E₁ E₂ x i=some b := by
    rw [←hb]
    exact congrFun (congrArg Prod.snd hmx) i
  dsimp [unionRecord] at hrec
  split_ifs at hrec
  exact Option.some.inj hrec

theorem union_deficit_bound (p : Law (κ × (ι → β)))
    (r : (ι → β) → ι → RankTypes) (E₁ E₂ : (ι → β) → Finset ι)
    (S : κ → ι → Finset β) (cap J : ℝ) (hcap : 1 ≤ cap)
    (hS : ∀ c i,((S c i).card:ℝ) ≤ cap)
    (hsupp : ∀ c x,0<p (c,x) → ∀ i,x i∈S c i) :
    mean (first (withMessage p (unionMessage r E₁ E₂)))
      (fun z=>activeDeficit (fiber (withMessage p (unionMessage r E₁ E₂)) z)
        (unspecified z.2) J) ≤
      (Fintype.card ι:ℝ)*J-entropy (second p)+entropy (first p)+
        (Fintype.card ι:ℝ)*Real.log 800+
        mean (second p) (fun x=>((E₁ x ∪ E₂ x).card:ℝ))*(Real.log cap-J) := by
  apply message_deficit_bound p (unionMessage r E₁ E₂) unspecified
    (fun x=>((E₁ x ∪ E₂ x).card:ℝ)) J (Real.log cap)
    ((Fintype.card ι:ℝ)*Real.log 800) (unspecified_card r E₁ E₂)
  exact union_marking_entropy p r id E₁ E₂ S cap hcap hS hsupp
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ConditionPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β γ κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ]

lemma withMessage_pair (p : Law α) (c : α→κ) (x : α→β) (M : β→γ) :
    withMessage (pair p c x) M=pair p (fun a=>(c a,M (x a))) x := by
  rw [withMessage,pair,map_comp]
  rfl
end

open scoped Classical BigOperators
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_Collisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
noncomputable section
variable {K V α β : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype α] [Fintype β] {n : ℕ}

def tupleMarginal (p : Law (Fin n → α × β)) (i : Fin n) : Law (α × β) :=
  map p (fun x => x i)

def tupleCapture (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V) (good : Fin n → Fin n → α → β → Prop)
    (i j : Fin n) (x : Fin n → α × β) : Prop :=
  i<j ∧ capturedEvent (tupleMarginal p i) (tupleMarginal p j) w v (good i j)
    (x i).1 (x i).2 (x j).1 (x j).2

def tupleCollision (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V) (good : Fin n → Fin n → α → β → Prop)
    (i j : Fin n) : ℝ := eventWeight p (tupleCapture p v w good i j)

omit [FiniteDimensional K V] in
lemma tupleCollision_nonneg (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V) (good : Fin n → Fin n → α → β → Prop)
    (i j : Fin n) : 0≤tupleCollision p v w good i j := eventWeight_nonneg _ _

end
end SharpRamseyFive.LowConflict

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ComponentLabelWitness
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

noncomputable def allTrunc (J : ℕ) (ω : Fin R × D → ℕ) : ℝ :=
  ∏ d : D, lineTrunc R J (fun r => ω (r,d))

end SharpRamseyFive.HighMoment
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_TruncatedTupleIntegrable
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

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatAtlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FlatAtlas

open Module
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma exists_spanning_code (A : Submodule K V) (n : ℕ) (hn : finrank K V≤n) :
    ∃f : Fin n→V,Submodule.span K (Set.range f)=A := by
  obtain ⟨f,hf,hs,-⟩ := Submodule.exists_fun_fin_finrank_span_eq K (A : Set V)
  have hs' : Submodule.span K (Set.range f)=A := hs.trans (Submodule.span_eq _)
  have hr : finrank K (Submodule.span K (A : Set V))≤n := (Submodule.finrank_le _).trans hn
  let g : Fin n→V := fun i=>if hi : i.val<finrank K (Submodule.span K (A : Set V)) then f ⟨i.val,hi⟩ else 0
  refine ⟨g,le_antisymm (Submodule.span_le.mpr ?_) ?_⟩
  · rintro v ⟨i,rfl⟩
    dsimp only [g]
    split_ifs with hi
    · exact hf _
    · exact A.zero_mem
  · apply hs'.symm.le.trans
    apply Submodule.span_mono
    rintro v ⟨i,rfl⟩
    refine ⟨i.castLE hr,?_⟩
    simp only [g,Fin.val_castLE,dite_eq_left i.prop]

noncomputable def flatCode (n : ℕ) (hn : finrank K V≤n) (A : Submodule K V) : Fin n→V :=
  (exists_spanning_code A n hn).choose

end SharpRamseyFive.FlatAtlas

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_IncidencesDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma incidences_eq_degrees (A : Finset (ℙ K V)) (Z : Finset (ℙ K (Dual K V))) :
    (incidences A Z:ℝ) = ∑ a∈A,((Z.filter fun y => Incident a y).card:ℝ) := by
  rw [incidences_eq_sum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [incidenceEntry,Finset.sum_boole]

theorem poor_joint_count (hdim : finrank K V=5)
    (A : Finset (ℙ K V)) (Z B : Finset (ℙ K (Dual K V)))
    (hpoor : ∀ a∈A,((Z.filter fun y => Incident a y).card:ℝ)≤(Z.card:ℝ)/(8*Nat.card K))
    (hB : B.card≤5*Z.card) :
    (incidences A B:ℝ)≤89*(Nat.card K:ℝ)^4 := by
  let q : ℝ:=Nat.card K
  have hq : 0<q := by
    dsimp [q]
    exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α := K))
  have hs : (incidences A Z:ℝ)≤(A.card:ℝ)*Z.card/(4*q) := by
    rw [incidences_eq_degrees]
    calc
      _ ≤ ∑ a∈A,(Z.card:ℝ)/(8*q) := Finset.sum_le_sum fun a ha => hpoor a ha
      _ = (A.card:ℝ)*Z.card/(8*q) := by simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hp := sparse_rectangle_size (d := 4) hdim (by decide) A Z hs
  have hB' : (B.card:ℝ)≤5*Z.card := by exact_mod_cast hB
  have hprod : (A.card:ℝ)*B.card≤80*q^5 := by
    have hh := mul_le_mul_of_nonneg_left hB' (show (0:ℝ)≤A.card by positivity)
    change (A.card:ℝ)*Z.card≤16*q^5 at hp
    nlinarith
  have hmix := incidence_mixing (d := 4) hdim (by decide) A B
  have hd := density_upper (K := K) (d := 4) (by decide)
  have hmain : ((Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4)*A.card*B.card≤80*q^4 := by
    calc
      _ ≤ (1/q)*((A.card:ℝ)*B.card) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd (show (0:ℝ)≤(A.card:ℝ)*B.card by positivity)
      _ ≤ (1/q)*(80*q^5) := mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by field_simp
  have hsqrt : Real.sqrt (q^3*A.card*B.card)≤9*q^4 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hp' := mul_le_mul_of_nonneg_left hprod (show 0≤q^3 by positivity)
    nlinarith [sq_nonneg (q^4)]
  have hupper := (abs_le.mp hmix).2
  change (incidences A B:ℝ)≤89*q^4
  change (incidences A B:ℝ)-((Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4)*A.card*B.card≤
    Real.sqrt (q^3*A.card*B.card) at hupper
  linarith

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ChooseLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (ℙ K (Dual K V))]

lemma chooseLevel_le (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) :
    chooseLevel W r ≤ r := (exists_level W r).choose_spec.1

lemma chooseLevel_large (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) :
    (upperSet W r).card≤(r+1)*(levelSet W (chooseLevel W r)).card :=
  (exists_level W r).choose_spec.2.2

lemma chooseLevel_nonempty (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (b : ℙ K (Dual K V)) :
    (levelSet W (chooseLevel W (finrank K (W b)))).Nonempty := by
  have hb : b∈upperSet W (finrank K (W b)) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩
  have hc := chooseLevel_large W (finrank K (W b))
  have hn := Finset.card_pos.mpr ⟨b,hb⟩
  apply Finset.card_pos.mp
  by_contra h
  have hh : (levelSet W (chooseLevel W (finrank K (W b)))).card=0 := by omega
  rw [hh,mul_zero] at hc
  omega

end

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem popular_joint_count (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) (hlr : l ≤ r) (hr : r≤4) (hZ : (levelSet W l).Nonempty)
    (B : Finset (ℙ K (Dual K V)))
    (hB : ∀ b∈B,finrank K (W b)=r ∧
      ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) b) :
    (((Finset.univ ×ˢ B).filter fun ab : ℙ K V × ℙ K (Dual K V) =>
      ab.1.submodule≤(W ab.2).dualCoannihilator).card:ℝ)≤64*(Nat.card K:ℝ)^4 := by
  have hcard := popular_count W (levelSet W l) hZ l (fun y hy => (Finset.mem_filter.mp hy).2)
  have hsub : B⊆Finset.univ.filter fun b : ℙ K (Dual K V) =>
      ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) b := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hB b hb).2⟩
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hbcard : (B.card:ℝ)≤32*(Nat.card K:ℝ)^r := by
    have hb : (B.card:ℝ)≤(Finset.univ.filter fun b : ℙ K (Dual K V) =>
      ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) b).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hb.trans (hcard.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hlr) (by norm_num)))
  rw [←Finset.sum_boole,Finset.sum_product,Finset.sum_comm]
  calc
    _ ≤ ∑ b∈B,2*(Nat.card K:ℝ)^(4-r) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [Finset.sum_boole]
      exact coannihilator_card_bound hdim (W b) r (hB b hb).1 hr
    _ = (B.card:ℝ)*(2*(Nat.card K:ℝ)^(4-r)) := by simp
    _ ≤ (32*(Nat.card K:ℝ)^r)*(2*(Nat.card K:ℝ)^(4-r)) :=
      mul_le_mul_of_nonneg_right hbcard (by positivity)
    _ = _ := by
      have hp : (Nat.card K:ℝ)^r*(Nat.card K:ℝ)^(4-r)=(Nat.card K:ℝ)^4 := by
        rw [←pow_add,Nat.add_sub_of_le hr]
      nlinarith [hp]

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] in
lemma scanSet_subset (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (n : ℕ) :
    scanSet a b q n⊆Finset.range n := by
  induction n with
  | zero => simp [scanSet]
  | succ n ih =>
    rw [scanSet]
    split_ifs
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (ih hi)))
    · exact Finset.Subset.trans ih (Finset.range_mono (Nat.le_succ n))

omit [FiniteDimensional K V] in
lemma scanState_update (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) (he : Expensive (scanState a b q n) (a n) (b n) q) :
    scanState a b q (n+1)=nextState (scanState a b q n) (a n) (b n) := by
  funext y
  change state a b (scanSet a b q (n+1)) y=_
  change Expensive (state a b (scanSet a b q n)) (a n) (b n) q at he
  rw [scanSet,ite_eq_left he,state_insert]
  unfold nextState
  split_ifs
  · rfl
  · exact bot_sup_eq _

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def popularDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) : Finset (ℙ K V × ℙ K (Dual K V)) :=
  ((Finset.univ : Finset (ℙ K V)) ×ˢ (Finset.univ.filter fun b : ℙ K (Dual K V) =>
    finrank K (W b)=r ∧ ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) b)).filter
    fun ab => ab.1.submodule≤(W ab.2).dualCoannihilator

noncomputable def poorDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) : Finset (ℙ K V × ℙ K (Dual K V)) :=
  ((Finset.univ.filter fun a : ℙ K V =>
    (((levelSet W l).filter fun y => Incident a y).card:ℝ)≤((levelSet W l).card:ℝ)/(8*Nat.card K)) ×ˢ
      upperSet W r).filter fun ab => Incident ab.1 ab.2

theorem popularDomain_card (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r l : ℕ) (hlr : l ≤ r) (hr : r≤4)
    (hZ : (levelSet W l).Nonempty) :
    ((popularDomain W r l).card:ℝ)≤64*(Nat.card K:ℝ)^4 :=
  popular_joint_count hdim W r l hlr hr hZ _ (fun _ hb => (Finset.mem_filter.mp hb).2)

theorem poorDomain_card (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) (hr : r≤4) :
    ((poorDomain W r (chooseLevel W r)).card:ℝ)≤89*(Nat.card K:ℝ)^4 := by
  apply poor_joint_count hdim _ _ _ (fun a ha => (Finset.mem_filter.mp ha).2)
  exact (chooseLevel_large W r).trans (Nat.mul_le_mul_right _ (by omega))

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in

lemma scan_annihilator (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) : (a n).submodule≤(scanState a b q n (b n)).dualCoannihilator := by
  rw [←Submodule.le_dualAnnihilator_iff_le_dualCoannihilator]
  apply iSup₂_le
  intro i hi
  split_ifs with hab
  · exact (incident_iff_dualAnnihilator _ _).mp
      (hF i n (Finset.mem_range.mp (scanSet_subset a b q n hi)) hn hab)
  · exact bot_le

omit [Finite K] [FiniteDimensional K V] in

theorem cheap_mem_domains (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (N : ℕ)
    (hflag : ∀ n<N,Incident (a n) (b n))
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N)
    (hc : ¬Expensive (scanState a b (Nat.card K) n) (a n) (b n) (Nat.card K)) :
    let W:=scanState a b (Nat.card K) n
    let r:=finrank K (W (b n))
    let l:=chooseLevel W r
    (a n,b n)∈popularDomain W r l ∨ (a n,b n)∈poorDomain W r l := by
  dsimp only
  let W:=scanState a b (Nat.card K) n
  let r:=finrank K (W (b n))
  let l:=chooseLevel W r
  change (a n,b n)∈popularDomain W r l ∨ (a n,b n)∈poorDomain W r l
  by_cases hp : ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) (b n)
  · left
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,hp⟩⟩
    · exact scan_annihilator a b (Nat.card K) N hF hn
  · right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hflag n hn⟩
    · apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      apply le_of_not_gt
      intro hpoor
      apply hc
      exact ⟨lt_of_not_ge hp,hpoor⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanRecord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def decodeState (record : ℕ → Option (ℙ K V × ℙ K (Dual K V))) :
    ℕ → ℙ K (Dual K V) → Submodule K (Dual K V)
  | 0 => fun _ => ⊥
  | n+1 => match record n with
    | none => decodeState record n
    | some ab => nextState (decodeState record n) ab.1 ab.2

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma decode_scanRecord (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : decodeState (scanRecord a b q) n=scanState a b q n := by
  induction n with
  | zero => funext y; exact (state_empty a b y).symm
  | succ n ih =>
    rw [decodeState,scanRecord]
    split_ifs with he
    · simp only [ih]
      exact (scanState_update a b q n he).symm
    · simp only [ih]
      change state a b (scanSet a b q n)=state a b (scanSet a b q (n+1))
      change ¬Expensive (state a b (scanSet a b q n)) (a n) (b n) q at he
      rw [scanSet,ite_eq_right he]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma decodeState_congr_prefix (record record' : ℕ → Option (ℙ K V × ℙ K (Dual K V)))
    (n : ℕ) (h : ∀ i<n,record i=record' i) : decodeState record n=decodeState record' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [decodeState,decodeState,h n (Nat.lt_succ_self n),ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

noncomputable def rankMask (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : Fin 5 := ⟨finrank K (scanState a b q n (b n))%5,Nat.mod_lt _ (by decide)⟩

noncomputable def cheapDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) :
    Finset (ℙ K V × ℙ K (Dual K V)) :=
  if (levelSet W (chooseLevel W r.val)).Nonempty then
    popularDomain W r.val (chooseLevel W r.val) ∪ poorDomain W r.val (chooseLevel W r.val)
  else ∅

variable [Finite K]

theorem cheapDomain_card (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) :
    ((cheapDomain W r).card:ℝ)≤153*(Nat.card K:ℝ)^4 := by
  unfold cheapDomain
  split_ifs with hz
  · have hp:=popularDomain_card hdim W r.val (chooseLevel W r.val)
      (chooseLevel_le W r.val) (by omega) hz
    have hs:=poorDomain_card hdim W r.val (by omega)
    have hu : (((popularDomain W r.val (chooseLevel W r.val) ∪
        poorDomain W r.val (chooseLevel W r.val)).card):ℝ)≤
        (popularDomain W r.val (chooseLevel W r.val)).card+
          (poorDomain W r.val (chooseLevel W r.val)).card := by
      exact_mod_cast Finset.card_union_le _ _
    linarith
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanRecordPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section

variable {β : Type*} [Nonempty β] {N : ℕ}
attribute [local instance] OAI.SharpRamseyFive.Marking.finiteMarkingDecEq
lemma extendTuple_at (f : Fin N → β) (i : Fin N) : extendTuple f i.val=f i := by
  simp only [extendTuple,dite_eq_left i.isLt]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma tupleIncident_extend {f : Fin N → FlagPair K V} (h : TupleIncident f) :
    ∀ i,i<N → Incident (tupleFirst f i) (tupleSecond f i) := by
  intro i hi
  simpa only [tupleFirst,tupleSecond,extendTuple,dite_eq_left hi] using h ⟨i,hi⟩

def finiteRank (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :=
  rankMask (tupleFirst f) (tupleSecond f) q i.val

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma finiteRecord_value (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :
    finiteRecord f q i = if i∈expensiveSet f q then some (f i) else none := by
  simp only [expensiveSet,finiteRecord,scanRecord]
  split_ifs with h <;> simp_all [tupleFirst,tupleSecond,extendTuple_at]

def finiteDecodeRecord (record : Fin N → Option (FlagPair K V)) (n : ℕ) :=
  if h:n<N then record ⟨n,h⟩ else none

def finiteDomain (record : Fin N → Option (FlagPair K V)) (r : Fin N → Fin 5)
    (i : Fin N) : Finset (FlagPair K V) :=
  cheapDomain (decodeState (finiteDecodeRecord record) i.val) (r i)

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma finite_decode (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :
    decodeState (finiteDecodeRecord (finiteRecord f q)) i.val =
      decodeState (scanRecord (tupleFirst f) (tupleSecond f) q) i.val := by
  apply decodeState_congr_prefix
  intro j hj
  simp only [finiteDecodeRecord,dite_eq_left (hj.trans i.isLt),finiteRecord]

variable [Finite K]
omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] in
theorem finiteDomain_card (hdim : finrank K V=5)
    (record : Fin N → Option (FlagPair K V)) (r : Fin N → Fin 5) (i : Fin N) :
    ((finiteDomain record r i).card:ℝ)≤153*(Nat.card K:ℝ)^4 :=
  cheapDomain_card hdim _ _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_TwoScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
local instance typedScanDecEq_re9819f_1 (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] {N : ℕ}

def typedDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) (popular : Bool) : Finset (FlagPair K V) :=
  if (levelSet W (chooseLevel W r.val)).Nonempty then
    if popular then popularDomain W r.val (chooseLevel W r.val)
      else poorDomain W r.val (chooseLevel W r.val)
  else ∅

omit [FiniteDimensional K V] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] in
lemma typedDomain_subset (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) (popular : Bool) : typedDomain W r popular⊆cheapDomain W r := by
  unfold typedDomain cheapDomain
  split_ifs <;> simp only [Finset.subset_union_left,Finset.subset_union_right,
    Finset.Subset.refl]

def finiteTypedDomain (record : Fin N → Option (FlagPair K V))
    (r : Fin N → Fin 5) (popular : Fin N → Bool) (i : Fin N) :=
  typedDomain (decodeState (finiteDecodeRecord record) i.val) (r i) (popular i)

def finitePopular (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) : Bool :=
  let W:=decodeState (finiteDecodeRecord (finiteRecord f q)) i.val
  let r:=finiteRank f q i
  decide (f i∈popularDomain W r.val (chooseLevel W r.val))

variable [Finite K]

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] in
lemma finiteTypedDomain_card (hdim : finrank K V=5)
    (record : Fin N → Option (FlagPair K V)) (r : Fin N → Fin 5)
    (popular : Fin N → Bool) (i : Fin N) :
    ((finiteTypedDomain record r popular i).card:ℝ)≤153*(Nat.card K:ℝ)^4 := by
  have h : ((finiteTypedDomain record r popular i).card:ℝ)≤
      ((finiteDomain record r i).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (typedDomain_subset _ _ _)
  exact h.trans (finiteDomain_card hdim record r i)

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
attribute [local instance] OAI.SharpRamseyFive.Marking.concreteMarkingDecEq
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N : ℕ}

def twoScanTypes (f : Fin N → FlagPair K V) (i : Fin N) : RankTypes :=
  ((finiteRank f (Nat.card K) i,finiteRank (reverseTuple f) (Nat.card K) i.rev),
    finitePopular f (Nat.card K) i,finitePopular (reverseTuple f) (Nat.card K) i.rev)

def markingMessage (f : Fin N → FlagPair K V) : UnionTranscript (Fin N) (FlagPair K V) :=
  unionMessage twoScanTypes (fun f=>expensiveSet f (Nat.card K))
    (fun f=>reverseExpensive f (Nat.card K)) f

def forwardRecord (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  if (m.1 i).2.1 then m.2 i else none

def backwardRecord (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  (if (m.1 i.rev).2.2 then m.2 i.rev else none).map swapFlag

lemma backwardRecord_marking (f : Fin N → FlagPair K V) :
    backwardRecord (markingMessage f)=finiteRecord (reverseTuple f) (Nat.card K) := by
  funext i
  simp only [backwardRecord,markingMessage,unionMessage,unionMask,decide_eq_true_eq]
  rw [unionRecord_decode_right id (fun f=>expensiveSet f (Nat.card K))
    (fun f=>reverseExpensive f (Nat.card K)) f i.rev,finiteRecord_value]
  simp only [mem_reverseExpensive,Fin.rev_rev]
  split_ifs <;> rfl

def forwardDomain (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  finiteTypedDomain (forwardRecord m) (fun j=>(m.1 j).1.1.1) (fun j=>(m.1 j).1.2.1) i

def backwardDomain (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  finiteTypedDomain (backwardRecord m) (fun j=>(m.1 j.rev).1.1.2)
    (fun j=>(m.1 j.rev).1.2.2) i.rev

def markingDomain (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  forwardDomain m i ∩ (backwardDomain m i).map swapFlag.symm.toEmbedding

variable [Finite K]
omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
lemma markingDomain_card (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    ((markingDomain m i).card:ℝ)≤153*(Nat.card K:ℝ)^4 := by
  have h : ((markingDomain m i).card:ℝ)≤((forwardDomain m i).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_left)
  exact h.trans (finiteTypedDomain_card hdim _ _ _ _)

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

attribute [local instance] OAI.SharpRamseyFive.Marking.markingEndpointsPointDecEq
attribute [local instance] OAI.SharpRamseyFive.Marking.markingEndpointsDualDecEq
local instance markingEndpointsPairDecEq_re9819f_1 : DecidableEq (FlagPair K V) := Classical.decEq _
omit [Finite K] [FiniteDimensional K V] in
lemma mem_popularDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) (z : FlagPair K V) : z∈popularDomain W r l ↔
    finrank K (W z.2)=r ∧ ((levelSet W l).card:ℝ)/(16*Nat.card K)≤
      memberships W (levelSet W l) z.2 ∧ z.1.submodule≤(W z.2).dualCoannihilator := by
  simp only [popularDomain,Finset.mem_filter,Finset.mem_product,Finset.mem_univ,true_and]
  tauto

omit [Finite K] [FiniteDimensional K V] in
lemma mem_poorDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) (z : FlagPair K V) : z∈poorDomain W r l ↔
    (((levelSet W l).filter fun y=>Incident z.1 y).card:ℝ)≤
      ((levelSet W l).card:ℝ)/(8*Nat.card K) ∧ finrank K (W z.2) ≤ r ∧
      Incident z.1 z.2 := by
  simp only [poorDomain,Finset.mem_filter,Finset.mem_product,Finset.mem_univ,
    true_and,upperSet]
  tauto

omit [FiniteDimensional K V] in
lemma typed_popular_second (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) :
    (((typedDomain W r true).image Prod.snd).card:ℝ)≤32*(Nat.card K:ℝ)^r.val := by
  unfold typedDomain
  simp only [↓reduceIte]
  split_ifs with hz
  · have hsub : (popularDomain W r.val (chooseLevel W r.val)).image Prod.snd ⊆
        Finset.univ.filter fun b : ℙ K (Dual K V)=>
          ((levelSet W (chooseLevel W r.val)).card:ℝ)/(16*Nat.card K)≤
            memberships W (levelSet W (chooseLevel W r.val)) b := by
      intro b hb
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_popularDomain _ _ _ _).mp hz |>.2.1⟩
    have hc := popular_count W _ hz (chooseLevel W r.val)
      (fun y hy=>(Finset.mem_filter.mp hy).2)
    have hc' : ((((popularDomain W r.val (chooseLevel W r.val)).image Prod.snd).card):ℝ)≤
        32*(Nat.card K:ℝ)^(chooseLevel W r.val) :=
      (show _ ≤ (_:ℝ) from by exact_mod_cast Finset.card_le_card hsub).trans hc
    exact hc'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by exact_mod_cast (Finite.one_lt_card (α:=K)).le)
        (chooseLevel_le W r.val)) (by norm_num))
  · simp only [Finset.image_empty,Finset.card_empty,Nat.cast_zero]
    positivity

omit [Finite K] [FiniteDimensional K V] in
lemma typed_poor_second (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) :
    (((typedDomain W r false).image Prod.snd).card:ℝ)≤
      5*((levelSet W (chooseLevel W r.val)).card:ℝ) := by
  unfold typedDomain
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs with hz
  · have hsub : (poorDomain W r.val (chooseLevel W r.val)).image Prod.snd⊆upperSet W r.val := by
      intro b hb
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((mem_poorDomain _ _ _ _).mp hz).2.1⟩
    have hc : ((upperSet W r.val).card:ℝ)≤5*((levelSet W (chooseLevel W r.val)).card:ℝ) := by
      exact_mod_cast (chooseLevel_large W r.val).trans (Nat.mul_le_mul_right _ (by omega))
    exact (show _ ≤ (_:ℝ) from by exact_mod_cast Finset.card_le_card hsub).trans hc
  · simp only [Finset.image_empty,Finset.card_empty,Nat.cast_zero]
    positivity

lemma typed_poor_first (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) :
    (((typedDomain W r false).image Prod.fst).card:ℝ)*
      ((levelSet W (chooseLevel W r.val)).card:ℝ)≤16*(Nat.card K:ℝ)^5 := by
  let A := (typedDomain W r false).image Prod.fst
  let Z := levelSet W (chooseLevel W r.val)
  apply sparse_rectangle_size (d:=4) hdim (by decide) A Z
  rw [incidences_eq_degrees]
  have hpoor (a : ℙ K V) (ha : a∈A) :
      ((Z.filter fun y=>Incident a y).card:ℝ)≤(Z.card:ℝ)/(8*Nat.card K) := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    unfold typedDomain at hz
    simp only [Bool.false_eq_true, ↓reduceIte] at hz
    split_ifs at hz with hn
    · have hh : z∈poorDomain W r.val (chooseLevel W r.val) := hz
      exact ((mem_poorDomain W r.val (chooseLevel W r.val) z).mp hh).1
    · exact False.elim (Finset.notMem_empty _ hz)
  calc
    _ ≤ ∑ _a∈A,(Z.card:ℝ)/(8*Nat.card K) := Finset.sum_le_sum hpoor
    _ = (A.card:ℝ)*Z.card/(8*Nat.card K) := by simp; ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by
      have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
      positivity) (by nlinarith [Nat.cast_nonneg (α:=ℝ) (Nat.card K)])

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

attribute [local instance] OAI.SharpRamseyFive.Marking.clampedPointDecEq
attribute [local instance] OAI.SharpRamseyFive.Marking.clampedDualDecEq
local instance clampedPairDecEq_re9819f_1 : DecidableEq (FlagPair K V) := Classical.decEq _
omit [Finite K] [FiniteDimensional K V] in
lemma typedDomain_level_nonempty (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) (pop : Bool) (h : (typedDomain W r pop).Nonempty) :
    (levelSet W (chooseLevel W r.val)).Nonempty := by
  by_contra hn
  rw [typedDomain, ite_eq_right hn] at h
  exact Finset.not_nonempty_empty h

theorem typed_poor_reciprocal (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5)
    (h : (typedDomain W r false).Nonempty) :
    let u:=clampParameter (Nat.card K) (levelSet W (chooseLevel W r.val)).card
    (((typedDomain W r false).image Prod.fst).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u) ∧
    (((typedDomain W r false).image Prod.snd).card:ℝ)≤32*Real.exp u := by
  have hq : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have hcA : Fintype.card (ℙ K V)≤2*Nat.card K^4 := projective_card_le_two_pow hdim hq
  have hcB : Fintype.card (ℙ K (Dual K V))≤2*Nat.card K^4 :=
    projective_card_le_two_pow (by simpa using hdim) hq
  apply clamped_reciprocal_caps (by exact_mod_cast (show 1≤Nat.card K by omega))
    (by exact_mod_cast (typedDomain_level_nonempty W r false h).card_pos) (by positivity) (by positivity)
  · exact_mod_cast (Finset.card_le_univ _).trans hcA
  · exact_mod_cast (Finset.card_le_univ _).trans hcB
  · exact typed_poor_first hdim W r
  · exact typed_poor_second W r

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

local instance bandsPointDecEq_re9819f_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance bandsDualDecEq_re9819f_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance bandsPairDecEq_re9819f_1 : DecidableEq (FlagPair K V) := Classical.decEq _
omit [Finite K] [Fintype (ℙ K V)] in
lemma zero_level_memberships (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (b : ℙ K (Dual K V)) : memberships W (levelSet W 0) b=0 := by
  unfold memberships
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hy,hb⟩:=Finset.mem_filter.mp hy
  have hw : finrank K (W y)=0 := (Finset.mem_filter.mp hy).2
  have hz : W y=⊥ := Submodule.finrank_eq_zero.mp hw
  rw [hz] at hb
  have he := b.finrank_submodule
  rw [le_antisymm hb bot_le] at he
  simp at he

lemma typed_popular_rank_pos (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r : Fin 5) (h : (typedDomain W r true).Nonempty) : 1 ≤ r.val := by
  by_contra hh
  have hr : r.val=0 := by omega
  have hl : chooseLevel W r.val=0 := by have := chooseLevel_le W r.val;omega
  have hn:=typedDomain_level_nonempty W r true h
  obtain ⟨z,hz⟩:=h
  unfold typedDomain at hz
  rw [ite_eq_left hn] at hz
  simp only [ite_true] at hz
  have hb:=((mem_popularDomain _ _ _ _).mp hz).2.1
  rw [hl,zero_level_memberships,Nat.cast_zero] at hb
  have hp : (0:ℝ)<(levelSet W 0).card := by exact_mod_cast (hl ▸ hn).card_pos
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  exact (div_pos hp (by positivity)).not_ge hb

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalLowConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {n : ℕ}

def reciprocalGood (p : Law (Fin n→FlagPair K V)) (u : Fin n→ℝ) (s : ℝ)
    (i j : Fin n) (a : ℙ K V) (b : ℙ K (Dual K V)) : Prop :=
  a∈goodFirstEndpoints (tupleMarginal p i) (32*Real.exp (5*Real.log (Nat.card K)-u i))
    ((Nat.card K:ℝ)^4) s ∧
  b∈goodFirstEndpoints (swap (tupleMarginal p j)) (32*Real.exp (u j))
    ((Nat.card K:ℝ)^4) s ∧ Incident a b

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section

def windowCoordinates {w r : ℕ} : Slots w r→Fin w×Fin (4*r)
  | Sum.inl ((v,false),a) => (v,⟨a.val,by omega⟩)
  | Sum.inl ((v,true),a) => (v,⟨3*r+a.val,by omega⟩)
  | Sum.inr (v,t) => (v,⟨r+t.val,by omega⟩)

lemma windowCoordinates_injective {w r : ℕ} : Function.Injective (@windowCoordinates w r) := by
  intro x y he
  have hw := congrArg (fun z=>z.1) he
  have hp := congrArg (fun z=>z.2.val) he
  rcases x with ⟨⟨v,b⟩,a⟩|⟨v,t⟩ <;> rcases y with ⟨⟨u,c⟩,d⟩|⟨u,s⟩
  · cases b <;> cases c
    all_goals simp only [windowCoordinates] at hw hp
    · subst u
      have : a=d := Fin.ext (by omega)
      subst d
      rfl
    · omega
    · omega
    · subst u
      have : a=d := Fin.ext (by omega)
      subst d
      rfl
  · cases b <;> simp only [windowCoordinates] at hw hp <;> omega
  · cases c <;> simp only [windowCoordinates] at hw hp <;> omega
  · simp only [windowCoordinates] at hw hp
    subst u
    have : t=s := Fin.ext (by omega)
    subst s
    rfl

def slotEmbedding {w r : ℕ} : Slots w r↪Fin (w*(4*r)) :=
  ⟨fun i=>finProdFinEquiv (windowCoordinates i),
    finProdFinEquiv.injective.comp windowCoordinates_injective⟩

lemma card_slots (w r : ℕ) : Fintype.card (Slots w r)=w*(4*r) := by
  simp only [Slots,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  ring

lemma slotEmbedding_bijective (w r : ℕ) : Function.Bijective (@slotEmbedding w r) := by
  have hc : Fintype.card (Slots w r)=Fintype.card (Fin (w*(4*r))) := by
    rw [card_slots,Fintype.card_fin]
  exact (Fintype.bijective_iff_injective_and_card (@slotEmbedding w r)).mpr
    ⟨slotEmbedding.injective,hc⟩

end
end SharpRamseyFive.Windows

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrderedReciprocalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
noncomputable def slotEquiv (w r : ℕ) : Slots w r≃Fin (w*(4*r)) :=
  Equiv.ofBijective slotEmbedding (slotEmbedding_bijective w r)
end SharpRamseyFive.Windows
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

def orderedCollision (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s : ℝ)
    (i j : I) : ℝ :=
  let q:=orderedLaw p e
  let good:=reciprocalGood q (u∘e.symm) s
  tupleCollision q Projectivization.rep Projectivization.rep good (e i) (e j)+
    tupleCollision q Projectivization.rep Projectivization.rep good (e j) (e i)
omit [Finite K] [FiniteDimensional K V] in
lemma orderedCollision_nonneg (p : Law (I→FlagPair K V)) (e : I≃Fin n)
    (u : I→ℝ) (s : ℝ) (i j : I) : 0≤orderedCollision p e u s i j :=
  add_nonneg (tupleCollision_nonneg ..) (tupleCollision_nonneg ..)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowReadiness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section
variable {κ β : Type} [Fintype κ] [Fintype β] {w r n rem : ℕ} [Nonempty (Fin r)]

local instance readinessBlockDE_re9819f_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.readinessIndexDE
def windowReady (bad : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r) (v : Fin w) (t : Fin (2*r)) : Prop :=
  bad (Sum.inr (v,t))=0 ∧ ∀ b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_SelectedExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
open FiniteEntropy
noncomputable section
variable {α Ω : Type*} [Fintype α] [Fintype Ω]

lemma mem_occurrences_iff {n l : ℕ} (s : Fin n→α) (f : Fin l→α) :
    s∈occurrences f ↔ ∃ e:Fin l ↪o Fin n,∀ i,s (e i)=f i := by
  constructor
  · intro h
    obtain ⟨I,_,hI⟩:=Finset.mem_biUnion.mp h
    exact ⟨I.val.orderEmbOfFin I.property,(Finset.mem_filter.mp hI).2⟩
  · rintro ⟨e,he⟩
    let I : Finset (Fin n) := Finset.univ.map e.toEmbedding
    have hI : I.card=l := by simp [I]
    have hei : I.orderEmbOfFin hI=e := by
      symm
      apply Finset.orderEmbOfFin_unique' hI
      intro j
      simp [I]
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨I,hI⟩,Finset.mem_univ _,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j=>by rw [hei];exact he j⟩

lemma occurrences_trans {n m l : ℕ} (s : Fin n→α) (f : Fin m→α) (g : Fin l→α)
    (hf : s∈occurrences f) (hg : f∈occurrences g) : s∈occurrences g := by
  obtain ⟨e,he⟩:=(mem_occurrences_iff s f).mp hf
  obtain ⟨d,hd⟩:=(mem_occurrences_iff f g).mp hg
  apply (mem_occurrences_iff s g).mpr
  exact ⟨d.trans e,fun i=>(he (d i)).trans (hd i)⟩

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_StageState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
open FiniteEntropy
noncomputable section
variable {α β γ Ω κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω] [Fintype κ]

lemma sourceSequence_occurs {n l : ℕ} (reverse : Bool) (view : β→α)
    (x : Fin n→β) (y : Fin l→β) (h : x∈occurrences y) :
    sourceSequence reverse view x∈occurrences (sourceSequence reverse view y) := by
  obtain ⟨e,he⟩:=(mem_occurrences_iff x y).mp h
  apply (mem_occurrences_iff _ _).mpr
  cases reverse
  · exact ⟨e,fun i=>congrArg view (he i)⟩
  · refine ⟨reverseEmbedding e,fun i=>?_⟩
    change view (x ((e i.rev).rev).rev)=view (y i.rev)
    rw [Fin.rev_rev,he]

namespace SelectedStream
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

def restrict (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (E : Finset Ω) (hE : 0<eventMass S.law E) :
    SelectedStream (Ω:=Ω) (β:=β) N n admissible where
  law := conditionOn S.law E hE
  stream := S.stream
  tuple := S.tuple
  reverse := S.reverse
  view := S.view
  selected := fun a ha=>S.selected a (conditionOn_positive S.law E hE a ha).2
  good := fun a ha=>S.good a (conditionOn_positive S.law E hE a ha).2
  density := S.density/eventMass S.law E
  density_nonneg := div_nonneg S.density_nonneg hE.le
  density_bound := by
    intro s
    apply (map_conditionOn_le S.law E hE S.stream s).trans
    have hh:=div_le_div_of_nonneg_right (S.density_bound s) hE.le
    convert hh using 1 <;> first | rfl | ring

def extract {l : ℕ} (hl : l≤n) (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (positions : Ω→Finset (Fin n)) : SelectedStream (Ω:=Ω) (β:=β) N l admissible where
  law := S.law
  stream := S.stream
  tuple := fun a=>retainedTuple hl (S.tuple a) (positions a)
  reverse := S.reverse
  view := S.view
  selected := by
    intro a ha
    exact occurrences_trans _ _ _ (S.selected a ha)
      (sourceSequence_occurs S.reverse S.view _ _ (retainedTuple_occurs hl _ _))
  good := S.good
  density := S.density
  density_nonneg := S.density_nonneg
  density_bound := S.density_bound

end SelectedStream
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingClassDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] {N : ℕ}

attribute [local instance] OAI.SharpRamseyFive.Marking.classDomainPointDE
attribute [local instance] OAI.SharpRamseyFive.Marking.classDomainDualDE
attribute [local instance] OAI.SharpRamseyFive.Marking.classDomainDualDualDE
def reversedMarkingDomain (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  (markingDomain m i).map swapFlag.toEmbedding

omit [Finite K] in
lemma markingDomain_forward (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    markingDomain m i  ⊆  forwardDomain m i := Finset.inter_subset_left

omit [Finite K] in
lemma markingDomain_backward (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    reversedMarkingDomain m i  ⊆  backwardDomain m i := by
  intro z hz
  obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hz
  obtain ⟨y,hy,he⟩:=Finset.mem_map.mp (Finset.mem_inter.mp hx).2
  have hh : y=swapFlag x := by
    simpa only [Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using congrArg swapFlag he
  exact hh ▸ hy

omit [Finite K] in
lemma reversedDomain_first_card (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    ((reversedMarkingDomain m i).image Prod.fst).card=((markingDomain m i).image Prod.snd).card := by
  congr 1
  ext b
  simp only [reversedMarkingDomain,Finset.mem_image,Finset.mem_map]
  aesop

omit [Finite K] in
lemma reversedDomain_second_card (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    ((reversedMarkingDomain m i).image Prod.snd).card=((markingDomain m i).image Prod.fst).card := by
  have he : (reversedMarkingDomain m i).image Prod.snd=
      ((markingDomain m i).image Prod.fst).map bidualPoint.toEmbedding := by
    ext b
    simp only [reversedMarkingDomain,Finset.mem_image,Finset.mem_map]
    aesop
  rw [he,Finset.card_map]

def ForwardCaps (D : Finset (FlagPair K V)) (u : ℝ) : Prop :=
  ((D.image Prod.fst).card:ℝ) ≤ 32*Real.exp (5*Real.log (Nat.card K)-u) ∧
  ((D.image Prod.snd).card:ℝ) ≤ 32*Real.exp u

def ReverseCaps (D : Finset (FlagPair K V)) (u : ℝ) : Prop :=
  ((D.image Prod.snd).card:ℝ) ≤ 32*Real.exp (5*Real.log (Nat.card K)-u) ∧
  ((D.image Prod.fst).card:ℝ) ≤ 32*Real.exp u

lemma marking_poor_forward (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) (hp : (m.1 i).1.2.1=false) :
    ∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ForwardCaps (markingDomain m i) u := by
  let W:=decodeState (finiteDecodeRecord (forwardRecord m)) i.val
  let r:=(m.1 i).1.1.1
  have hs : markingDomain m i ⊆ typedDomain W r false := by
    simpa only [forwardDomain,finiteTypedDomain,hp] using markingDomain_forward m i
  have ht:=(typed_poor_reciprocal hdim W r (hne.mono hs))
  let u:=clampParameter (Nat.card K) (levelSet W (chooseLevel W r.val)).card
  have hb:=clampParameter_bounds (M:=(levelSet W (chooseLevel W r.val)).card)
    (show (1:ℝ) ≤ Nat.card K by exact_mod_cast (Finite.one_lt_card (α:=K)).le)
  exact ⟨u,hb.1,hb.2,(endpoint_card_mono hs).1.trans ht.1,
    (endpoint_card_mono hs).2.trans ht.2⟩

lemma marking_poor_backward (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) (hp : (m.1 i).1.2.2=false) :
    ∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ReverseCaps (markingDomain m i) u := by
  let W:=decodeState (finiteDecodeRecord (backwardRecord m)) i.rev.val
  let r:=(m.1 i).1.1.2
  have hs : reversedMarkingDomain m i ⊆ typedDomain W r false := by
    simpa only [backwardDomain,finiteTypedDomain,Fin.rev_rev,hp] using markingDomain_backward m i
  have ht:=(typed_poor_reciprocal (K:=K) (V:=Dual K V) (by simpa using hdim)
    W r (hne.map.mono hs))
  let u:=clampParameter (Nat.card K) (levelSet W (chooseLevel W r.val)).card
  have hb:=clampParameter_bounds (M:=(levelSet W (chooseLevel W r.val)).card)
    (show (1:ℝ) ≤ Nat.card K by exact_mod_cast (Finite.one_lt_card (α:=K)).le)
  have hc:=endpoint_card_mono hs
  rw [reversedDomain_first_card,reversedDomain_second_card] at hc
  exact ⟨u,hb.1,hb.2,hc.1.trans ht.1,hc.2.trans ht.2⟩

lemma marking_popular_caps (_hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty)
    (hp : (m.1 i).1.2.1=true) (hp' : (m.1 i).1.2.2=true) :
    let r:=(m.1 i).1.1.1
    let s:=(m.1 i).1.1.2
    1 ≤ r.val ∧ 1 ≤ s.val ∧
      (((markingDomain m i).image Prod.fst).card:ℝ) ≤ 32*(Nat.card K:ℝ)^s.val ∧
      (((markingDomain m i).image Prod.snd).card:ℝ) ≤ 32*(Nat.card K:ℝ)^r.val := by
  let W:=decodeState (finiteDecodeRecord (forwardRecord m)) i.val
  let W':=decodeState (finiteDecodeRecord (backwardRecord m)) i.rev.val
  let r:=(m.1 i).1.1.1
  let s:=(m.1 i).1.1.2
  have hs : markingDomain m i ⊆ typedDomain W r true := by
    simpa only [forwardDomain,finiteTypedDomain,hp] using markingDomain_forward m i
  have hs' : reversedMarkingDomain m i ⊆ typedDomain W' s true := by
    simpa only [backwardDomain,finiteTypedDomain,Fin.rev_rev,hp'] using markingDomain_backward m i
  have hc':=(endpoint_card_mono hs').2.trans (typed_popular_second W' s)
  rw [reversedDomain_second_card] at hc'
  exact ⟨typed_popular_rank_pos W r (hne.mono hs),
    typed_popular_rank_pos W' s (hne.map.mono hs'),hc',
    (endpoint_card_mono hs).2.trans (typed_popular_second W r)⟩

theorem marking_domain_dichotomy (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) :
    (∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ForwardCaps (markingDomain m i) u) ∨
    (∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ReverseCaps (markingDomain m i) u) ∨
    ((m.1 i).1.2.1=true ∧ (m.1 i).1.2.2=true ∧
      5 < (m.1 i).1.1.1.val+(m.1 i).1.1.2.val) := by
  cases hp:(m.1 i).1.2.1 with
  | false=>exact Or.inl (marking_poor_forward hdim m i hne hp)
  | true=>
    cases hp':(m.1 i).1.2.2 with
    | false=>exact Or.inr (Or.inl (marking_poor_backward hdim m i hne hp'))
    | true=>
      by_cases hh:5 < (m.1 i).1.1.1.val+(m.1 i).1.1.2.val
      · exact Or.inr (Or.inr ⟨rfl,rfl,hh⟩)
      · have hc:=marking_popular_caps hdim m i hne hp hp'
        have hr:=(m.1 i).1.1.1.isLt
        have he:=popular_reciprocal_caps
          (show (1:ℝ) ≤ Nat.card K by exact_mod_cast (Finite.one_lt_card (α:=K)).le)
          hc.1 (by omega) (by omega) hc.2.2.1 hc.2.2.2
        exact Or.inl ⟨_,he.1,he.2.1,he.2.2⟩
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N : ℕ}

local instance slotPointDE_re9819f_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance slotDualDE_re9819f_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance slotDualDualDE_re9819f_1 : DecidableEq (ℙ K (Dual K (Dual K V))) := Classical.decEq _
def classValid (width : ℝ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (i : Fin N) : SlotClass → Prop
  | .inl b => ∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ForwardCaps (markingDomain m i) u ∧ BandCondition (Real.log (Nat.card K)) width u b
  | .inr (.inl b) => ∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ReverseCaps (markingDomain m i) u ∧ BandCondition (Real.log (Nat.card K)) width u b
  | .inr (.inr (r,s)) => (m.1 i).1.1.1=r ∧ (m.1 i).1.1.2=s ∧
      (m.1 i).1.2.1=true ∧ (m.1 i).1.2.2=true ∧ 5 < r.val+s.val

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))]

theorem exists_valid_class (hdim : finrank K V=5) (width : ℝ) (hw : 0 ≤ width)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) : ∃ c,classValid width m i c := by
  rcases marking_domain_dichotomy hdim m i hne with h | h | h
  · obtain ⟨u,hu,hu',hc⟩:=h
    obtain ⟨b,hb⟩:=exists_reciprocal_band hw hu hu'
    exact ⟨.inl b,u,hu,hu',hc,hb⟩
  · obtain ⟨u,hu,hu',hc⟩:=h
    obtain ⟨b,hb⟩:=exists_reciprocal_band hw hu hu'
    exact ⟨.inr (.inl b),u,hu,hu',hc,hb⟩
  · exact ⟨.inr (.inr ((m.1 i).1.1.1,(m.1 i).1.1.2)),rfl,rfl,h⟩

def markingClass (hdim : finrank K V=5) (width : ℝ) (hw : 0 ≤ width)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) : SlotClass :=
  if hne : (markingDomain m i).Nonempty then (exists_valid_class hdim width hw m i hne).choose
  else .inl 0

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_TwoScanContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] {N l : ℕ}

attribute [local instance] OAI.SharpRamseyFive.Marking.markedClassFinDE
local instance markedClassPointDE_re9819f_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance markedClassDualDE_re9819f_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
def markedCode (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (c : κ×UnionTranscript (Fin N) (FlagPair K V)) := markingClass hdim width hw c.2

def markedClassLaw (hdim : finrank K V=5) (p : Law (κ×(Fin N→FlagPair K V)))
    (hl : l≤N) (width : ℝ) (hw : 0≤width) (a : SlotClass)
    (hE : 0<eventMass (first (withMessage p markingMessage))
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a)) :=
  selectByContext
    (conditionContext (withMessage p markingMessage)
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a) hE)
    (fun c=>(selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a c : Fin l→Fin N))

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkedStreamExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

def markedContext (ctx : Ω→κ) (x : Ω→Fin n→FlagPair K V) (a : Ω) :=
  (ctx a,markingMessage (x a))

attribute [local instance] OAI.SharpRamseyFive.Marking.streamClassFinDE
local instance streamClassPointDE_re9819f_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance streamClassDualDE_re9819f_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
def markedPositions (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (ctx : Ω→κ) (x : Ω→Fin n→FlagPair K V) (a : SlotClass) (z : Ω) :=
  classPositions (unspecified (markingMessage (x z)))
    (markedCode hdim width hw (markedContext ctx x z)) a

def markedEvent (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (l : ℕ) : SlotClass→Finset (κ×UnionTranscript (Fin n) (FlagPair K V)) :=
  selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw)

def classStream (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) :
    SelectedStream (Ω:=Ω) (β:=FlagPair K V) N l admissible :=
  (S.restrict _ hE).extract hl (markedPositions hdim width hw ctx S.tuple a)

omit [Finite K] in
lemma markedContext_law (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) :
    first (withMessage (pair S.law ctx S.tuple) markingMessage)=
      map S.law (markedContext ctx S.tuple) := by
  rw [withMessage_pair,first_pair]
  rfl

lemma classStream_joint (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) :
    ∃ hE',pair (classStream hdim width hw S ctx hl a hE).law (markedContext ctx S.tuple)
      (classStream hdim width hw S ctx hl a hE).tuple=
        markedClassLaw hdim (pair S.law ctx S.tuple) hl width hw a hE' := by
  have hE' : 0<eventMass (first (withMessage (pair S.law ctx S.tuple) markingMessage))
      (markedEvent hdim width hw l a) := by
    rwa [markedContext_law,eventMass_map_preimage]
  refine ⟨hE',?_⟩
  change pair (conditionOn S.law _ hE) (markedContext ctx S.tuple)
    (fun z=>retainedTuple hl (S.tuple z) (markedPositions hdim width hw ctx S.tuple a z)) = _
  unfold markedClassLaw
  simp only [withMessage_pair]
  rw [←conditionContext_pair,selected_pair]
  · rfl
  · rw [eventMass_map_preimage]
    exact hE

attribute [local irreducible] unspecified classPositions

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveExpectedLevelLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem projective_expected_level_loss (hdim : finrank K V=5)
    (p : Law ((ℙ K V)×(ℙ K (Dual K V))))
    (hp : ∀z,0 < p z→Incident z.1 z.2) (NA NB C : ℝ)
    (hNA : 0 < NA) (hNB : 0 < NB) (hC : 0 < C)
    (hA : ((support (first p)).card:ℝ) ≤ NA) (hB : ((support (second p)).card:ℝ) ≤ NB)
    (hprod : NA*NB ≤ C^2*(Nat.card K:ℝ)^5) :
    (∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤
      2*(4*Real.log (Nat.card K)+Real.log C+Real.log (C+1)-entropy p+
        entropy (levelLaw (first p))+entropy (levelLaw (second p))) := by
  let D : ℝ := Real.log (C+1)+(3:ℝ)/2*Real.log (Nat.card K)+(Real.log NA+Real.log NB)/2
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have he := expected_total_level_loss p NA NB D (by
    intro n hn
    let F := (support p).filter (fun z=>endpointLevels p z=n)
    let A := levelCell (first p) n.1
    let B := levelCell (second p) n.2
    have hF : F.Nonempty := positive_level_pair_support p n hn
    have hsub : F⊆(A×ˢB).filter (fun z=>Incident z.1 z.2) := level_pair_support_subset p Incident hp n
    have hI : 0 < incidences A B := Finset.card_pos.mpr (hF.mono hsub)
    have hAc : 0 < A.card := by
      obtain ⟨z,hz⟩ := hF
      exact Finset.card_pos.mpr ⟨z.1,(Finset.mem_product.mp (Finset.mem_filter.mp (hsub hz)).1).1⟩
    have hBc : 0 < B.card := by
      obtain ⟨z,hz⟩ := hF
      exact Finset.card_pos.mpr ⟨z.2,(Finset.mem_product.mp (Finset.mem_filter.mp (hsub hz)).1).2⟩
    have hAcR : (0:ℝ) < A.card := by exact_mod_cast hAc
    have hBcR : (0:ℝ) < B.card := by exact_mod_cast hBc
    have hAB : (A.card:ℝ)*B.card ≤ C^2*(Nat.card K:ℝ)^5 :=
      (mul_le_mul (levelCell_cap _ NA hA _) (levelCell_cap _ NB hB _) (Nat.cast_nonneg _) hNA.le).trans hprod
    have hl := incidence_rectangle_log hdim A B C hC.le hAB hAc hBc hI
    have hFc : (0:ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hF
    have hc : (F.card:ℝ) ≤ (incidences A B:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have hf := (Real.log_le_log hFc hc).trans hl
    change Real.log (F.card:ℝ) ≤ D-(Real.log (NA/(A.card:ℝ))+Real.log (NB/(B.card:ℝ)))/2
    rw [Real.log_div hNA.ne' hAcR.ne',Real.log_div hNB.ne' hBcR.ne']
    dsimp [D]
    linarith)
  have hlog := Real.log_le_log (mul_pos hNA hNB) hprod
  rw [Real.log_mul hNA.ne' hNB.ne',Real.log_mul (pow_pos hC _).ne' (pow_pos hq _).ne',
    Real.log_pow,Real.log_pow] at hlog
  change (∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤
      2*(D-entropy p+entropy (levelLaw (first p))+entropy (levelLaw (second p))) at he
  dsimp only [D] at he
  apply he.trans
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_entropy_cap (hdim : finrank K V=5) (p : Law (ℙ K V)) :
    entropy p ≤ 5*Real.log (Nat.card K) := by
  have h := entropy_le_log_card p
  rw [card_points (d:=4) hdim] at h
  have hQ : (0:ℝ) < Q (Nat.card K) 4 := by exact_mod_cast Q_pos (Nat.card K) 4
  have hl := Real.log_le_log hQ (Q_le_power (d:=4) (by have:=Finite.one_lt_card (α:=K);omega))
  rw [Real.log_pow] at hl
  norm_num at hl
  exact h.trans hl

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma dual_entropy_cap (hdim : finrank K V=5) (p : Law (ℙ K (Dual K V))) :
    entropy p ≤ 5*Real.log (Nat.card K) := by
  have h := entropy_le_log_card p
  rw [card_hyperplanes (d:=4) hdim] at h
  have hQ : (0:ℝ) < Q (Nat.card K) 4 := by exact_mod_cast Q_pos (Nat.card K) 4
  have hl := Real.log_le_log hQ (Q_le_power (d:=4) (by have:=Finite.one_lt_card (α:=K);omega))
  rw [Real.log_pow] at hl
  norm_num at hl
  exact h.trans hl

omit [FiniteDimensional K V] in
theorem projective_level_entropy (hdim : finrank K V=5)
    (p : Law ((ℙ K V)×(ℙ K (Dual K V)))) :
    entropy (levelLaw (first p))+entropy (levelLaw (second p)) ≤
      2*(Real.log (5*Real.log (Nat.card K)+1)+1) := by
  have hq : (1:ℝ) < Nat.card K := by exact_mod_cast Finite.one_lt_card (α:=K)
  have hM : 0 < 5*Real.log (Nat.card K) := mul_pos (by norm_num) (Real.log_pos hq)
  have h₁ := endpoint_level_entropy (first p) _ hM (point_entropy_cap hdim _)
  have h₂ := endpoint_level_entropy (second p) _ hM (dual_entropy_cap hdim _)
  linarith

theorem endpoint_supports (hdim : finrank K V=5)
    (p : Law ((ℙ K V)×(ℙ K (Dual K V))))
    (hp : ∀z,0 < p z→Incident z.1 z.2) (NA NB C k δ b : ℝ)
    (hNA : 0 < NA) (hNB : 0 < NB) (hC : 0 < C) (hk : 0 < k)
    (hA : ((support (first p)).card:ℝ) ≤ NA)
    (hB : ((support (second p)).card:ℝ) ≤ NB)
    (hprod : NA*NB ≤ C^2*(Nat.card K:ℝ)^5)
    (hent : 4*Real.log (Nat.card K)-entropy p ≤ δ)
    (GA : Finset (ℙ K V)) (GB : Finset (ℙ K (Dual K V)))
    (hGA : eventMass (first p) GAᶜ ≤ b) (hGB : eventMass (second p) GBᶜ ≤ b)
    (hsmall : 2*(δ+Real.log C+Real.log (C+1)+
      2*(Real.log (5*Real.log (Nat.card K)+1)+1))/k+2*Real.exp 1*b ≤ (1:ℝ)/2) :
    ∃μ : Law (Finset (ℙ K V)), ∃ν : Law (Finset (ℙ K (Dual K V))),
      (∀A,0 < μ A→A⊆GA ∧ NA*Real.exp (-k)/2 ≤ (A.card:ℝ) ∧ (A.card:ℝ) ≤ NA) ∧
      (∀B,0 < ν B→B⊆GB ∧ NB*Real.exp (-k)/2 ≤ (B.card:ℝ) ∧ (B.card:ℝ) ≤ NB) ∧
      (∀a,(∑A,μ A*(if a∈A then 1/(A.card:ℝ) else 0)) ≤ 4*Real.exp 1*first p a) ∧
      (∀a,(∑B,ν B*(if a∈B then 1/(B.card:ℝ) else 0)) ≤ 4*Real.exp 1*second p a) := by
  let T := 2*(δ+Real.log C+Real.log (C+1)+2*(Real.log (5*Real.log (Nat.card K)+1)+1))
  have hbound := projective_expected_level_loss hdim p hp NA NB C hNA hNB hC hA hB hprod
  have hlevels := projective_level_entropy hdim p
  have htotal : (∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤ T := by
    dsimp only [T]
    apply hbound.trans
    linarith only [hent,hlevels]
  have hnA : 0 ≤ ∑n,levelLaw (first p) n*levelLoss (first p) NA n :=
    Finset.sum_nonneg (fun n _=>mul_nonneg ((levelLaw _).nonneg n)
      (levelLoss_nonneg _ NA hNA (levelCell_cap _ NA hA) n))
  have hnB : 0 ≤ ∑n,levelLaw (second p) n*levelLoss (second p) NB n :=
    Finset.sum_nonneg (fun n _=>mul_nonneg ((levelLaw _).nonneg n)
      (levelLoss_nonneg _ NB hNB (levelCell_cap _ NB hB) n))
  have hsA : (∑n,levelLaw (first p) n*levelLoss (first p) NA n)/k+
      2*Real.exp 1*eventMass (first p) GAᶜ ≤ (1:ℝ)/2 := by
    apply le_trans (add_le_add (div_le_div_of_nonneg_right (by linarith :
      (∑n,levelLaw (first p) n*levelLoss (first p) NA n) ≤ T) hk.le)
      (mul_le_mul_of_nonneg_left hGA (by positivity))) hsmall
  have hsB : (∑n,levelLaw (second p) n*levelLoss (second p) NB n)/k+
      2*Real.exp 1*eventMass (second p) GBᶜ ≤ (1:ℝ)/2 := by
    apply le_trans (add_le_add (div_le_div_of_nonneg_right (by linarith :
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤ T) hk.le)
      (mul_le_mul_of_nonneg_left hGB (by positivity))) hsmall
  have heA := permissible_half_mass (first p) GA NA k hNA hk (levelCell_cap _ NA hA) hsA
  have heB := permissible_half_mass (second p) GB NB k hNB hk (levelCell_cap _ NB hB) hsB
  refine ⟨goodSupportLaw (first p) GA NA k heA,goodSupportLaw (second p) GB NB k heB,?_,?_,?_,?_⟩
  · exact goodSupportLaw_bounds _ _ NA k hNA (levelCell_cap _ NA hA) heA
  · exact goodSupportLaw_bounds _ _ NB k hNB (levelCell_cap _ NB hB) heB
  · exact goodSupportLaw_domination _ _ NA k heA
  · exact goodSupportLaw_domination _ _ NB k heB

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalLevelProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] in
theorem reciprocal_bad_endpoints (p : Law (FlagPair K V)) (u s d C₀ : ℝ)
    (hs : 0 < s)
    (hA : ((support (first p)).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u))
    (hB : ((support (second p)).card:ℝ)≤32*Real.exp u)
    (hflag : ((support p).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d) :
    eventMass (first p) (goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u))
      ((Nat.card K:ℝ)^4) s)ᶜ ≤ reciprocalBadMass s d C₀ ∧
    eventMass (second p) (goodFirstEndpoints (swap p) (32*Real.exp u)
      ((Nat.card K:ℝ)^4) s)ᶜ ≤ reciprocalBadMass s d C₀ := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hlog : Real.log ((Nat.card K:ℝ)^4)=4*Real.log (Nat.card K) := by rw [Real.log_pow]; norm_num
  have hratio : (C₀*(Nat.card K:ℝ)^4)/(Nat.card K:ℝ)^4=C₀ := by field_simp
  have hbound : Real.exp (-s)+50*(Real.log ((Nat.card K:ℝ)^4)-entropy p+
      (C₀*(Nat.card K:ℝ)^4)/(Nat.card K:ℝ)^4)/s ≤ reciprocalBadMass s d C₀ := by
    rw [hlog,hratio]
    exact add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hent (le_refl C₀)) (by norm_num : (0:ℝ)≤50)) hs.le)
  constructor
  · exact (bad_first_endpoint_mass p _ _ _ s (by positivity) (by positivity) hs hA hflag).trans hbound
  · have hflag' : ((support (swap p)).card:ℝ)≤C₀*(Nat.card K:ℝ)^4 := by rw [support_swap_card]; exact hflag
    have hh:=bad_first_endpoint_mass (swap p) (32*Real.exp u) ((Nat.card K:ℝ)^4)
      (C₀*(Nat.card K:ℝ)^4) s (by positivity) (by positivity) hs (by simpa only [first_swap] using hB) hflag'
    simpa only [first_swap,entropy_swap] using hh.trans (by simpa only [entropy_swap] using hbound)

structure ReciprocalLevels (p : Law (FlagPair K V)) (u s : ℝ) where
  firstLaw : Law (Finset (ℙ K V))
  secondLaw : Law (Finset (ℙ K (Dual K V)))
  first_good : ∀ A,0<firstLaw A→A.Nonempty ∧
    A⊆goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s ∧
    (32*Real.exp (5*Real.log (Nat.card K)-u))*Real.exp (-s)/2≤(A.card:ℝ) ∧
    (A.card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u)
  second_good : ∀ B,0 < secondLaw B→B.Nonempty ∧
    B⊆goodFirstEndpoints (swap p) (32*Real.exp u) ((Nat.card K:ℝ)^4) s ∧
    (32*Real.exp u)*Real.exp (-s)/2≤(B.card:ℝ) ∧ (B.card:ℝ)≤32*Real.exp u
  first_dom : ∀ a,(∑ A,firstLaw A*uniformWeight A a)≤4*Real.exp 1*first p a
  second_dom : ∀ b,(∑ B,secondLaw B*uniformWeight B b)≤4*Real.exp 1*second p b

theorem reciprocal_levels_exist (hdim : finrank K V=5)
    (p : Law (FlagPair K V)) (u s d C₀ : ℝ)
    (hinc : ∀ z,0<p z→Incident z.1 z.2) (hs : 0 < s)
    (hA : ((support (first p)).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u))
    (hB : ((support (second p)).card:ℝ)≤32*Real.exp u)
    (hflag : ((support p).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d)
    (hsmall : 2*(d+Real.log 32+Real.log 33+
      2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
      2*Real.exp 1*reciprocalBadMass s d C₀≤(1:ℝ)/2) :
    Nonempty (ReciprocalLevels p u s) := by
  obtain ⟨ha,hb⟩:=reciprocal_bad_endpoints p u s d C₀ hs hA hB hflag hent
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hprod : (32*Real.exp (5*Real.log (Nat.card K)-u))*(32*Real.exp u)=
      32^2*(Nat.card K:ℝ)^5 := by
    have he : Real.exp (5*Real.log (Nat.card K)-u)*Real.exp u=(Nat.card K:ℝ)^5 := by
      rw [←Real.exp_add,sub_add_cancel]
      rw [show (5:ℝ)*Real.log (Nat.card K)=(5:ℕ)*Real.log (Nat.card K) from rfl,
        Real.exp_nat_mul,Real.exp_log hq]
    nlinarith only [he]
  obtain ⟨μ,ν,hμ,hν,hdμ,hdν⟩:=endpoint_supports hdim p hinc
    (32*Real.exp (5*Real.log (Nat.card K)-u)) (32*Real.exp u) 32 s d
    (reciprocalBadMass s d C₀) (by positivity) (by positivity) (by norm_num) hs
    hA hB hprod.le hent _ _ ha hb (by simpa only [show (32:ℝ)+1=33 by norm_num] using hsmall)
  refine ⟨⟨μ,ν,?_,?_,hdμ,hdν⟩⟩
  · intro A h
    have hh:=hμ A h
    have hn : 0<(A.card:ℝ):=(by positivity : 0<(32*Real.exp (5*Real.log (Nat.card K)-u))*Real.exp (-s)/2).trans_le hh.2.1
    exact ⟨Finset.card_pos.mp (by exact_mod_cast hn),hh⟩
  · intro B h
    have hh:=hν B h
    have hn : 0<(B.card:ℝ):=(by positivity : 0<(32*Real.exp u)*Real.exp (-s)/2).trans_le hh.2.1
    exact ⟨Finset.card_pos.mp (by exact_mod_cast hn),hh⟩
end
end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalGoodReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

def reciprocalGoodA (p : Law (FlagPair K V)) (u s : ℝ) : Finset (ℙ K V) :=
  goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s

def reciprocalGoodB (p : Law (FlagPair K V)) (u s : ℝ) : Finset (ℙ K (Dual K V)) :=
  goodFirstEndpoints (swap p) (32*Real.exp u) ((Nat.card K:ℝ)^4) s

omit [FiniteDimensional K V] in
theorem reciprocal_good_mass (p : Law (FlagPair K V)) (u s d C₀ : ℝ) (hs : 0 < s)
    (hA : ((support (first p)).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u))
    (hB : ((support (second p)).card:ℝ)≤32*Real.exp u)
    (hflag : ((support p).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d) (hsmall : reciprocalBadMass s d C₀≤(1:ℝ)/2) :
    (1:ℝ)/2≤eventMass (first p) (reciprocalGoodA p u s) ∧
      (1:ℝ)/2≤eventMass (second p) (reciprocalGoodB p u s) := by
  obtain ⟨ha,hb⟩:=reciprocal_bad_endpoints p u s d C₀ hs hA hB hflag hent
  have h1:=eventMass_complement (first p) (reciprocalGoodA p u s)
  have h2:=eventMass_complement (second p) (reciprocalGoodB p u s)
  change eventMass (first p) (reciprocalGoodA p u s)ᶜ≤_ at ha
  change eventMass (second p) (reciprocalGoodB p u s)ᶜ≤_ at hb
  constructor <;> linarith

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowReciprocalScores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical
noncomputable section
variable {w r : ℕ}
def earlySlot (sel : (Fin w×Bool)→Fin r) (v : Fin w) : Slots w r :=
  Sum.inl ((v,false),sel (v,false))
def lateSlot (sel : (Fin w×Bool)→Fin r) (v : Fin w) : Slots w r :=
  Sum.inl ((v,true),sel (v,true))
end
end SharpRamseyFive.Windows

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]
local instance windowLevelsIndexDE : DecidableEq (Slots w r) := Classical.decEq _

local instance windowLevelsBlockDE_re9819f_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
structure ReciprocalWindows (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ)
    (sel : (Fin w×Bool)→Fin r) (e : I→Fin w) (s : ℝ) where
  early : ∀ i,ReciprocalLevels (map p (fun x=>x (earlySlot sel (e i)))) (u (earlySlot sel (e i))) s
  late : ∀ i,ReciprocalLevels (map p (fun x=>x (lateSlot sel (e i)))) (u (lateSlot sel (e i))) s
  early_half : ∀ i,(1:ℝ)/2 ≤ eventMass (first (map p (fun x=>x (earlySlot sel (e i)))))
    (reciprocalGoodA (map p (fun x=>x (earlySlot sel (e i)))) (u (earlySlot sel (e i))) s)
  late_half : ∀ i,(1:ℝ)/2 ≤ eventMass (second (map p (fun x=>x (lateSlot sel (e i)))))
    (reciprocalGoodB (map p (fun x=>x (lateSlot sel (e i)))) (u (lateSlot sel (e i))) s)

namespace ReciprocalWindows
local instance windowLevelsBlockDE_re9819f_2 : DecidableEq (Fin w×Bool) := Classical.decEq _
variable {p : Law (Slots w r→FlagPair K V)} {u : Slots w r→ℝ}
  {sel : (Fin w×Bool)→Fin r} {e : I→Fin w} {s : ℝ}
  (W : ReciprocalWindows p u sel e s)

def firstReference (i : I) : Law (ℙ K V) :=
  conditionOn (first (map p (fun x=>x (earlySlot sel (e i)))))
    (reciprocalGoodA (map p (fun x=>x (earlySlot sel (e i)))) (u (earlySlot sel (e i))) s)
    (lt_of_lt_of_le (by norm_num) (W.early_half i))
def secondReference (i : I) : Law (ℙ K (Dual K V)) :=
  conditionOn (second (map p (fun x=>x (lateSlot sel (e i)))))
    (reciprocalGoodB (map p (fun x=>x (lateSlot sel (e i)))) (u (lateSlot sel (e i))) s)
    (lt_of_lt_of_le (by norm_num) (W.late_half i))
def firstSupport (i : I) (A : Finset (ℙ K V)) : Finset (ℙ K V) :=
  (W.early i).firstLaw.repair A
def secondSupport (i : I) (B : Finset (ℙ K (Dual K V))) : Finset (ℙ K (Dual K V)) :=
  (W.late i).secondLaw.repair B

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma first_nonempty (i : I) (A : Finset (ℙ K V)) : (W.firstSupport i A).Nonempty :=
  ((W.early i).first_good _ ((W.early i).firstLaw.repair_positive A)).1
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma second_nonempty (i : I) (B : Finset (ℙ K (Dual K V))) : (W.secondSupport i B).Nonempty :=
  ((W.late i).second_good _ ((W.late i).secondLaw.repair_positive B)).1
end ReciprocalWindows

omit [Nonempty (Fin r)] in
theorem reciprocal_windows_exist (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ)
    (sel : (Fin w×Bool)→Fin r) (e : I→Fin w) (s d ε C₀ : ℝ) (hs : 0 < s)
    (hinc : ∀ x,0<p x → ∀ i,Incident (x i).1 (x i).2)
    (hA : ∀ i,((support (first (map p (fun x=>x i)))).card:ℝ) ≤ 32*Real.exp (5*Real.log (Nat.card K)-u i))
    (hB : ∀ i,((support (second (map p (fun x=>x i)))).card:ℝ) ≤ 32*Real.exp (u i))
    (hflag : ∀ i,((support (map p (fun x=>x i))).card:ℝ) ≤ C₀*(Nat.card K:ℝ)^4)
    (hgood : ∀ i,indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (earlySlot sel (e i))=0 ∧
      indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (lateSlot sel (e i))=0)
    (hmass : reciprocalBadMass s d C₀ ≤ (1:ℝ)/2)
    (hsmall : 2*(d+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
      2*Real.exp 1*reciprocalBadMass s d C₀ ≤ (1:ℝ)/2) :
    Nonempty (ReciprocalWindows p u sel e s) := by
  have hend (i : Slots w r) (h : indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel i=0) :
      4*Real.log (Nat.card K)-entropy (map p (fun x=>x i)) ≤ d :=
    (good_index_scores _ d ε p _ (fun _ _=>orderedCollision_nonneg ..) sel i h).1
  have hi (i : Slots w r) : ∀ z,0 < map p (fun x=>x i) z → Incident z.1 z.2 := by
    intro z hz
    obtain ⟨x,hx,rfl⟩:=map_positive p (fun x=>x i) z hz
    exact hinc x hx i
  let L (i : I) := Classical.choice (reciprocal_levels_exist hdim _ _ s d C₀ (hi _) hs
    (hA _) (hB _) (hflag _) (hend _ (hgood i).1) hsmall)
  let R (i : I) := Classical.choice (reciprocal_levels_exist hdim _ _ s d C₀ (hi _) hs
    (hA _) (hB _) (hflag _) (hend _ (hgood i).2) hsmall)
  refine ⟨⟨L,R,?_,?_⟩⟩
  · intro i
    exact (reciprocal_good_mass _ _ s d C₀ hs (hA _) (hB _) (hflag _) (hend _ (hgood i).1) hmass).1
  · intro i
    exact (reciprocal_good_mass _ _ s d C₀ hs (hA _) (hB _) (hflag _) (hend _ (hgood i).2) hmass).2
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_SurvivingWindowCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance swcIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.swcProp
local instance swcBDE_re9819f_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w)) (hE : E.Nonempty)
  {s : ℝ} (W : ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

abbrev WindowLevelsData (m : ℕ) :=
  (Fin (m+1)→Finset (ℙ K V))×(Fin (m+1)→Finset (ℙ K (Dual K V)))

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowDeletionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {w r : ℕ}

attribute [local instance] OAI.SharpRamseyFive.Windows.deletionTargetDE
def goodWindowSet (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r) : Finset (Fin w) :=
  Finset.univ.filter (fun v=>∀b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0)
def survivingWindowSet (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r)
    (drop : Fin w→ℝ) (k : ℝ) : Finset (Fin w) :=
  (goodWindowSet bad sel).filter (fun v=>drop v≤k)
lemma mem_goodWindowSet (bad : Slots w r→ℝ) (sel : Fin w×Bool→Fin r) (v : Fin w) :
    v∈goodWindowSet bad sel ↔ ∀b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0 := by
  simp only [goodWindowSet,Finset.mem_filter,Finset.mem_univ,true_and]
end
end SharpRamseyFive.Windows

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_AllHistoryWindowLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance allHistIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
local instance allHistBDE_re9819f_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.allHistTDE
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ]
  {w n steps rem : ℕ} [Nonempty (Fin n)]

abbrev WindowHistory (κ K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (w n steps : ℕ) :=
  (κ×BlockHistory (Fin w×Bool) (Fin n) (Fin w×Fin (2*n)) (FlagPair K V) steps)×
    (Fin w×Bool→Fin n)

def windowPosterior (p : κ→Law (Slots w n→FlagPair K V)) (z : WindowHistory κ K V w n steps) :
    Law (Slots w n→FlagPair K V) := historyPosterior (p z.1.1) z.1.2

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_DomainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

attribute [local instance] OAI.SharpRamseyFive.Marking.dtPDE
attribute [local instance] OAI.SharpRamseyFive.Marking.dtDDE
attribute [local instance] OAI.SharpRamseyFive.Marking.dtDDDE
structure HighCaps (D : Finset (FlagPair K V)) (r r' : ℕ) : Prop where
  flag : (D.card:ℝ)≤153*(Nat.card K:ℝ)^4
  first : ((D.image Prod.fst).card:ℝ)≤32*(Nat.card K:ℝ)^r'
  second : ((D.image Prod.snd).card:ℝ)≤32*(Nat.card K:ℝ)^r
  firstPartners : ∀a,((Finset.univ.filter fun b=>(a,b)∈D).card:ℝ)≤2*(Nat.card K:ℝ)^(4-r')
  secondPartners : ∀b,((Finset.univ.filter fun a=>(a,b)∈D).card:ℝ)≤2*(Nat.card K:ℝ)^(4-r)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_PreparedStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.psFinDE
structure Prepared (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (J B M : ℝ) where
  domain : κ→Fin n→Finset (FlagPair K V)
  contains : ∀z,0<S.law z→∀i,S.tuple z i∈domain (ctx z) i
  cap : ∀c i,Real.log (domain c i).card≤J
  deficit : mean (first (pair S.law ctx S.tuple))
    (fun c=>(n:ℝ)*J-entropy (fiber (pair S.law ctx S.tuple) c))≤B
  incident : ∀z,0<S.law z→TupleIncident (S.tuple z)
  consistent : ∀z,0<S.law z→TupleConsistent (S.tuple z)
  occupancy : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
    (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighSampleRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def SampleConflict (w z : SampleFlag (K:=K) (V:=V)) : Prop :=
  Incident w.1 z.2 ∧ ¬Incident z.1 w.2

end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {w n : ℕ} [Nonempty (Fin n)]
local instance wfcIDE : DecidableEq (Slots w n) := Classical.decEq _

local instance wfcBDE_re9819f_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
structure ReciprocalCaps (p : Law (I→FlagPair K V)) (u : I→ℝ) (C : ℝ) : Prop where
  incident : ∀x,0<p x→∀i,Incident (x i).1 (x i).2
  first : ∀i,((support (first (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u i)
  second : ∀i,((support (second (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (u i)
  flag : ∀i,((support (map p (fun x=>x i))).card:ℝ)≤C*(Nat.card K:ℝ)^4

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma goodWindow_scores {p : Law (Slots w n→FlagPair K V)} {u : Slots w n→ℝ}
    {sel : Fin w×Bool→Fin n} {J d ε s : ℝ} (hJ : 4*Real.log (Nat.card K)≤J)
    {v : Fin w} (hv : v∈goodWindowSet
      (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel) sel) :
    indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w n) u s) sel
      (earlySlot sel v)=0 ∧
    indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w n) u s) sel
      (lateSlot sel v)=0 := by
  have hg := (mem_goodWindowSet _ _ _).mp hv
  exact ⟨indexBad_of_larger_cap hJ _ _ _ _ (hg false),indexBad_of_larger_cap hJ _ _ _ _ (hg true)⟩

variable (hdim : finrank K V=5) (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (J d ε s C : ℝ)
  (hcap : ReciprocalCaps p u C) (hs : 0 < s) (hJ : 4*Real.log (Nat.card K)≤J)
  (hmass : reciprocalBadMass s d C≤1/2)
  (hsmall : 2*(d+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
    2*Real.exp 1*reciprocalBadMass s d C≤1/2)

include hdim hcap hs hJ hmass hsmall

omit [Nonempty (Fin n)] in
theorem goodWindows_exist {A : Type} [Fintype A] (e : A→Fin w)
    (he : ∀i,e i∈goodWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel) sel) :
    Nonempty (ReciprocalWindows p u sel e s) :=
  reciprocal_windows_exist hdim p u sel e s d ε C hs hcap.incident hcap.first hcap.second hcap.flag
    (fun i=>goodWindow_scores hJ (he i)) hmass hsmall

omit [Nonempty (Fin n)] in
theorem survivingWindows_exist (k : ℝ)
    (hE : (survivingWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel)
      sel (fun v=>u (earlySlot sel v)-u (lateSlot sel v)) k).Nonempty) :
    Nonempty (ReciprocalWindows p u sel
      (survivingOriginal (survivingWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel)
        sel (fun v=>u (earlySlot sel v)-u (lateSlot sel v)) k) hE) s) := by
  apply goodWindows_exist hdim p u sel J d ε s C hcap hs hJ hmass hsmall
  intro i
  have hi:=survivingOriginal_mem _ hE i
  exact (Finset.mem_filter.mp hi).1

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalDomainCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module ProjectiveIncidence FiniteEntropy Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I]

lemma support_map_mono {α β : Type} [Fintype α] [Fintype β]
    (p r : Law α) (f : α→β) (h : ∀x,0 < r x→0<p x) :
    support (map r f)⊆support (map p f) := by
  intro b hb
  obtain ⟨x,hx,rfl⟩:=map_positive r f b ((mem_support _ _).mp hb)
  apply (mem_support _ _).mpr
  apply (h x hx).trans_le
  change p x≤∑y,if f y=f x then p y else 0
  have ht:=Finset.single_le_sum (s:=Finset.univ) (a:=x)
    (f:=fun y=>if f y=f x then p y else 0)
    (fun y _=>by split_ifs;exact p.nonneg _;rfl) (Finset.mem_univ x)
  simpa only [ite_true] using ht

variable {B A T : Type} [Fintype B] [Fintype A] [Fintype T] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.Marking.reciprocalHistoryDE
omit [Finite K] [FiniteDimensional K V] [Nonempty A] in
lemma ReciprocalCaps.history
    (p : Law (((B×A)⊕T)→FlagPair K V)) (u : ((B×A)⊕T)→ℝ) (C : ℝ)
    (h : ReciprocalCaps (K:=K) (V:=V) p u C) (steps : ℕ) (z : BlockHistory B A T (FlagPair K V) steps) :
    ReciprocalCaps (K:=K) (V:=V) (historyPosterior p z) u C := by
  have hp : ∀x,0<historyPosterior p z x→0<p x := history_support p steps z
  have hfm (i) : support (FiniteEntropy.first (map (historyPosterior p z) (fun x=>x i)))⊆
      support (FiniteEntropy.first (map p (fun x=>x i))) := by
    rw [←map_fst,←map_fst,map_comp,map_comp]
    exact support_map_mono p (historyPosterior p z) _ hp
  have hsm (i) : support (FiniteEntropy.second (map (historyPosterior p z) (fun x=>x i)))⊆
      support (FiniteEntropy.second (map p (fun x=>x i))) := by
    rw [←map_snd,←map_snd,map_comp,map_comp]
    exact support_map_mono p (historyPosterior p z) _ hp
  refine ⟨fun x hx=>h.incident x (hp x hx),?_,?_,?_⟩
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (hfm i))).trans (h.first i)
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (hsm i))).trans (h.second i)
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card
      (support_map_mono p (historyPosterior p z) (fun x=>x i) hp))).trans (h.flag i)
end
end

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance histWinIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
local instance histWinBDE_re9819f_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ]
  {w n steps : ℕ} [Nonempty (Fin n)]

def historyCollision (p : κ→Law (Slots w n→FlagPair K V)) (u : κ→Slots w n→ℝ) (s : ℝ)
    (a : κ) (h : BlockHistory (Fin w×Bool) (Fin n) (Fin w×Fin (2*n)) (FlagPair K V) steps) :=
  orderedCollision (historyPosterior (p a) h) (slotEquiv w n) (u a) s

def actualWindowSet (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (u : κ→Slots w n→ℝ) (J d ε s k : ℝ) (z : WindowHistory κ K V w n steps) : Finset (Fin w) :=
  if 0<μ z.1.1 then survivingWindowSet
    (indexBad J d ε (windowPosterior p z) (historyCollision p u s z.1.1 z.1.2) z.2)
    z.2 (fun v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) k else ∅

def actualWindows (hdim : finrank K V=5) (μ : Law κ)
    (p : κ→Law (Slots w n→FlagPair K V)) (u : κ→Slots w n→ℝ) (J d ε s k C : ℝ)
    (hcap : ∀a,0<μ a→ReciprocalCaps (p a) (u a) C)
    (hs : 0 < s) (hJ : 4*Real.log (Nat.card K)≤J)
    (hmass : reciprocalBadMass s d C≤1/2)
    (hsmall : 2*(d+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
      2*Real.exp 1*reciprocalBadMass s d C≤1/2)
    (z : WindowHistory κ K V w n steps) (hE : (actualWindowSet μ p u J d ε s k z).Nonempty) :
    ReciprocalWindows (windowPosterior p z) (u z.1.1) z.2
      (survivingOriginal (actualWindowSet μ p u J d ε s k z) hE) s := by
  have ha : 0<μ z.1.1 := by
    by_contra h
    simp only [actualWindowSet,ite_eq_right h,Finset.not_nonempty_empty] at hE
  generalize hset : actualWindowSet μ p u J d ε s k z=E at hE ⊢
  have hsame : E=survivingWindowSet
      (indexBad J d ε (windowPosterior p z) (historyCollision p u s z.1.1 z.1.2) z.2)
      z.2 (fun v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) k := by
    rw [←hset,actualWindowSet,ite_eq_left ha]
  cases hsame
  exact Classical.choice (survivingWindows_exist hdim (windowPosterior p z) (u z.1.1) z.2
    J d ε s C ((hcap z.1.1 ha).history _ _ _ steps z.1.2) hs hJ hmass hsmall k hE)

end

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ClassifiedStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.Marking.csFinDE
local instance csPDE_re9819f_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance csDDE_re9819f_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
def DomainClass (width : ℝ) (D : Finset (FlagPair K V)) : SlotClass→Prop
  | .inl b=>∃u,Real.log (Nat.card K)≤u ∧ u≤4*Real.log (Nat.card K) ∧
      ForwardCaps D u ∧ BandCondition (Real.log (Nat.card K)) width u b
  | .inr (.inl b)=>∃u,Real.log (Nat.card K)≤u ∧ u≤4*Real.log (Nat.card K) ∧
      ReverseCaps D u ∧ BandCondition (Real.log (Nat.card K)) width u b
  | .inr (.inr (r,s))=>5 < r.val+s.val ∧ HighCaps D r.val s.val

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ClassPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.cmFinDE
variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype α]

structure ClassifiedPrepared (N n : ℕ) (admissible : (Fin N→α)→Prop)
    (d J B M width : ℝ) where
  sample : Type
  [finiteSample : Fintype sample]
  context : Type
  [finiteContext : Fintype context]
  stream : SelectedStream (Ω:=sample) (β:=FlagPair K V) N n admissible
  ctx : sample→context
  prepared : Prepared stream ctx J B M
  slotClass : SlotClass
  classified : ∀c,0 < map stream.law ctx c→∀i,DomainClass width (prepared.domain c i) slotClass
  density_bound : stream.density≤d
attribute [instance] ClassifiedPrepared.finiteSample ClassifiedPrepared.finiteContext

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlagGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FlagConstruction
open Module SharpRamseyFive.Marking SharpRamseyFive.FiniteEntropy SharpRamseyFive.SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K : Type*} [Field K] {N n : ℕ}

variable [Nonempty (Flag K)]
def encodeRaw (z : FlagPair K (Space K)) : Flag K :=
  if h : Incident z.1 z.2 then ⟨z,h⟩ else Classical.choice inferInstance

end
end SharpRamseyFive.FlagConstruction

end OAI
end


