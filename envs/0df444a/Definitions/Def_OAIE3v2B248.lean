-- Prove2me | Definitions.Def_OAIE3v2B248
-- name    : OAIE3v2B248
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:19:52.521978+00:00
-- url     : https://prove2.me/theorems/53c4eb41-5292-4f10-a800-8eaf84a2770e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 253 of 311
-- statement:
--   Definitions bundle 253 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B237`, `OAIE3v2B238`, `OAIE3v2B239`, `OAIE3v2B240` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateDenseSliceInput.lean`, `Estimates/AllocatedExternalCandidateTaggedPairFamily.lean`, `Estimates/AllocatedExternalRetainedResidual.lean`, `Estimates/AllocatedZeroLayerScalarPassage.lean`, `Estimates/BoundedNativeDependentApproximations.lean`, `Estimates/CommonDependentWordLayers.lean`, `Estimates/ComparableScalarPhysicalFamilyPatch.lean`, `Estimates/InheritedTaggedQuotientPrecenterMasks.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeDependentRepresentativeFamily.lean`, `Estimates/PreparedRelativeEndpointSourceBounds.lean`, `Estimates/UnconditionedArbitraryFixedPatchFamily.lean`, `Geometry/ActualFixedSpatialDenseSliceCenter.lean`, `Geometry/ActualFixedSpatialRetainedModulusBudget.lean`, `Geometry/AllocatedExternalCandidateRefilteredSupportedStep.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/NativeRankRelationExistence.lean`, `Polynomial/CommonDependentPolynomialIntersections.lean`, `Polynomial/NativeDegreePowerBound.lean`, `Probability/AllocatedExternalCandidateAllSiteLaw.lean`, `Probability/AllocatedExternalCandidateRetainedSliceLaw.lean`, `Probability/AllocatedExternalLocalSliceLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B237
import Definitions.Def_OAIE3v2B238
import Definitions.Def_OAIE3v2B239
import Definitions.Def_OAIE3v2B240

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3

theorem exists_native_reduced_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ (q : ℝ) (B : NativeMultilinearIntervalFamily W q) (P : ℝ)
        (D : NativeMixedReductionData B.mixed P),
        Nonempty (NativeReducedIntervalFamily B D ((p + C) ^ C)) := by
  obtain ⟨a, _, hfamily⟩ := exists_native_multilinear_interval_family s
  obtain ⟨b, _, hreduce⟩ := exists_mixed_quadruple_budget s
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Y + (Y + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 0 ≤ (q + b) ^ b := by positivity
  have hcost : q + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Y, q, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨B⟩ := hfamily W hf
  obtain ⟨P, ⟨D⟩, hP, hl, hg⟩ := hreduce B.mixed
  refine ⟨q, B, P, D, B.reduce_with_budget D ?_ ?_ ?_ ?_⟩
  · linarith only [hb, hcost]
  · linarith only [hP, hcost]
  · exact hg.trans (by linarith only [hq, hcost])
  · exact hl.trans (by linarith only [hq, hcost])

end Erdos3

end

section

namespace Erdos3.NativeReducedIntervalFamily

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_fixed_global_term {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
    {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K) :
    ∃ (j : Fin R.globalExpansion.count) (S : Finset R.retained), S.Nonempty ∧
      Real.exp (-(2 * K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (S.card : ℝ) ∧
      ∀ t ∈ S, Real.exp (-(2 * K)) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
        B.rankProduct t.val n * (R.globalExpansion.test j).eval (B.sample t.val n) *
          R.localLower t n‖ := by
  classical
  let rel (t : R.retained) (_ : Unit) (j : Fin R.globalExpansion.count) : Prop :=
    Real.exp (-(2 * K)) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
      B.rankProduct t.val n * (R.globalExpansion.test j).eval (B.sample t.val n) * R.localLower t n‖
  have hnonempty : (Finset.univ : Finset R.retained).Nonempty := by
    obtain ⟨t, ht⟩ := R.retained_nonempty
    exact ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  have hchoice : ∀ t ∈ (Finset.univ : Finset R.retained), ∀ b, ∃ j, rel t b j := by
    intro t _ _
    have hc : Real.exp (-K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
        (B.rankProduct t.val n * R.localLower t n) *
          D.globalError (fun _ => B.coordinate) R.code (B.sample t.val n)‖ := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using R.rank_correlation t
    obtain ⟨j, hj⟩ := R.globalExpansion.select_sample_product_correlation
      (B.intervalSet t.val) (B.sample t.val) (fun n => B.rankProduct t.val n * R.localLower t n) hc
    refine ⟨j, ?_⟩
    rw [show K + K = 2 * K by ring] at hj
    simpa only [rel, mul_assoc, mul_left_comm, mul_comm] using hj
  have hcount : (Fintype.card (Fin R.globalExpansion.count) : ℝ) ≤ Real.exp K := by
    simpa only [Fintype.card_fin] using R.globalExpansion.count_bound
  obtain ⟨j, S, _, hS, hsize, hfixed⟩ :=
    exists_large_fixed_choices Finset.univ hnonempty rel hchoice hcount
  refine ⟨j (), S, hS, ?_, fun t ht => hfixed t ht ()⟩
  calc
    Real.exp (-(2 * K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
        Real.exp (-K) * (Real.exp (-K) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-K) * (R.retained.card : ℝ) :=
      mul_le_mul_of_nonneg_left R.density (Real.exp_nonneg _)
    _ ≤ (S.card : ℝ) := by
      simpa only [Fintype.card_unit, Nat.cast_one, mul_one, Finset.card_univ, Fintype.card_coe] using hsize

end Erdos3.NativeReducedIntervalFamily

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_interval_global_reduction (s : ℕ) :
    ∃ c : ℕ, 2 ≤ c ∧ IntervalGlobalReductionStatement s c := by
  obtain ⟨c, hc, hreduce⟩ := exists_coordinate_error_reduction (Fin 5) s
  refine ⟨c, hc, ?_⟩
  intro r N _ p q P K f W B D R
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  have hinput := intervalSplitInput_bounds hK
  have hinput0 : 0 ≤ intervalSplitInput K := le_trans (by norm_num) hinput.1
  obtain ⟨j, S, hS, hSsize, hcorr⟩ := R.exists_fixed_global_term
  let T := R.globalExpansion.test j
  let F (t : R.retained) (n : ℤ) := B.rankProduct t.val n * R.localLower t n
  have hT : T.ComplexityLE (intervalSplitInput K) :=
    (R.globalExpansion.complexity j).mono hinput.2.1
  have hF : ∀ t ∈ S, ∀ n ∈ B.intervalSet t.val, ‖F t n‖ ≤ Real.exp (intervalSplitInput K) := by
    intro t _ n _
    exact (R.scalar_norm t n).trans (Real.exp_le_exp.mpr hinput.2.2.2)
  have hcorr' : ∀ t ∈ S, Real.exp (-intervalSplitInput K) ≤
      ‖𝔼 n ∈ B.intervalSet t.val, F t n * T.eval
        (Function.update (B.sample t.val 0) (3 : Fin 5) n)‖ := by
    intro t ht
    have h := (Real.exp_le_exp.mpr (neg_le_neg hinput.2.2.1)).trans (hcorr t ht)
    simpa only [F, T, ← B.sample_update, mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨weight, Q, hw, _, hQ, hQsize, hcor⟩ := hreduce (3 : Fin 5) T hinput.1 hT S hS
    (fun t => B.intervalSet t.val) (fun t => B.sample t.val 0) (fun _ n => n) F
    (fun t _ => B.intervalSet_nonempty t.val) hF hcorr'
  refine ⟨weight, Q, hw, hQ, ?_, ?_⟩
  · calc
      Real.exp (-(2 * K + intervalSplitTermBudget c K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
          Real.exp (-intervalSplitTermBudget c K) *
            (Real.exp (-(2 * K)) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-intervalSplitTermBudget c K) * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hSsize (Real.exp_nonneg _)
      _ ≤ (Q.card : ℝ) := hQsize
  · intro t ht
    obtain ⟨v, _, ⟨E⟩, hcv⟩ := hcor t ht
    let w (n : ℤ) := R.localLower t n * v n
    have hL : 0 ≤ intervalErrorBudget K := intervalErrorBudget_nonneg hK
    have hJ : 0 ≤ intervalSplitTermBudget c K := by
      unfold intervalSplitTermBudget
      positivity
    have hL' : intervalErrorBudget K ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by
      linarith only [hJ]
    have hJ' : intervalSplitTermBudget c K ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by
      linarith only [hL]
    have htwo : 2 ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by
      linarith only [hL, hJ]
    refine ⟨w, ⟨?_⟩, ?_⟩
    · exact ((R.localExpansion t).mono hL').mul (E.mono hJ') htwo
    · simpa only [F, w, intervalSplitTermBudget, mul_assoc, mul_left_comm, mul_comm] using hcv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_absorbed_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
      {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
      {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K),
      ∃ (weight : ℤ → ℂ) (Q : Finset R.retained), (∀ n, ‖weight n‖ ≤ 1) ∧ Q.Nonempty ∧
        Real.exp (-((K + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, ∃ v : ℤ → ℂ,
          Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((K + C) ^ C)
            (fun x => v (x ()))) ∧
          Real.exp (-((K + C) ^ C)) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
            B.rankProduct t.val n * weight n * v n‖ := by
  obtain ⟨c, _, hreduce⟩ := exists_interval_global_reduction s
  obtain ⟨C, hC, hbudget⟩ := exists_interval_split_budget c
  refine ⟨C, hC, ?_⟩
  intro r N _ p q P K f W B D R
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  obtain ⟨weight, Q, hw, hQ, hsize, hcor⟩ := hreduce R
  have hF : intervalSplitTermBudget c K ≤ (K + C) ^ C := by
    linarith only [hK, (hbudget K hK).1]
  refine ⟨weight, Q, hw, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (hbudget K hK).1)) (by positivity)).trans hsize
  · intro t ht
    obtain ⟨v, ⟨E⟩, hc⟩ := hcor t ht
    exact ⟨v, ⟨E.mono (hbudget K hK).2⟩, (Real.exp_le_exp.mpr (neg_le_neg hF)).trans hc⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

theorem exists_native_weighted_rank_intervals (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
      {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
      {D : NativeMixedReductionData B.mixed P} (_R : NativeReducedIntervalFamily B D K),
      Nonempty (NativeWeightedRankIntervals W.family B.rankCoordinate B.shifts
        (K + (K + C) ^ C + 2)) := by
  obtain ⟨C, hC, hexists⟩ := exists_absorbed_interval_family s
  refine ⟨C, hC, ?_⟩
  intro r N _ p q P K f W B D R
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  have hpow : 0 ≤ (K + C) ^ C := by positivity
  have hKP : K ≤ K + (K + C) ^ C + 2 := by linarith only [hpow]
  have hPP : (K + C) ^ C ≤ K + (K + C) ^ C + 2 := by linarith only [hK]
  obtain ⟨weight, Q, hw, hQ, hsize, hcor⟩ := hexists R
  classical
  obtain ⟨t₀, ht₀⟩ := hQ
  let : Nonempty Q := ⟨⟨t₀, ht₀⟩⟩
  have hdata (t : Q) := hcor t.val t.property
  choose v hE hv using hdata
  let e := (Fintype.equivFin Q).symm
  let old (i : Fin (Fintype.card Q)) : B.quadruples := (e i).val.val
  refine ⟨{
    budget_two := by linarith only [hK, hpow]
    count := Fintype.card Q
    count_pos := Fintype.card_pos
    index := fun i => (old i).val
    index_injective := ?_
    density := ?_
    first_mem := fun i => (B.interval (old i)).first_mem
    second_mem := fun i => (B.interval (old i)).second_mem
    third_mem := fun i => (B.interval (old i)).third_mem
    fourth_mem := fun i => (B.interval (old i)).fourth_mem
    integer_relation := fun i => (B.interval (old i)).integer_relation
    branch := fun i => (B.interval (old i)).branch
    start := fun i => (B.interval (old i)).start
    length := fun i => (B.interval (old i)).length
    length_pos := fun i => (B.interval (old i)).length_pos
    endpoint_le := fun i => (B.interval (old i)).endpoint_le
    length_short := fun i => (B.interval (old i)).length_short
    length_ratio := fun i => (Real.exp_le_exp.mpr (neg_le_neg hKP)).trans
      (R.interval_length_ratio (e i).val)
    weight := weight
    weight_norm := hw
    lower := fun i => v (e i)
    expansion := fun i => (Classical.choice (hE (e i))).mono hPP
    correlation := fun i => (Real.exp_le_exp.mpr (neg_le_neg hPP)).trans (hv (e i)) }⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hij
  · simpa only [Fintype.card_coe] using
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hPP)) (by positivity)).trans hsize

end Erdos3

end

section

namespace Erdos3

theorem exists_native_rank_relation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)),
        H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
        Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
        Nonempty (NativeRankRelation W.family out H ((p + C) ^ C) ((p + C) ^ C)) := by
  obtain ⟨a, _, hreduce⟩ := exists_native_reduced_interval_family s
  obtain ⟨c, _, habsorb⟩ := exists_native_weighted_rank_intervals s
  obtain ⟨C, hC, hbudget⟩ := exists_rank_relation_budget a c
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  obtain ⟨q, B, P, D, ⟨R⟩⟩ := hreduce W hf
  obtain ⟨F⟩ := habsorb R
  obtain ⟨T⟩ := F.remove_weight
  have hK : 0 ≤ (p + a) ^ a := by positivity
  have hq : q ≤ (p + C) ^ C := by
    have hpow : 0 ≤ ((p + a) ^ a + c) ^ c := by positivity
    linarith only [R.base_budget, (hbudget p hp).1, hK, hpow]
  refine ⟨B.rankCoordinate, B.shifts, B.shifts_subset, B.shifts_nonempty,
    B.shifts_short, ?_, ⟨T.mono (hbudget p hp).1 (hbudget p hp).2⟩⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hq))
    (Nat.cast_nonneg _)).trans B.shifts_density

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_common_rank_relation (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ N →
      ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q : ℝ),
        H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
        Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
        p ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ R : NativeRankRelation W.family out H q q,
          Nonempty (R.CommonData ((p + C) ^ C)) := by
  obtain ⟨a, _, hrelation⟩ := exists_native_rank_relation s
  obtain ⟨c, _, hcommon⟩ := exists_common_rank_relation s hs
  obtain ⟨C, hC, hbudget⟩ := exists_native_common_rank_budget a c
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hbase : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  obtain ⟨hqC, hcommonC⟩ := hbudget p hp
  obtain ⟨out, H, hHW, hH, hshort, hHsize, ⟨R⟩⟩ := hrelation W hf
  let R' : NativeRankRelation W.family out H q q := R.mono hbase hbase
  obtain ⟨D⟩ := hcommon hq hpq R' ((Real.exp_le_exp.mpr hcommonC).trans hN)
  refine ⟨out, H, q, hHW, hH, hshort, ?_, hpq, hqC, R', ⟨D.mono hcommonC⟩⟩
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg (hbase.trans hqC))) (Nat.cast_nonneg _)).trans hHsize

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ ν : Type*} [Fintype ι] [Fintype ν] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_native_dependent_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) (hα₀ : α ≠ 0)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K)
    (v : ν → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) =
      D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f)
    {JH : ℕ} (hJH : 1 ≤ JH) (hvH : ∀ a k i, RationalHeightLE (v a k i) JH)
    {z : ℝ} (hz : 0 ≤ z) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ z)
    (hcols : (Fintype.card ν : ℝ) ≤ z) (hJHz : (JH : ℝ) ≤ Real.exp z)
    (hlz : ((matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l : ℕ) : ℝ) ≤ Real.exp z)
    (hslow : 2 * (((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤ Real.exp z)
    (hN : Real.exp (separationBudget z) ≤ N)
    (hNdep : Real.exp (separationBudget
      (rankDependentInputBudget z + sparseGeneratorBudget (rankDependentInputBudget z))) ≤ N) :
    let β := W.nativeCoefficientCoordinates hs c τ hG α f
    let J := D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
    let Z := rankDependentInputBudget z
    let Q := Z + sparseGeneratorBudget Z
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (Q + ((Q + 2) ^ 3 + (Q + 2) ^ 36)) ∧
      matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l ∣ m ∧
      ∀ h ∈ A.shifts, ∃ e q : ι → ℝ,
        ‖e‖ ≤ (Real.exp Q + Real.exp ((Q + 2) ^ 3 + (Q + 2) ^ 18 + Q)) /
          monomialScale (fun _ : Unit => (N : ℝ)) α ∧ q ∈ realDenominatorGrid m ∧
        β h - β h₀ - e - q ∈ realRationalCoordinateSpan (fourDependentProjection J) := by
  intro β J Z Q
  obtain ⟨m₀, hm₀, hmp₀, hdiv₀, hpairs⟩ := A.exists_native_sparse_approximations h₀ hh₀
    hs hp hP c τ hG l hl hdenom α hα hα₀ f hf v hv hJH hvH hz hfour hcols hJHz hlz hslow hN
  obtain ⟨hZ, hzZ, h2zZ, hdenZ, hslowZ⟩ := rankDependentInputBudget_bounds hz
  have hZQ : Z ≤ Q := le_add_of_nonneg_right (sparseGeneratorBudget_nonneg hZ)
  have hdim : (Fintype.card ι : ℝ) ≤ z := by
    have hcard : Fintype.card ι ≤ Fintype.card (Σ _ : Fin 4, ι) :=
      Fintype.card_le_of_injective (fun i : ι => (⟨0, i⟩ : Σ _ : Fin 4, ι))
        (fun _ _ h => congrArg (fun j : Σ _ : Fin 4, ι => j.2) h)
    exact (Nat.cast_le.mpr hcard).trans hfour
  have hselected (K : Finset (Fin 4)) : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ Z :=
    ((Nat.cast_le.mpr (card_selected_four_le K)).trans hfour).trans hzZ
  have hdoublecols : (Fintype.card (ν ⊕ ν) : ℝ) ≤ Z := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  obtain ⟨m, hm, hmp, hdiv, hsolve⟩ := exists_dependent_coordinate_corrections J v hv hJH hm₀ hvH
    hZ (hdim.trans hzZ) (hselected _) (hselected _) hdoublecols
    (hJHz.trans (Real.exp_le_exp.mpr hzZ)) (hmp₀.trans (Real.exp_le_exp.mpr hdenZ))
    (fun _ : Unit => (N : ℝ)) (fun _ => hNdep)
  refine ⟨m, hm, hmp, hdiv₀.trans hdiv, ?_⟩
  intro h hh
  obtain ⟨e₁, q₁, e₂, q₂, he₁, he₂, hq₁, hq₂, hres₁, hres₂⟩ := hpairs h hh
  have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) α :=
    monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) α
  have hcost : 2 * (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) ≤ Real.exp Q :=
    hslowZ.trans (Real.exp_le_exp.mpr hZQ)
  have hsingle : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤ Real.exp Q := by
    linarith [Real.exp_pos z, Real.exp_pos ((z + 2) ^ 3 + (z + 2) ^ 18 + z)]
  have hfirst : ‖e₁‖ ≤ Real.exp Q / monomialScale (fun _ : Unit => (N : ℝ)) α :=
    he₁.trans (div_le_div_of_nonneg_right hsingle hscale.le)
  have hdiff : ‖e₂ - e₁‖ ≤ Real.exp Q / monomialScale (fun _ : Unit => (N : ℝ)) α := by
    calc
      ‖e₂ - e₁‖ ≤ ‖e₂‖ + ‖e₁‖ := norm_sub_le _ _
      _ ≤ (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
            monomialScale (fun _ : Unit => (N : ℝ)) α +
          (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
            monomialScale (fun _ : Unit => (N : ℝ)) α := add_le_add he₂ he₁
      _ = (2 * (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) /
          monomialScale (fun _ : Unit => (N : ℝ)) α := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hcost hscale.le
  exact hsolve α hα₀ (β h - β h₀) e₁ e₂ q₁ q₂ hres₁ hres₂ hfirst hdiff hq₁ hq₂

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_bounded_native_dependent_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P) (hbP : b ≤ P) (hpP : p ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l) (hlP : (l : ℝ) ≤ Real.exp P)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) (hα₀ : α ≠ 0)
    (hN : Real.exp (nativeCoordinateSeparationBudget s P) ≤ N) :
    ∃ m : ℕ, m ≤ W.dim ∧
      ∃ f : Basis (Fin m) ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2),
        (∀ i j, rationalLogHeight
          (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) ≤
          (P + 3) ^ 7) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp (nativeDependentDenominatorBudget s P) ∧ l ∣ n ∧
          ∀ h ∈ A.shifts, ∃ e q : Fin m → ℝ,
            ‖e‖ ≤ Real.exp (nativeDependentSlowBudget s P) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
            q ∈ realDenominatorGrid n ∧
            W.nativeCoefficientCoordinates hs c τ hG α f h -
                W.nativeCoefficientCoordinates hs c τ hG α f h₀ - e - q ∈
              realRationalCoordinateSpan (fourDependentProjection
                (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f)) := by
  have heval : α () ≠ 0 := by
    intro hzero
    apply hα₀
    apply Finsupp.ext
    intro u
    cases u
    exact hzero
  let d : Fin (s + 1) := ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩
  have hd : 1 ≤ d.val := Finsupp.le_weight_of_ne_zero' (fun _ : Unit => 1) heval
  obtain ⟨m, hm, f, hf, v, hv, hvH⟩ := D.exists_bounded_coordinate_generators hP hbP d hd
  let K := ⌈Real.exp ((P + 3) ^ 7)⌉₊
  let JH := ⌈Real.exp (horizontalCoordinateBudget P)⌉₊
  let z := nativeCoordinateInputBudget s P
  have hdim : (W.dim : ℝ) ≤ P := W.complexity.1.1.trans hbP
  have hK : (K : ℝ) ≤ Real.exp ((P + 3) ^ 7 + 1) := ceil_exp_le_exp_add_one (by positivity)
  obtain ⟨_, h4PU, _, _, hGU, _⟩ := nativeCoordinateBaseBudget_bounds s hP
  have hUz := (nativeCoordinateInputBudget_bounds s hP).1
  have hcount (a : ℕ) (ha : a ≤ W.dim) : (Fintype.card (Σ _ : Fin 4, Fin a) : ℝ) ≤ z := by
    have haP : (a : ℝ) ≤ P := (Nat.cast_le.mpr ha).trans hdim
    have h4 : 4 * (a : ℝ) ≤ z :=
      (mul_le_mul_of_nonneg_left haP (by norm_num : (0 : ℝ) ≤ 4)).trans (h4PU.trans hUz)
    simpa [Fintype.card_sigma] using h4
  have hJHz : (JH : ℝ) ≤ Real.exp z :=
    (ceil_exp_le_exp_add_one (horizontalCoordinateBudget_nonneg hP)).trans
      (Real.exp_le_exp.mpr (hGU.trans hUz))
  have hden : ((matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l : ℕ) : ℝ) ≤
      Real.exp z := nativeCoordinate_denominator_bound s hP _ l hlP
        (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hm).trans hdim)
        (by simpa only [Fintype.card_fin] using hdim) hf
  obtain ⟨hN₁, hN₂⟩ := nativeCoordinateSeparationBudget_cutoffs s hP hN
  obtain ⟨n, hn, hnp, hln, hsolve⟩ := A.exists_native_dependent_approximations h₀ hh₀ hs hp hP
    c τ hG l hl hdenom α hα hα₀ f (fun i j => rationalHeightLE_ceil_exp (hf i j))
    v hv (one_le_ceil_exp _) (fun a k i => rationalHeightLE_ceil_exp (hvH a k i))
    (nativeCoordinateInputBudget_nonneg s hP) (hcount m hm)
    (by simpa only [Fintype.card_fin] using hcount W.dim le_rfl) hJHz hden
    (nativeCoordinate_slow_bound s hP hpP W.dim K hdim hK) hN₁ hN₂
  refine ⟨m, hm, f, hf, n, hn, ?_, (dvd_mul_left l _).trans hln, ?_⟩
  · simpa only [nativeDependentDenominatorBudget, nativeDependentBudget, add_assoc] using hnp
  · intro h hh
    obtain ⟨e, q, he, hq, hres⟩ := hsolve h hh
    refine ⟨e, q, ?_, hq, hres⟩
    have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) α :=
      monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) α
    exact he.trans (div_le_div_of_nonneg_right (nativeDependentSlowBudget_bound s hP) hscale.le)

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreePowerBound
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_uniform_native_degree_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P) (hbP : b ≤ P) (hpP : p ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l) (hlP : (l : ℝ) ≤ Real.exp P)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (hN : Real.exp (nativeCoordinateSeparationBudget s P) ≤ N) :
    let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
    ∃ m : Fin s → ℕ, (∀ d, m d ≤ W.dim) ∧
      ∃ f : ∀ d, Basis (Fin (m d)) ℚ
        (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2),
        (∀ d i j, rationalLogHeight
          ((f d).repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2).mkQ
            (W.model.basis j)) i) ≤ (P + 3) ^ 7) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((s : ℝ) * nativeDependentDenominatorBudget s P) ∧ l ∣ n ∧
          ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
            ∃ e q : Fin (m d) → ℝ,
              ‖e‖ ≤ Real.exp (nativeDependentSlowBudget s P) /
                monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧ q ∈ realDenominatorGrid n ∧
              W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h -
                  W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h₀ - e - q ∈
                realRationalCoordinateSpan (fourDependentProjection
                  (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩ (f d))) := by
  classical
  intro α
  have hdegree (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  have hnonzero (d : Fin s) : α d ≠ 0 := by
    intro hz
    have h := congrArg (fun x : Unit →₀ ℕ => x ()) hz
    simp [α] at h
  have hchoice (d : Fin s) := A.exists_bounded_native_dependent_approximations h₀ hh₀
    hs hp hP hbP hpP c τ hG l hl hlP hdenom (α d) (hdegree d) (hnonzero d) hN
  choose m hm f hf n hn hnB hln happrox using hchoice
  let n₀ : ℕ := ∏ d : Fin s, n d
  have hn₀ : 0 < n₀ := Finset.prod_pos (fun d _ => hn d)
  have hn₀B : (n₀ : ℝ) ≤ Real.exp ((s : ℝ) * nativeDependentDenominatorBudget s P) := by
    change ((∏ d : Fin s, n d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      ∏ d : Fin s, (n d : ℝ) ≤ ∏ _d : Fin s, Real.exp (nativeDependentDenominatorBudget s P) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun d _ => hnB d)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have hdvd (d : Fin s) : n d ∣ n₀ := Finset.dvd_prod_of_mem n (Finset.mem_univ d)
  let d₀ : Fin s := ⟨0, by omega⟩
  refine ⟨m, hm, f, hf, n₀, hn₀, hn₀B, (hln d₀).trans (hdvd d₀), ?_⟩
  intro d hd h hh
  obtain ⟨e, q, he, hq, hres⟩ := happrox d h hh
  exact ⟨e, q, he, realDenominatorGrid_subset_of_dvd (hn d) (hdvd d) hq, hres⟩

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_degree_approximation_bound (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {b p q P : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}
      (A : D.SparseAnchors) (h₀ : ZMod N), h₀ ∈ A.shifts →
      0 ≤ p → 0 ≤ P → b ≤ P → p ≤ P →
      ∀ (c : Basis κ ℚ W.L) (τ : κ → ℕ)
        (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
        (l : ℕ), 0 < l → (l : ℝ) ≤ Real.exp P →
        (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l) →
        Real.exp ((P + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ m : Fin s → ℕ, (∀ d, m d ≤ W.dim) ∧
          ∃ f : ∀ d, Basis (Fin (m d)) ℚ
            (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2),
            (∀ d i j, rationalLogHeight
              ((f d).repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2).mkQ
                (W.model.basis j)) i) ≤ (P + C) ^ C) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((P + C) ^ C) ∧ l ∣ n ∧
              ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
                ∃ e q : Fin (m d) → ℝ,
                  ‖e‖ ≤ Real.exp ((P + C) ^ C) / monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧
                  q ∈ realDenominatorGrid n ∧
                  W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h -
                      W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h₀ - e - q ∈
                    realRationalCoordinateSpan (fourDependentProjection
                      (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩ (f d))) := by
  obtain ⟨C, hC, hbudget⟩ := exists_native_coordinate_polynomial_budget s
  refine ⟨C, hC, ?_⟩
  intro κ r N _ b p q P W out H R D A h₀ hh₀ hp hP hbP hpP c τ hG l hl hlP hdenom hN α
  obtain ⟨hcut, hden, hslow, hf⟩ := hbudget P hP
  obtain ⟨m, hm, f, hfheight, n, hn, hnB, hln, happrox⟩ :=
    A.exists_uniform_native_degree_approximations h₀ hh₀ hs hp hP hbP hpP c τ hG l hl hlP hdenom
      ((Real.exp_le_exp.mpr hcut).trans hN)
  have hden0 : 0 ≤ nativeDependentDenominatorBudget s P := by
    have hQ := nativeDependentBudget_nonneg s hP
    unfold nativeDependentDenominatorBudget
    positivity
  have hden' : (s : ℝ) * nativeDependentDenominatorBudget s P ≤ (P + C) ^ C :=
    (mul_le_mul_of_nonneg_right (by linarith : (s : ℝ) ≤ (s : ℝ) + 1) hden0).trans hden
  refine ⟨m, hm, f, (fun d i j => (hfheight d i j).trans hf), n, hn,
    hnB.trans (Real.exp_le_exp.mpr hden'), hln, ?_⟩
  intro d hd h hh
  obtain ⟨e, q, he, hq, hres⟩ := happrox d hd h hh
  refine ⟨e, q, ?_, hq, hres⟩
  have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) (α d) :=
    monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) (α d)
  exact he.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hslow) hscale.le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDependentRepresentativeFamily
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_coordinate_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors) (h₀ : ZMod N),
            h₀ ∈ A.shifts ∧ A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ m : Fin s → ℕ, (∀ d, m d ≤ W.family.dim) ∧
              ∃ f : ∀ d, Basis (Fin (m d)) ℚ
                (W.family.L ⧸ W.family.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2),
                (∀ d i j, rationalLogHeight
                  ((f d).repr ((W.family.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2).mkQ
                    (W.family.model.basis j)) i) ≤ (p + C) ^ C) ∧
                ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                  (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
                  ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
                    ∃ e u : Fin (m d) → ℝ,
                      ‖e‖ ≤ Real.exp ((p + C) ^ C) / monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧
                      u ∈ realDenominatorGrid n ∧
                      W.family.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h -
                          W.family.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h₀ - e - u ∈
                        realRationalCoordinateSpan (fourDependentProjection
                          (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩ (f d))) ∧
                      ∃ z ∈ (fourDependentProjection
                          (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ,
                        W.family.rank.filtration.realHigherHorizontalCoordinates
                            (Finsupp.weight (fun _ : Unit => 1) (α d)) (f d)
                            (W.family.horizontalCoefficient hs c τ hG (α d) h -
                              W.family.horizontalCoefficient hs c τ hG (α d) h₀ - z) = e + u := by
  obtain ⟨a, _, hcommon⟩ := exists_native_common_rank_relation s hs
  obtain ⟨b, _, hdegrees⟩ := exists_native_degree_approximation_bound s hs
  obtain ⟨C, hC, hbudget⟩ := exists_native_dependent_selection_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let P₀ := (p + a) ^ a
  let P := (P₀ + 2) ^ 3 + 2 * P₀
  have hP₀ : 0 ≤ P₀ := by dsimp only [P₀]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hP₀P : P₀ ≤ P := by
    have hc : 0 ≤ (P₀ + 2) ^ 3 := by positivity
    dsimp only [P]
    linarith
  obtain ⟨hP₀C, h2PC, hdegreeC⟩ := hbudget p hp
  have hPC : P ≤ (p + C) ^ C := by linarith
  obtain ⟨out, H, q, hHW, hH, hshort, _, hpq, hqP₀, R, ⟨D₀⟩⟩ :=
    hcommon W hF ((Real.exp_le_exp.mpr hP₀C).trans hN)
  obtain ⟨D, l, _, _, hl, hlbound, hdenom⟩ := D₀.exists_common_projected_denominator hP₀
  have hqP : q ≤ P := hqP₀.trans hP₀P
  have hpP : p ≤ P := hpq.trans hqP
  have hlP : (l : ℝ) ≤ Real.exp P := by
    apply hlbound.trans
    apply Real.exp_le_exp.mpr
    dsimp only [P]
    linarith
  obtain ⟨A⟩ := D.exists_sparse_anchors
  obtain ⟨h₀, hh₀⟩ := A.nonempty
  obtain ⟨m, hm, f, hf, n, hn, hnB, hln, happrox⟩ := hdegrees A h₀ hh₀
    (hp.trans hpq) hP hpP hqP c τ hG l hl hlP hdenom
    ((Real.exp_le_exp.mpr hdegreeC).trans hN)
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
    hh₀, A.shifts_subset.trans hHW, ?_, m, hm, f, (fun d i j => (hf d i j).trans hdegreeC),
    n, hn, hnB.trans (Real.exp_le_exp.mpr hdegreeC), ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h2PC))
      (Nat.cast_nonneg _)).trans A.density
  · intro t ht
    rw [hdenom t ht]
    exact hln
  · intro d hd h hh
    obtain ⟨e, u, he, hu, hres⟩ := happrox d hd h hh
    obtain ⟨z, hz, hcoords⟩ := D.exists_native_dependent_remainder hs c τ hG (α d) hd (f d) h h₀ e u hres
    refine ⟨e, u, ?_, hu, hres, z, hz, hcoords⟩
    have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) (α d) :=
      monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) (α d)
    exact he.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hdegreeC) hscale.le)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_representative_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors) (h₀ : ZMod N),
            h₀ ∈ A.shifts ∧ A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
                ∃ E Q : (W.family.rank.filtration.layer
                    (Finsupp.weight (fun _ : Unit => 1) (α d)) 1).baseChange ℝ,
                  ‖(W.family.model.basis.baseChange ℝ).equivFun E.val‖ ≤
                    Real.exp ((p + C) ^ C) / monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧
                  (W.family.model.basis.baseChange ℝ).equivFun Q.val ∈ realDenominatorGrid n ∧
                  W.family.horizontalCoefficient hs c τ hG (α d) h -
                      W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
                      W.family.rank.filtration.realHorizontalMap
                        (Finsupp.weight (fun _ : Unit => 1) (α d)) E -
                      W.family.rank.filtration.realHorizontalMap
                        (Finsupp.weight (fun _ : Unit => 1) (α d)) Q ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨a, _, hfamily⟩ := exists_native_dependent_coordinate_family s hs
  obtain ⟨C, hC, hbudget⟩ := exists_native_horizontal_lift_budget s a
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  let L := (B + 3) ^ 4
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBL : B ≤ L := by
    have h := le_power_budget (p := B + 1) (by linarith) (by decide : 1 ≤ 4)
    have heq : B + 1 + 2 = B + 3 := by ring
    rw [heq] at h
    exact (by linarith : B ≤ B + 1).trans h
  obtain ⟨hBC, hcut, hslow, hden⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A, h₀,
      hh₀, hAW, hdensity, k, hk, f, hf, n, hn, hnB, hproj, happrox⟩ :=
    hfamily W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B := hpq.trans (hqP.trans hPB)
  have hdegree (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) = d.val + 1 := by
    simp only [α, Finsupp.weight_single, smul_eq_mul, mul_one]
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    rw [hdegree]
    omega
  have hpos (d : Fin s) : 1 ≤ Finsupp.weight (fun _ : Unit => 1) (α d) := by
    rw [hdegree]
    omega
  have hnonzero (d : Fin s) : α d ≠ 0 := by
    simp only [α, ne_eq, Finsupp.single_eq_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, not_false_eq_true]
  have hrep (d : Fin s) := W.family.rank.exists_controlled_horizontal_representatives
    ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le (hd d)⟩ (hpos d) hB
    (W.family.complexity.mono W.family.rank hpB) (hk d) (f d) (hf d) hn hnB
    (fun _ : Unit => (N : ℝ)) (fun _ => (Real.exp_le_exp.mpr hcut).trans hN)
  choose m hm hmB hnm hsolve using hrep
  let M₀ := ∏ d, m d
  have hM₀ : 0 < M₀ := Finset.prod_pos (fun d _ => hm d)
  have hM₀B : (M₀ : ℝ) ≤ Real.exp ((s : ℝ) * (L + ((L + 2) ^ 3 + (L + 2) ^ 36))) := by
    calc
      _ = ∏ d, (m d : ℝ) := by rw [Nat.cast_prod]
      _ ≤ ∏ _d : Fin s, Real.exp (L + ((L + 2) ^ 3 + (L + 2) ^ 36)) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun d _ => hmB d)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have hmM₀ (d : Fin s) : m d ∣ M₀ := Finset.dvd_prod_of_mem m (Finset.mem_univ d)
  have hnM : n ∣ n * M₀ := dvd_mul_right _ _
  have hmM (d : Fin s) : m d ∣ n * M₀ := (hmM₀ d).trans (dvd_mul_left _ _)
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC,
    R, D, A, h₀, hh₀, hAW, ?_, n * M₀, Nat.mul_pos hn hM₀, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · calc
      ((n * M₀ : ℕ) : ℝ) ≤ Real.exp B *
          Real.exp ((s : ℝ) * (L + ((L + 2) ^ 3 + (L + 2) ^ 36))) := by
        rw [Nat.cast_mul]
        exact mul_le_mul hnB hM₀B (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (B + s * (L + ((L + 2) ^ 3 + (L + 2) ^ 36))) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hden
  · intro t ht
    exact (hproj t ht).trans hnM
  · intro d hd' h hh
    obtain ⟨e, u, he, hu, _, z, hz, hcoords⟩ := happrox d hd' h hh
    have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) (α d) :=
      monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) (α d)
    obtain ⟨E, Q, _, _, hres, hE, hQ⟩ := hsolve d (α d) (hnonzero d)
      (W.family.horizontalCoefficient hs c τ hG (α d) h)
      (W.family.horizontalCoefficient hs c τ hG (α d) h₀) z e u hcoords
      (he.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hBL) hscale.le)) hu
    refine ⟨E, Q, ?_, realDenominatorGrid_subset_of_dvd (hm d) (hmM d) hQ, ?_⟩
    · exact hE.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hslow) hscale.le)
    · rw [hres]
      exact hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem dependentWordLayer_antitone {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    D.dependentWordLayer e m n ≤ D.dependentWordLayer d k l :=
  markedLieSpan_antitone _ _ _ hde hkm hln

theorem dependentFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.dependentFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 1 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact markedLieSpan_leaf D.coefficientFreeGenerator D.coefficientWeight
    D.coefficientIsDependent (Sum.inr ⟨d, i⟩)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonDependentPolynomialIntersections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem coefficientFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.coefficientFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 0 1 :=
  sup_le (D.commonFreeSpan_le_dependentWordLayer d)
    ((D.dependentFreeSpan_le_dependentWordLayer d).trans
      (D.dependentWordLayer_antitone le_rfl (Nat.zero_le 1) le_rfl))

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ) (u : Fin t → ℝ)

noncomputable def realAffineMarkedBase (j : Fin s) :
    (D.dependentPolynomialLayer (σ := Fin t) (j.val + 1) 0 1).baseChange ℝ :=
  ⟨realAffinePolynomial (x j).val (fun i => (y j i).val),
    realAffinePolynomial_mem_marked D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
      (Submodule.baseChange_mono ℝ (D.coefficientFreeSpan_le_dependentWordLayer j) (x j).property)
      (fun i => Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_dependentWordLayer j) (y j i).property)⟩

noncomputable def realAffineMarkedSlope (j : Fin s) :
    (D.dependentPolynomialLayer (σ := Fin t) (j.val + 1) 1 1).baseChange ℝ := by
  let z := ∑ i, u i • (y j i).val
  refine ⟨(monomialLinearMap (0 : Fin t →₀ ℕ)).baseChange ℝ z, ?_⟩
  apply realMonomial_mem_markedPolynomialLayer
  simp only [map_zero, Nat.add_zero]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_dependentWordLayer j) (y j i).property

noncomputable def commonAffineMarkedOrbit : (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
  realMarkedAffineMixedOrbit D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t 1 (D.realAffineMarkedBase t x y) (D.realAffineMarkedSlope t y u)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialDenseSliceCenter
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

attribute [instance] ActualFixedSpatialDenseSliceInput.keepDecidable

namespace ActualFixedSpatialDenseSliceInput
variable {s q} (input : ActualFixedSpatialDenseSliceInput s q)

omit [DecidableEq X] in
theorem kernel_geometry (g : G) :
    2 ≤ input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ ∧
    0 ≤ (input.box.start ⟨Sum.inl g,input.kernel_kept g⟩ : ℝ) / S.value ∧
    Real.exp (-input.cost) / 2 ≤
      (input.step : ℝ) * (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ - 1 : ℕ) / S.value ∧
    (input.box.start ⟨Sum.inl g,input.kernel_kept g⟩ : ℝ) / S.value +
      (input.step : ℝ) * (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ - 1 : ℕ) / S.value < 1 ∧
    (input.step : ℝ) * (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ - 1 : ℕ) / S.value ≤ 1 ∧
    (input.step : ℝ) ≤ 2 * Real.exp input.cost :=
  input.box.denseCoordinate_geometry ⟨Sum.inl g,input.kernel_kept g⟩ input.step_pos
    S.positive (input.dense _) input.late_floor

omit [DecidableEq X] in
theorem principal_geometry
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    0 ≤ input.principalLower a p ∧
      Real.exp (-input.cost) / 2 ≤ input.principalWidth a p ∧
      |input.principalLower a p| + |input.principalWidth a p| ≤ 1 := by
  have heq := allocatedPrincipalSides_not_short B U b S a p
  have hf : 2 ≤ Real.exp (-input.cost) *
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) (Sum.inr ⟨a.val,p⟩) : ℕ) : ℝ) := by
    simpa only [Sum.elim_inr, heq] using input.late_floor
  have hg := input.box.fiberParameter_dense_geometry input.fixed
    (Sum.inr ⟨a.val,p⟩) (input.active_kept a p) input.step_pos
    (side_pos (S := S) _) (input.dense ⟨Sum.inr ⟨a.val,p⟩,input.active_kept a p⟩) hf
  exact ⟨hg.2.1, hg.2.2.1, hg.2.2.2.2⟩

omit [DecidableEq X] in
theorem step_le : (input.step : ℝ) ≤ 2 * Real.exp input.cost := by
  obtain ⟨g⟩ := input.kernel_nonempty
  exact (input.kernel_geometry g).2.2.2.2.2

end ActualFixedSpatialDenseSliceInput

namespace ActualFixedSpatialForecastPath

variable {s q} {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δbase s.P s.Pbad PpresBase)

noncomputable def toDenseSliceMember (input : ActualFixedSpatialDenseSliceInput s q) :
    ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q := by
  classical
  let origin : ∀ p : path.primes, LayerSamplerLongVariables
      (allocatedShortAxis (I := I) U b S.value) G B → ZMod (p.val ^ path.exponent p.val) :=
    fun p v => ((Sum.elim
      (fun g => (input.box.start ⟨Sum.inl g,input.kernel_kept g⟩ : ℤ))
      (fun a => input.box.fiberParameterStart input.fixed (Sum.inr ⟨a.1.val,a.2⟩)) v : ℤ) :
        ZMod (p.val ^ path.exponent p.val))
  have hpres : ((∏ p : path.primes, p.val ^ padicValNat p.val input.step : ℕ) : ℝ) ≤
      Real.exp s.Ppres :=
    (arbitraryStep_prescribed_product_exp_le path.primes path.prime input.step_pos input.step_le).trans
      (Real.exp_le_exp.mpr input.prescribed_log)
  let newpath := path.reparameterize δslice s.Ppres input.commonTuple
    (fun p => padicValNat p input.step) origin hpres
    input.principalLower input.principalWidth
    (fun a p => input.active_width.trans (input.principal_geometry a p).2.1)
    (fun a p => (input.principal_geometry a p).1)
    (fun a p => (input.principal_geometry a p).2.2)
  let slice := newpath.withResidueBoxSlice input.box input.length_pos input.fixed input.fixed_inside
    input.kernel_kept input.active_kept input.step_pos (fun g => (input.kernel_geometry g).1)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨slice, ?_, ?_, ?_⟩
  · intro a
    have hdense (k : {k // input.keep k}) : q.δ *
        ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℝ) ≤ input.box.length k :=
      (mul_le_mul_of_nonneg_right input.density_le (Nat.cast_nonneg _)).trans (input.dense k)
    have hregular := input.box.fiberParameter_regular_of_threshold hdense input.step_pos
      (fun k hk => (input.keep_iff k).mpr hk)
      (fun p : B ⟨(selected a).1,Sum.inr (selected a).2⟩ × Fin ((selected a).1.val + 1) =>
        Sum.inr (⟨⟨(selected a).1,Sum.inr (selected a).2⟩,p⟩ : PrincipalTupleIndex B (layerSamplerDegree I n)))
    rcases hregular with ⟨⟨i,v⟩,hsmall⟩ | ⟨hd,hs⟩
    · exact Or.inl ⟨i,v,hsmall⟩
    · exact Or.inr ⟨fun i v => hd (i,v), fun i v => hs (i,v)⟩
  · intro a i v
    exact (Nat.cast_le.mpr (ResidueBoxSlice.fiberParameterStride_le (keep := input.keep)
      (q := input.step) (Sum.inr ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩))).trans
        (input.step_le.trans input.stride_cap)
  · intro g
    exact input.kernel_exp_width.trans (input.kernel_geometry g).2.2.1

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialForecastPath

variable {s q} {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δbase s.P s.Pbad PpresBase)

omit [Fintype Tsp] in

@[simp] theorem toDenseSliceMember_center (input : ActualFixedSpatialDenseSliceInput s q) :
    (path.toDenseSliceMember input).slice.path.center = path.center := rfl

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalLocalSliceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem localLaw_complexMean_parameter (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    C.localLaw.complexMean (fun site => f site.val) =
      𝔼 u ∈ C.slice.integerPoints, f (C.parameter u) := by
  rw [localLaw, FiniteProbabilityWeights.complexMean_finitePushforward]
  exact FiniteProbabilityWeights.uniformFinset_complexMean _ _ (fun u => f (C.parameter u))

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "Γ" => A.frozenTaggedContext hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  periodCap coverCap Lip

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)

theorem localLaw_complexMean_eq_fullSliceLaw
    (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    C.localLaw.complexMean (fun site => f site.val) =
      (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
        (fun t => f (C.parameter t.val)) := by
  rw [C.localLaw_complexMean_parameter,
    C.slice.fullSliceLaw_complexMean_eq_expect_points _ C.step_pos,
    ← C.slice.fullSlicePoints_image_val]
  exact Finset.expect_image Subtype.val_injective.injOn

end AllocatedExternalLocalChart

namespace AllocatedFrozenTaggedPairInput

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)
    {LG MG LM : Type u} [LieRing LG] [LieAlgebra ℚ LG]
    [LieRing MG] [LieAlgebra ℚ MG] [LieRing LM] [LieAlgebra ℚ LM]
    {s d e t : ℕ} {D : RationalFilteredNilmanifold LG s d}
    {E : RationalFilteredNilmanifold MG s e} {Fmark : NilpotentLieFiltration LM t}
    {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (reference : D.Niltest (fullTaggedVariableWeight (X := X) J))
    (partner : E.Niltest (fullTaggedVariableWeight (X := X) J))
    (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    {p : ℝ} (hp : 0 ≤ p) (hcost : cost ≤ p)
    (hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hV : reference.ComplexityLE p) (hW : partner.ComplexityLE p)
    (hWnorm : partner.normBound ≤ 1)
    (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      reference.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * reference.observable x)
    (hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
      partner.observable (z • x) = CircleFourier.character
        ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * partner.observable x)
    (hK : (Fintype.card C.Variables : ℝ) ≤ p)

variable (hcorr : Real.exp (-p) ≤
  ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
    star (twist.eval N poly (C.physical t.val)) *
      (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖)

def ofCandidate_of_localLaw
    (hcorr : Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
      star (twist.eval N poly (A.physical C.path site)) *
        (reference.observable (candidate.value (C.retainedParameter site.val)) *
          partner.eval (fullTaggedPhysicalIntegerPoint J poly
            (fun j => (C.centerLift j).val) (A.physical C.path site))))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p := by
  apply ofCandidate A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall C candidate
    reference partner twist hp hcost hperiod hvariation hV hW hWnorm
    η θ hηheight hθheight hη hθ hK
  have he := C.localLaw_complexMean_eq_fullSliceLaw (fun x =>
    star (twist.eval N poly (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter x)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))))
  change Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
    star (twist.eval N poly (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter site.val)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val)))))‖ at hcorr
  rw [he] at hcorr
  have hf : (fun t : integerBox (fun i : C.Variables => A.sides i.val) =>
      star (twist.eval N poly (C.physical t.val)) *
        (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val))) =
      (fun t => star (twist.eval N poly
        (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))) *
          (reference.observable (candidate.value (C.retainedParameter (C.parameter t.val))) *
            partner.eval (fullTaggedPhysicalIntegerPoint J poly
              (fun j => (C.centerLift j).val)
              (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))))) := by
    funext t
    rw [C.retainedParameter_parameter,
      C.chartValues_eq_physicalIntegerPoint hσ1 Cgeo hCgeo hchart hsmall hpoly t.val t.property]
    rfl
  rw [hf]
  exact hcorr

end AllocatedFrozenTaggedPairInput

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateTaggedPairFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Ω Pivot D E Fmark φ marked
      keep cost p periodCap coverCap Lip)

def input (a : Ω) (j : Pivot) :
    AllocatedFrozenTaggedPairInput F.context Deck keep D (E j) p :=
  AllocatedFrozenTaggedPairInput.ofCandidate_of_localLaw A
    F.hpoly F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    (F.chart a) (F.candidate a) (F.reference a j) (F.selected j) (F.twist a j)
    F.hp F.hcost (F.hperiod a j) F.hvariation (F.hV a j) (F.hW j) (F.hWnorm j)
    (F.η j) (F.θ j) (F.hηheight j) (F.hθheight j) (F.hη a j) (F.hθ j) F.hK
    (by rw [F.chart_localLaw]; exact F.hcorr a j)

@[simp] theorem input_η (a : Ω) (j : Pivot) : (F.input a j).η = F.η j := rfl

@[simp] theorem input_θ (a : Ω) (j : Pivot) : (F.input a j).θ = F.θ j := rfl

@[simp] theorem input_V_orbit (a : Ω) (j : Pivot) :
    (F.input a j).V.orbit = (F.candidate a).orbit := rfl

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateRetainedSliceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (points : Finset (C.Variables → ℤ))
    (hpoints : points.Nonempty)
    (hbox : points ⊆ integerBox (fun i : C.Variables => A.sides i.val))

noncomputable def retainedSite (u : points) : A.Site :=
  C.site u.val (hbox u.property)

@[simp] theorem retainedSite_val (u : points) :
    (C.retainedSite points hbox u).val = C.parameter u.val := rfl

@[simp] theorem physical_retainedSite (u : points) :
    A.physical C.path (C.retainedSite points hbox u) = C.physical u.val := rfl

@[simp] theorem retainedParameter_retainedSite (u : points) :
    C.retainedParameter (C.retainedSite points hbox u).val = u.val :=
  C.retainedParameter_parameter u.val

noncomputable def retainedLaw : FiniteProbabilityWeights A.Site :=
  (FiniteProbabilityWeights.uniformFinset points hpoints).finitePushforward
    (C.retainedSite points hbox)

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

noncomputable def siteLaw (z : out.retained) : FiniteProbabilityWeights A.Site :=
  (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw
    (out.slice z).integerPoints (out.dense z).nonempty
    (out.slice z).integerPoints_subset_integerBox

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateDenseSliceInput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore)

variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
    {Dmod : ℕ} {Selection : Type} [Fintype Selection]
    {selected : Selection → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod selected τ δslice)
    (qnum : ActualFixedSpatialSlicedForecastNumerics s)
    (z : out.retained)
    (hkeep : ∀ k, (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔
      qnum.Hchild ≤ A.sides k)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (hkernel : Nonempty G)
    (hcutoff : qnum.Hchild ≤ S.value)
    (hlate : 2 ≤ Real.exp (-outputCost) * (S.value : ℝ))
    (hdensity : qnum.δ ≤ Real.exp (-outputCost))
    (hactive : δslice ≤ Real.exp (-outputCost) / 2)
    (hlog : outputCost + 1 ≤ qnum.v)
    (hprescribed : outputCost + 1 ≤ s.Ppres)
    (hstride : 2 * Real.exp outputCost ≤ qnum.Ptail)

noncomputable def denseSliceInput : ActualFixedSpatialDenseSliceInput s qnum := by
  classical
  exact
    { keep := (P.chart ⟨z.val, out.subset z.property⟩).keep
      keep_iff := hkeep
      step := out.step z
      step_pos := out.step_pos z
      box := out.slice z
      fixed := (P.chart ⟨z.val, out.subset z.property⟩).fixed
      fixed_inside := (P.chart ⟨z.val, out.subset z.property⟩).fixed_in_box
      commonTuple := commonTuple
      cost := outputCost
      dense := (out.slice z).length_lower_of_dense (out.step_pos z) (out.dense z)
      kernel_nonempty := hkernel
      cutoff_le := hcutoff
      late_floor := hlate
      density_le := hdensity
      active_width := hactive
      kernel_log := hlog
      prescribed_log := hprescribed
      stride_cap := hstride }

@[simp] theorem denseSliceInput_cost :
    (out.denseSliceInput s qnum z hkeep commonTuple hkernel hcutoff hlate hdensity
      hactive hlog hprescribed hstride).cost = outputCost := rfl

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InheritedTaggedQuotientPrecenterMasks
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e dQ dQF : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s dQ)
    (hQ : Q.filtration = D.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold (M ⧸ Fmark.filtration.layerIdeal (s + 1)) s dQF)
    (hQF : QF.filtration = Fmark.filtration.quotientTop)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark.filtration φ marked)

noncomputable def topQuotient :
    AllocatedExternalLocalCandidate C Q QF.filtration
      (D.topQuotientMarkedMap Fmark φ hφ) (Fmark.topQuotientOrbit QF hQF marked) where
  orbit := D.topQuotientOrbit Q hQ candidate.orbit
  mark_on_slice u hu := by
    rw [D.topQuotientOrbit_eval Q hQ, Fmark.topQuotientOrbit_eval QF hQF]
    have hsquare :
        realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
          (hM := QF.filtration.lowerCentralSeries_eq_bot)
          (D.topQuotientMarkedMap Fmark φ hφ)
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
            (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) =
        realificationMap (hnil := Fmark.filtration.lowerCentralSeries_eq_bot)
          (hM := QF.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (Fmark.filtration.layerIdeal (s + 1)))
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) := by
      apply NilpotentLieBCHGroup.ext
      exact D.topQuotientMarkedMap_real_mk Fmark φ hφ _
    rw [hsquare, candidate.mark_on_slice u hu]

@[simp] theorem topQuotient_orbit :
    (candidate.topQuotient Fmark φ hφ Q hQ QF hQF).orbit =
      D.topQuotientOrbit Q hQ candidate.orbit := rfl

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem sides_pos (k : LayerSamplerVariables G I n B) : 0 < A.sides k := by
  cases k with
  | inl g => exact S.positive
  | inr j => exact allocatedPrincipalSides_pos B U b S j

end AllocatedExternalCandidateSampler

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalRetainedResidual
namespace OAI


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

noncomputable def sliceTest : D.Niltest (fun _ : C.Variables => 1) :=
  (reference.withOrbit candidate.orbit).scalarAffinePullback
    (C.step : ℚ) (fun i => (C.slice.start i : ℚ))

@[simp] theorem sliceTest_normBound :
    (candidate.sliceTest reference).normBound = reference.normBound := rfl

@[simp] theorem sliceTest_lipBound :
    (candidate.sliceTest reference).lipBound = reference.lipBound := rfl

@[simp] theorem sliceTest_observable :
    (candidate.sliceTest reference).observable = reference.observable := rfl

@[simp] theorem sliceTest_complexity (p : ℝ) :
    (candidate.sliceTest reference).ComplexityLE p ↔ reference.ComplexityLE p := Iff.rfl

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

local instance candidateVariableDecidableEq : DecidableEq C.Variables := Subtype.instDecidableEq

end AllocatedExternalLocalCandidate

namespace AllocatedExternalLocalChart
variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

noncomputable def fixedNatural (i : LayerSamplerVariables G I n B) : ℕ :=
  if hi : C.keep i then 0 else (C.fixed ⟨i, hi⟩).toNat

theorem fixedNatural_lt (i : LayerSamplerVariables G I n B) (hi : ¬C.keep i) :
    C.fixedNatural i < A.sides i := by
  simp only [fixedNatural, dif_neg hi]
  have h := C.fixed_in_box ⟨i, hi⟩
  have he : ((C.fixed ⟨i, hi⟩).toNat : ℤ) = C.fixed ⟨i, hi⟩ :=
    Int.toNat_of_nonneg h.1
  exact_mod_cast (show ((C.fixed ⟨i, hi⟩).toNat : ℤ) < (A.sides i : ℤ) by
    rw [he]
    exact h.2)

end AllocatedExternalLocalChart

end
end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)
    {sliceBudget testBudget : ℝ}
    (hbudget : 0 ≤ sliceBudget) (hcost : outputCost ≤ sliceBudget)
    (htest : 2 ≤ testBudget)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp sliceBudget)

noncomputable def retainedResidualPacket (z : out.retained) :
    LocalMajorSliceTest (RationalTorus.trivialNilmanifold 0) A.sides sliceBudget testBudget where
  stride := out.step z
  stride_pos := out.step_pos z
  slice := (out.slice z).freezeShort (P.chart ⟨z.val, out.subset z.property⟩).keep
    (P.chart ⟨z.val, out.subset z.property⟩).fixedNatural
    (P.chart ⟨z.val, out.subset z.property⟩).fixedNatural_lt
  dense := by
    let C := P.chart ⟨z.val, out.subset z.property⟩
    have he : Classical.decEq C.Variables = Subtype.instDecidableEq :=
      Subsingleton.elim _ _
    have hd : @IsDenseCommonStrideBox C.Variables _ Subtype.instDecidableEq
        (fun i => A.sides i.val) outputCost
        (@ResidueBoxSlice.integerPoints C.Variables _ _ _ Subtype.instDecidableEq (out.slice z)) := by
      rw [← he]
      exact out.dense z
    have h : IsDenseCommonStrideBox A.sides (max outputCost (Real.log (Real.exp sliceBudget)))
        ((out.slice z).freezeShort C.keep C.fixedNatural C.fixedNatural_lt).integerPoints := by
      exact (out.slice z).freezeShort_dense C.keep C.fixedNatural C.fixedNatural_lt
        (out.step_pos z) hd (Real.one_le_exp hbudget) (fun i hi => hshort z ⟨i, hi⟩)
    simpa only [Real.log_exp, max_eq_right hcost] using h
  test := RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold 0) _ 1
  norm := by change ‖(1 : ℂ)‖ ≤ 1; exact le_of_eq norm_one
  complexity := RationalTorus.trivialNilmanifold_const_one_complexity 0 _ htest

@[simp] theorem retainedResidualPacket_weight (z : out.retained)
    (x : LayerSamplerVariables G I n B → ℤ) :
    (out.retainedResidualPacket hbudget hcost htest hshort z).weight x = 1 := by
  simp [LocalMajorSliceTest.weight, retainedResidualPacket]

noncomputable def residualPacket (z : A.Path) :
    LocalMajorSliceTest (RationalTorus.trivialNilmanifold 0) A.sides sliceBudget testBudget :=
  if hz : z ∈ out.retained then out.retainedResidualPacket hbudget hcost htest hshort ⟨z, hz⟩
  else LocalMajorSliceTest.full A.sides A.sides_pos sliceBudget testBudget hbudget
    (RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold 0) _ 1)
    (by simp [RationalFilteredNilmanifold.Niltest.const])
    (RationalTorus.trivialNilmanifold_const_one_complexity 0 _ htest)

@[simp] theorem residualPacket_weight (z : A.Path)
    (x : LayerSamplerVariables G I n B → ℤ) :
    (out.residualPacket hbudget hcost htest hshort z).weight x = 1 := by
  unfold residualPacket
  split_ifs
  · exact out.retainedResidualPacket_weight hbudget hcost htest hshort _ x
  · simp [LocalMajorSliceTest.weight, LocalMajorSliceTest.full]

@[simp] theorem residualPacket_retained (z : out.retained) :
    out.residualPacket hbudget hcost htest hshort z.val =
      out.retainedResidualPacket hbudget hcost htest hshort z := by
  simp only [residualPacket, dif_pos z.property]

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointSourceBounds
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

@[simp] theorem sides_free (g : G) : A.sides (.inl g) = S.value := rfl

@[simp] theorem sides_continuous (j : Fin m) (i : I j)
    (a : B ⟨j, .inl i⟩) (r : Fin (j.val + 1)) :
    A.sides (.inr ⟨⟨j, .inl i⟩, a, r⟩) = S.value := rfl

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComparableScalarPhysicalFamilyPatch
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

def IndexedComparableUnconditionedScalarSliceTransferStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d),
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ level density : ℝ}, 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p → Real.exp (-p) ≤ level → level ≤ 2 →
    0 < density → density⁻¹ ≤ Real.exp p →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : K → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ r * L) →
    ∀ (q : ℕ) (S : ResidueBoxSlice parameters q),
      0 < q → q ≤ ⌈2 / density⌉₊ →
      (∀ j, density * L / 2 ≤ (S.length j : ℝ)) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : K, (0 : ℤ) < S.length j),
    budget ≤ (p + F) ^ F ∧
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-target) <
          (integerBoxUniformWeights (fun _ : K => (0 : ℤ)) (fun j => (S.length j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-target)

end
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] retainedLabelDecidableEq

local instance smallReferencePrimeNeZero : ∀ p : path.primes, NeZero p.val :=
  path.primeNeZero

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllSiteLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
    {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}

namespace AllocatedExternalCandidateSampler

variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm τ ξ stride cells center)

theorem site_nonempty : Nonempty A.Site :=
  (allocatedParameterBox_nonempty B U basis S).to_subtype

noncomputable def physicalBox (hξ1 : ξ ≤ 1)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x) :
    A.Path → A.Site → integerBox N :=
  narrowPhysicalSiteMap (allocatedExternalCandidateRootBudget_nonneg B U basis S)
    A.trim_pos hξ1 N A.size_pos hmargin (fun t => t.val)
    (fun t => (allocatedParameterSite_sum_bound B U basis S t).trans_eq
      (allocatedExternalCandidateRootBudget_eq B U basis S).symm)

@[simp] theorem physicalBox_val (hξ1 : ξ ≤ 1)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x) (z : A.Path) (t : A.Site) :
    (A.physicalBox hξ1 hmargin z t).val = A.physical z t := rfl

end AllocatedExternalCandidateSampler

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

local instance instNonemptySite : Nonempty A.Site := A.site_nonempty

noncomputable def allSiteLaw (z : A.Path) : FiniteProbabilityWeights A.Site :=
  if hz : z ∈ out.retained then out.siteLaw ⟨z, hz⟩
  else FiniteProbabilityWeights.uniform A.Site

@[simp] theorem allSiteLaw_retained (z : out.retained) :
    out.allSiteLaw z.val = out.siteLaw z := by
  simp only [allSiteLaw, dif_pos z.property]

@[simp] theorem allSiteLaw_of_mem (z : A.Path) (hz : z ∈ out.retained) :
    out.allSiteLaw z = out.siteLaw ⟨z, hz⟩ := by
  exact out.allSiteLaw_retained ⟨z, hz⟩

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

structure AllocatedReturnedPatchSource (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j) (z : A.Path) where
  supported : 0 < A.law.weight z
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  read : AllocatedActualCoefficientIndex G X I E n B → ℤ
  recovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
    centerLift z.1.val z.2.val sample read
  fixed : {i // ¬keep i} → ℤ
  fixed_in_box : ∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val

namespace AllocatedReturnedPatchSource

variable {keep : LayerSamplerVariables G I n B → Prop} {centerLift : ∀ j, U j}
    {z : A.Path} (source : AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z)

noncomputable def physical (u : {i // keep i} → ℤ) : X → ℤ :=
  jointIntegerPhysicalSite (finiteSplitPoint keep u source.fixed) (z.1.val, z.2.val)

noncomputable def chart {cost : ℝ}
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    {q : ℕ} (slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q)
    (hq : 0 < q) (hlen : ∀ i, 0 < slice.length i)
    (hlength : ∀ i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ slice.length i) :
    AllocatedExternalLocalChart (E := E) A cost where
  path := z
  path_supported := source.supported
  centerLift := centerLift
  center_eq := hcenter
  sample := source.sample
  read := source.read
  recovered := source.recovered
  keep := keep
  fixed := source.fixed
  fixed_in_box := source.fixed_in_box
  step := q
  step_pos := hq
  slice := slice
  dense := ⟨_, _, _, hq, hlen, slice.progression_inside, hlength,
    slice.integerPoints_eq_commonStrideBox⟩

@[simp] theorem chart_physical {cost : ℝ}
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    {q : ℕ} (slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q)
    (hq : 0 < q) (hlen : ∀ i, 0 < slice.length i)
    (hlength : ∀ i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ slice.length i)
    (u : {i // keep i} → ℤ) :
    (source.chart hcenter slice hq hlen hlength).physical u = source.physical u := rfl

end AllocatedReturnedPatchSource

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerScalarPassage
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w x
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

def IndexedComparableScalarSharedSliceTailStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type x} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d),
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ level density : ℝ}, 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p → Real.exp (-p) ≤ level → level ≤ 2 →
    0 < density → density⁻¹ ≤ Real.exp p →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : K → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ r * L) →
    ∀ {κ : Type w} [Fintype κ] [Nonempty κ]
      (stride : κ → ℕ) (S : ∀ c, ResidueBoxSlice parameters (stride c)),
      (∀ c, 0 < stride c) → (∀ c, stride c ≤ ⌈2 / density⌉₊) →
      (∀ c j, density * L / 2 ≤ ((S c).length j : ℝ)) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ c j, (0 : ℤ) < (S c).length j),
    budget ≤ (p + F) ^ F ∧
    ∀ (c : κ) (h : (I → ℤ) → ℂ),
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-target) <
          (integerBoxUniformWeights (fun _ : K => (0 : ℤ)) (fun j => ((S c).length j : ℤ)) (hparam c)).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => ((S c).start j : ℤ) + (stride c : ℤ) * (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => ((S c).start j : ℤ) + (stride c : ℤ) * (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-target)

end
end Erdos3

end

end OAI
end


