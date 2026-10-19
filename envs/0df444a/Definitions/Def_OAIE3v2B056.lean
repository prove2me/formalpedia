-- Prove2me | Definitions.Def_OAIE3v2B056
-- name    : OAIE3v2B056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:15:06.459797+00:00
-- url     : https://prove2.me/theorems/dafa5244-1804-4f3b-9c22-54cca79bbe77
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 57 of 311
-- statement:
--   Definitions bundle 57 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B007`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B012`, `OAIE3v2B013`, `OAIE3v2B014`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B017`, `OAIE3v2B018`, `OAIE3v2B023`, `OAIE3v2B024`, `OAIE3v2B025`, `OAIE3v2B026` of this split.
--
--   Modules: `Dynamics/MarkedEvaluationHeightBudget.lean`, `Dynamics/NativeDependentSelectionBudget.lean`, `Estimates/CommonCoefficientFourAnnihilators.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/CubicPairPartitionPrecision.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/CyclicMixedReflection.lean`, `Estimates/DiagonalRowTransfer.lean`, `Estimates/FiniteAssignmentPartition.lean`, `Estimates/FourBalancedRelations.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/LinearCutoff.lean`, `Estimates/MarkedEvaluationJointBounds.lean`, `Estimates/MixedFrozenMiddleRows.lean`, `Estimates/MixedPermutationTensor.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeIteratedDifferencing.lean`, `Estimates/NativeRoundedGraphEnergy.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/PrescribedInvariantUnit.lean`, `Estimates/QuarticRootExchange.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/TailReflectionInduction.lean`, `Estimates/TensorSquarePairComparison.lean`, `Estimates/UnitVerticalCyclicDifference.lean`, `Estimates/UnitVerticalMeanRowCorrelation.lean`, `Estimates/WeightedTranslationShearExponential.lean`, `Fourier/CommonMarkedFrequencyModel.lean`, `Fourier/QuadraticFrequencyCoordinates.lean`, `Fourier/RealQuarterTorusExtension.lean`, `Lattices/FourAffineRefinement.lean`, `Lattices/NaturalScaleIntegerWindow.lean`, `Linear/RankDependentInputBudget.lean`, `Probability/RoundedModelDensityBudget.lean`, `Probability/SlicedRemainderDensityFamily.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B012
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B014
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B017
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B023
import Definitions.Def_OAIE3v2B024
import Definitions.Def_OAIE3v2B025
import Definitions.Def_OAIE3v2B026

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersMoment_one (f : H → ℂ) :
    gowersMoment 1 f = (𝔼 x, f x) * star (𝔼 x, f x) := by
  change (𝔼 h, 𝔼 x, f x * star (f (x + h))) = _
  rw [Finset.expect_comm]
  calc
    (𝔼 x, 𝔼 h, f x * star (f (x + h))) =
        𝔼 x, f x * star (𝔼 h, f h) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [← Finset.mul_expect, expect_translate (fun h ↦ star (f h)), expect_star]
    _ = _ := (Finset.expect_mul _ _ _).symm

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem expect_crossDerivative (f g : H → ℂ) :
    (𝔼 h, 𝔼 x, crossDerivative f g h x) = (𝔼 x, f x) * star (𝔼 x, g x) := by
  change (𝔼 h, 𝔼 x, f x * star (g (x + h))) = _
  rw [Finset.expect_comm]
  calc
    (𝔼 x, 𝔼 h, f x * star (g (x + h))) = 𝔼 x, f x * star (𝔼 y, g y) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [← Finset.mul_expect, expect_translate (fun y ↦ star (g y)), expect_star]
    _ = _ := (Finset.expect_mul _ _ _).symm

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem correlation_sq_eq_expect_derivative (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f u‖ ^ 2 =
      𝔼 h, (finiteCorrelation Finset.univ
        (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  calc
    _ = (gowersMoment 1 (fun x => f x * star (u x))).re := by
      rw [gowersMoment_one, mul_star_re_eq_norm_sq]
      rfl
    _ = _ := by
      rw [gowersMoment, expect_re]
      apply Finset.expect_congr rfl
      intro h _
      congr 1
      change (𝔼 x, multiplicativeDerivative (fun x => f x * star (u x)) h x) = _
      apply Finset.expect_congr rfl
      intro x _
      simp only [multiplicativeDerivative, star_mul, star_star]
      ring

theorem correlation_sq_le_expect_norm_derivative (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f u‖ ^ 2 ≤
      𝔼 h, ‖finiteCorrelation Finset.univ
        (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ := by
  rw [correlation_sq_eq_expect_derivative]
  exact Finset.expect_le_expect (fun _ _ => Complex.re_le_norm _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

noncomputable def smoothedIndicator (I B : Finset H) (x : H) : ℂ :=
  𝔼 h ∈ B, finiteIndicator I (x - h)

end Erdos3

end

section

open scoped BigOperators symmDiff

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [AddCommGroup H] in
theorem mean_finiteIndicator_difference (I J : Finset H) :
    (𝔼 x, ‖finiteIndicator I x - finiteIndicator J x‖) =
      ((I ∆ J).card : ℝ) / Fintype.card H := by
  have he (x : H) : ‖finiteIndicator I x - finiteIndicator J x‖ =
      if x ∈ I ∆ J then (1 : ℝ) else 0 := by
    by_cases hi : x ∈ I <;> by_cases hj : x ∈ J <;>
      simp [finiteIndicator, Finset.mem_symmDiff, hi, hj]
  simp only [he, Fintype.expect_eq_sum_div_card]
  simp

theorem mean_indicator_smoothing_error (I : Finset H) {B : Finset H} (hB : B.Nonempty)
    {ε : ℝ} (hshift : ∀ h ∈ B, (𝔼 x, ‖finiteIndicator I x - finiteIndicator I (x - h)‖) ≤ ε) :
    (𝔼 x, ‖finiteIndicator I x - smoothedIndicator I B x‖) ≤ ε := by
  have hpoint (x : H) : ‖finiteIndicator I x - smoothedIndicator I B x‖ ≤
      𝔼 h ∈ B, ‖finiteIndicator I x - finiteIndicator I (x - h)‖ := by
    have he : finiteIndicator I x - smoothedIndicator I B x =
        𝔼 h ∈ B, (finiteIndicator I x - finiteIndicator I (x - h)) := by
      rw [Finset.expect_sub_distrib, Finset.expect_const hB]
      rfl
    rw [he]
    exact RCLike.norm_expect_le (K := ℂ)
  calc
    _ ≤ 𝔼 x, 𝔼 h ∈ B, ‖finiteIndicator I x - finiteIndicator I (x - h)‖ :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = 𝔼 h ∈ B, 𝔼 x, ‖finiteIndicator I x - finiteIndicator I (x - h)‖ := Finset.expect_comm _ _ _
    _ ≤ 𝔼 _h ∈ B, ε := Finset.expect_le_expect hshift
    _ = ε := Finset.expect_const hB ε

end Erdos3

end

section

open scoped BigOperators symmDiff

namespace Erdos3

variable {N : ℕ}

theorem mem_cyclicInterval_shift (a t x : ZMod N) (L : ℕ) :
    x - t ∈ cyclicInterval a L ↔ x ∈ cyclicInterval (a + t) L := by
  simp only [cyclicInterval, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, he⟩
    refine ⟨k, hk, ?_⟩
    calc
      a + t + k = (a + k) + t := by ring
      _ = x := by rw [he]; ring
  · rintro ⟨k, hk, he⟩
    refine ⟨k, hk, ?_⟩
    rw [← he]
    ring

theorem cyclicInterval_sdiff_next (a : ZMod N) (L : ℕ) :
    cyclicInterval a L \ cyclicInterval (a + 1) L ⊆ {a} := by
  intro x hx
  obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hk' := Finset.mem_range.mp hk
  cases k with
  | zero => simp
  | succ k =>
    exfalso
    apply hn
    refine Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
    push_cast
    ring

theorem cyclicInterval_next_sdiff (a : ZMod N) (L : ℕ) :
    cyclicInterval (a + 1) L \ cyclicInterval a L ⊆ {a + L} := by
  intro x hx
  obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hk' := Finset.mem_range.mp hk
  by_cases hnext : k + 1 < L
  · exfalso
    apply hn
    refine Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr hnext, ?_⟩
    push_cast
    ring
  · have he : L = k + 1 := by omega
    apply Finset.mem_singleton.mpr
    rw [he]
    push_cast
    ring

theorem card_cyclicInterval_symmDiff_next (a : ZMod N) (L : ℕ) :
    (cyclicInterval a L ∆ cyclicInterval (a + 1) L).card ≤ 2 := by
  rw [Finset.symmDiff_def]
  calc
    _ ≤ (cyclicInterval a L \ cyclicInterval (a + 1) L).card +
        (cyclicInterval (a + 1) L \ cyclicInterval a L).card := Finset.card_union_le _ _
    _ ≤ ({a} : Finset (ZMod N)).card + ({a + L} : Finset (ZMod N)).card :=
      Nat.add_le_add (Finset.card_le_card (cyclicInterval_sdiff_next a L))
        (Finset.card_le_card (cyclicInterval_next_sdiff a L))
    _ = 2 := by simp

theorem cyclicInterval_unit_shift_error [NeZero N] (a : ZMod N) (L : ℕ) :
    (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - finiteIndicator (cyclicInterval a L) (x - 1)‖) ≤
      2 / (N : ℝ) := by
  have he (x : ZMod N) : finiteIndicator (cyclicInterval a L) (x - 1) =
      finiteIndicator (cyclicInterval (a + 1) L) x := by
    simp only [finiteIndicator, mem_cyclicInterval_shift]
  simp only [he]
  rw [mean_finiteIndicator_difference, ZMod.card]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_cyclicInterval_symmDiff_next a L) (Nat.cast_nonneg N)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem cyclicInterval_nonempty (a : ZMod N) {L : ℕ} (hL : 0 < L) :
    (cyclicInterval a L).Nonempty := by
  refine ⟨a, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hL, ?_⟩⟩
  simp

theorem cyclicInterval_nat_shift_error (a : ZMod N) (L h : ℕ) :
    (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - finiteIndicator (cyclicInterval a L) (x - h)‖) ≤
      2 * (h : ℝ) / N := by
  let u := finiteIndicator (cyclicInterval a L)
  induction h with
  | zero => simp
  | succ h ih =>
    have he (x : ZMod N) : x - ((h + 1 : ℕ) : ZMod N) = (x - h) - 1 := by
      push_cast
      ring
    have ht : (𝔼 x, ‖u (x - h) - u ((x - h) - 1)‖) = 𝔼 x, ‖u x - u (x - 1)‖ := by
      simpa only [sub_eq_add_neg] using
        (Fintype.expect_equiv (Equiv.addRight (-(h : ZMod N)))
          (fun x => ‖u (x + -(h : ZMod N)) - u ((x + -(h : ZMod N)) - 1)‖)
          (fun x => ‖u x - u (x - 1)‖) (fun _ => rfl))
    change (𝔼 x, ‖u x - u (x - ((h + 1 : ℕ) : ZMod N))‖) ≤ _
    calc
      _ ≤ (𝔼 x, ‖u x - u (x - h)‖) + (𝔼 x, ‖u (x - h) - u ((x - h) - 1)‖) := by
        rw [← Finset.expect_add_distrib]
        apply Finset.expect_le_expect
        intro x _
        rw [he]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (h : ℝ) / N + 2 / N := by
        rw [ht]
        exact add_le_add ih (cyclicInterval_unit_shift_error a L)
      _ = _ := by push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

noncomputable def sigmaAxisMeasure (μ : ∀ d, Measure (I d → ℝ)) : Measure ((Σ d, I d) → ℝ) :=
  Measure.map (sigmaAxisCoordinates I).symm (Measure.pi μ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

namespace PolynomialTranslationLie

noncomputable def toProdl : PolynomialTranslationLie σ ≃ₗ[ℚ] (σ → ℚ) × MvPolynomial σ ℚ :=
  { toProd with map_add' _ _ := rfl, map_smul' _ _ := rfl }

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

theorem lieTreeEval_relabel (v : J → L) (f : I → J) (a : FreeMagma I) :
    lieTreeEval v (FreeMagma.map f a) = lieTreeEval (v ∘ f) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change ⁅lieTreeEval v (FreeMagma.map f a), lieTreeEval v (FreeMagma.map f b)⁆ = _
    exact congrArg₂ (fun x y : L => ⁅x, y⁆) ha hb

theorem lieTreeWeight_relabel (w : J → ℕ) (f : I → J) (a : FreeMagma I) :
    lieTreeWeight w (FreeMagma.map f a) = lieTreeWeight (w ∘ f) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change lieTreeWeight w (FreeMagma.map f a) + lieTreeWeight w (FreeMagma.map f b) = _
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeSupport_relabel (f : I → J) (a : FreeMagma I) :
    lieTreeSupport (FreeMagma.map f a) = f '' lieTreeSupport a := by
  induction a using FreeMagma.rec with
  | of i => simp only [FreeMagma.map_of, lieTreeSupport, Set.image_singleton]
  | mul a b ha hb =>
    change lieTreeSupport (FreeMagma.map f a) ∪ lieTreeSupport (FreeMagma.map f b) = _
    rw [ha, hb, ← Set.image_union]
    rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourBalancedRelations
namespace OAI

section

namespace Erdos3

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem fourAlternatingMap_apply (v : Fin 4 → V) :
    fourAlternatingMap (R := R) v = v 0 + v 1 - v 2 - v 3 := rfl

theorem mem_fourCommonModulo (C D : Submodule R V) (v : Fin 4 → V) :
    v ∈ fourCommonModulo C D ↔ (∀ k, v k ∈ C) ∧ ∀ k, v k - v 0 ∈ D := by
  simp [fourCommonModulo, Submodule.mem_pi]

theorem mem_fourBalancedDependent (D : Submodule R V) (v : Fin 4 → V) :
    v ∈ fourBalancedDependent D ↔ (∀ k, v k ∈ D) ∧ v 0 + v 1 - v 2 - v 3 = 0 := by
  simp [fourBalancedDependent, Submodule.mem_pi, fourAlternatingMap_apply]

theorem fourBalancedDependent_le_common (C D : Submodule R V) (hDC : D ≤ C) :
    fourBalancedDependent D ≤ fourCommonModulo C D := by
  intro v hv
  obtain ⟨hv, _⟩ := (mem_fourBalancedDependent D v).mp hv
  exact (mem_fourCommonModulo C D v).mpr
    ⟨fun k => hDC (hv k), fun k => D.sub_mem (hv k) (hv 0)⟩

theorem fourRefinedRelation_le_common (C D : Submodule R V) (hDC : D ≤ C)
    (K : Submodule R (Fin 4 → V)) : fourRefinedRelation C D K ≤ fourCommonModulo C D :=
  sup_le inf_le_right (fourBalancedDependent_le_common C D hDC)

theorem mem_fourPetalSpace (D : Submodule R V) (K : Submodule R (Fin 4 → V)) (v : V) :
    v ∈ fourPetalSpace D K ↔ v ∈ D ∧ LinearMap.single R (fun _ : Fin 4 => V) 0 v ∈ K := Iff.rfl

theorem fourPetalSpace_le_first (D : Submodule R V) (K : Submodule R (Fin 4 → V)) :
    fourPetalSpace D K ≤ K.map (LinearMap.proj 0) := by
  intro v hv
  exact ⟨LinearMap.single R (fun _ : Fin 4 => V) 0 v, hv.2, by simp [LinearMap.single_apply]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

section Algebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem mem_petalComparisonSpace (C P K : Submodule R V) (x : Fin 2 → V) :
    x ∈ petalComparisonSpace C P K ↔ x 1 ∈ C ⊔ K ∧ x 0 - x 1 ∈ P ⊔ K := Iff.rfl

theorem petalComparisonSpace_decompose (C P K : Submodule R V) (x : Fin 2 → V)
    (hx : x ∈ petalComparisonSpace C P K) :
    ∃ c ∈ C, ∃ p ∈ P, ∃ k₀ ∈ K, ∃ k₁ ∈ K,
      x 0 = c + p + k₀ ∧ x 1 = c + k₁ := by
  obtain ⟨c, hc, k₁, hk₁, h₁⟩ := Submodule.mem_sup.mp hx.1
  obtain ⟨p, hp, k₀, hk₀, h₀⟩ := Submodule.mem_sup.mp hx.2
  change c + k₁ = x 1 at h₁
  change p + k₀ = x 0 - x 1 at h₀
  refine ⟨c, hc, p, hp, k₁ + k₀, K.add_mem hk₁ hk₀, k₁, hk₁, ?_, h₁.symm⟩
  calc
    x 0 = (x 0 - x 1) + x 1 := (sub_add_cancel _ _).symm
    _ = (p + k₀) + (c + k₁) := by rw [← h₀, ← h₁]
    _ = c + p + (k₁ + k₀) := by abel

theorem petalComparisonSpace_le_pi (C P K U : Submodule R V)
    (hC : C ≤ U) (hP : P ≤ U) (hK : K ≤ U) :
    petalComparisonSpace C P K ≤ Submodule.pi Set.univ (fun _ : Fin 2 => U) := by
  intro x hx
  obtain ⟨c, hc, p, hp, k₀, hk₀, k₁, hk₁, h₀, h₁⟩ := petalComparisonSpace_decompose C P K x hx
  apply Submodule.mem_pi.mpr
  intro i _
  fin_cases i
  · change x 0 ∈ U
    rw [h₀]
    exact U.add_mem (U.add_mem (hC hc) (hP hp)) (hK hk₀)
  · change x 1 ∈ U
    rw [h₁]
    exact U.add_mem (hC hc) (hK hk₁)

end Algebra

open scoped TensorProduct

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem linearCutoff_eq_one (a : ℝ) (h : ℝ≥0) (hh : 0 < h) {t : ℝ} (ht : t ≤ a) :
    linearCutoff a h t = 1 := by
  have hhR : (0 : ℝ) < h := hh
  have hfrac : (1 : ℝ) ≤ (a + (h : ℝ) - t) / h := (le_div_iff₀ hhR).mpr (by linarith)
  simp only [linearCutoff, min_eq_left hfrac, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem cubeRepresentativeSum_intCast {d N : ℕ} (k : Fin d → ZMod N) (ω : Fin d → Bool) :
    (cubeRepresentativeSum k ω : ℤ) = cubeShift (fun i => ((k i).val : ℤ)) ω := by
  simp [cubeRepresentativeSum, cubeShift]

theorem cubeRepresentativeSum_zmodCast {d N : ℕ} [NeZero N] (k : Fin d → ZMod N) (ω : Fin d → Bool) :
    (cubeRepresentativeSum k ω : ZMod N) = cubeShift k ω := by
  simp [cubeRepresentativeSum, cubeShift]

theorem exists_cube_carry_code {d N : ℕ} [NeZero N]
    (k : Fin d → ZMod N) {a : ℕ} (ha : a < N) :
    ∃ b : (Fin d → Bool) → Fin (d + 1), ∀ ω,
      cyclicTranslationOffset (cubeShift k ω) a =
        cubeShift (fun i => ((k i).val : ℤ)) ω + cubeCarryShift d N b ω := by
  let b (ω : Fin d → Bool) : Fin (d + 1) :=
    ⟨(a + cubeRepresentativeSum k ω) / N, (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr (by
      have hs := cubeRepresentativeSum_le k ω
      nlinarith)⟩
  refine ⟨b, ?_⟩
  intro ω
  have ha' : (a : ZMod N).val = a := by simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
  have hadd := cyclic_representative_add (cubeShift k ω) (a : ZMod N)
  rw [ha'] at hadd
  have hcast : ((a + cubeRepresentativeSum k ω : ℕ) : ZMod N) = cubeShift k ω + (a : ZMod N) := by
    rw [Nat.cast_add, cubeRepresentativeSum_zmodCast, add_comm]
  have hval := congrArg (fun x : ZMod N => (x.val : ℤ)) hcast
  rw [ZMod.val_natCast] at hval
  have hdiv := Nat.mod_add_div (a + cubeRepresentativeSum k ω) N
  have hdiv' := congrArg (fun x : ℕ => (x : ℤ)) hdiv
  simp only [Nat.cast_add, Nat.cast_mul] at hdiv'
  rw [hval, hadd] at hdiv'
  rw [← cubeRepresentativeSum_intCast]
  change (cubeShift k ω).val - (if N - (cubeShift k ω).val ≤ a then (N : ℤ) else 0) =
    (cubeRepresentativeSum k ω : ℤ) + -(((a + cubeRepresentativeSum k ω) / N : ℕ) : ℤ) * N
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FourAffineRefinement
namespace OAI

section

namespace Erdos3

variable {R I E : Type*} {V : I → Type*} [CommRing R]
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [AddCommGroup E] [Module R E]

theorem four_affine_balanced_invariant (f : (∀ i, V i) → E) (C D : ∀ i, Submodule R (V i))
    (haffine : ∀ x : ∀ i, V i, (∀ i, x i ∈ C i) →
      ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
        f (fun i => x i + (y i : V i)) = f x + A y)
    (v z : ∀ i, Fin 4 → V i) (hv : ∀ i, v i ∈ fourCommonModulo (C i) (D i))
    (hz : ∀ i, z i ∈ fourBalancedDependent (D i)) :
    fourFunctionDifference f (fun i k => v i k + z i k) = fourFunctionDifference f v := by
  let x : ∀ i, V i := fun i => v i 0
  obtain ⟨A, hA⟩ := haffine x (fun i => ((mem_fourCommonModulo (C i) (D i) (v i)).mp (hv i)).1 0)
  let y (k : Fin 4) : ∀ i, D i := fun i =>
    ⟨v i k - v i 0, ((mem_fourCommonModulo (C i) (D i) (v i)).mp (hv i)).2 k⟩
  let t (k : Fin 4) : ∀ i, D i := fun i =>
    ⟨z i k, ((mem_fourBalancedDependent (D i) (z i)).mp (hz i)).1 k⟩
  have hbase (k : Fin 4) : f (fun i => v i k) = f x + A (y k) := by
    have heq : (fun i => x i + ((y k) i : V i)) = fun i => v i k := by
      funext i
      dsimp only [x, y]
      abel
    simpa only [heq] using hA (y k)
  have hnew (k : Fin 4) : f (fun i => v i k + z i k) = f x + (A (y k) + A (t k)) := by
    have heq : (fun i => x i + ((y k + t k) i : V i)) = fun i => v i k + z i k := by
      funext i
      change v i 0 + (v i k - v i 0 + z i k) = _
      abel
    simpa only [heq, map_add] using hA (y k + t k)
  have ht : t 0 + t 1 - t 2 - t 3 = 0 := by
    funext i
    apply Subtype.ext
    change z i 0 + z i 1 - z i 2 - z i 3 = 0
    exact ((mem_fourBalancedDependent (D i) (z i)).mp (hz i)).2
  have hAt : A (t 0) + A (t 1) - A (t 2) - A (t 3) = 0 := by
    rw [← map_add, ← map_sub, ← map_sub, ht, map_zero]
  calc
    _ = fourFunctionDifference f v + (A (t 0) + A (t 1) - A (t 2) - A (t 3)) := by
      unfold fourFunctionDifference
      rw [hnew 0, hnew 1, hnew 2, hnew 3, hbase 0, hbase 1, hbase 2, hbase 3]
      abel
    _ = _ := by rw [hAt, add_zero]

theorem four_refined_affine_identity (f : (∀ i, V i) → E) (C D : ∀ i, Submodule R (V i))
    (haffine : ∀ x : ∀ i, V i, (∀ i, x i ∈ C i) →
      ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
        f (fun i => x i + (y i : V i)) = f x + A y)
    (K : ∀ i, Submodule R (Fin 4 → V i))
    (hK : ∀ v : ∀ i, Fin 4 → V i, (∀ i, v i ∈ K i) → fourFunctionDifference f v = 0)
    (v : ∀ i, Fin 4 → V i) (hv : ∀ i, v i ∈ fourRefinedRelation (C i) (D i) (K i)) :
    fourFunctionDifference f v = 0 := by
  classical
  have hdecomp (i : I) : ∃ u ∈ K i ⊓ fourCommonModulo (C i) (D i),
      ∃ z ∈ fourBalancedDependent (D i), u + z = v i := Submodule.mem_sup.mp (hv i)
  choose u hu z hz heq using hdecomp
  have hvEq : (fun i k => u i k + z i k) = v := by
    funext i k
    exact congrFun (heq i) k
  rw [← hvEq, four_affine_balanced_invariant f C D haffine u z (fun i => (hu i).2) hz]
  exact hK u (fun i => (hu i).1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NaturalScaleIntegerWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]

theorem card_doubled_centeredIntegerBox_le (R : ι → ℕ) :
    (centeredIntegerBox (fun i => 2 * R i)).card ≤
      2 ^ Fintype.card ι * (centeredIntegerBox R).card := by
  rw [card_centeredIntegerBox, card_centeredIntegerBox]
  calc
    (∏ i, (2 * (2 * R i) + 1)) ≤ ∏ i, (2 * (2 * R i + 1)) := by
      gcongr with i
      omega
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
namespace OAI

section

namespace Erdos3

theorem affineCyclicTorusCarry_identity {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) (i : Fin r) :
    (-(h₀.val : ℝ) * t i - c i) +
      ((-(affineCyclicTorusCarry t c h₀ h i) : ℤ) : ℚ) + (h.val : ℝ) * t i =
        affineCyclicTorusLocalLift t c h₀ h i := by
  rw [affineCyclicTorusLocalLift_eq_sub_carry]
  push_cast
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedInvariantUnit
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_complex_unit_completion {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (f : X → ℂ) (v : Fin n → X → ℂ) {K J : ℝ≥0}
    (hf : ∀ x, ‖f x‖ ≤ 1 / 2) (hfLip : LipschitzWith K f)
    (hv : ∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) (hvnorm : ∀ i x, ‖v i x‖ ≤ 1)
    (hvLip : ∀ i, LipschitzWith J (v i)) :
    ∃ u : Fin (n + 1) → X → ℂ,
      (∀ x, u 0 x = f x) ∧
      (∀ x, ∑ i, ‖u i x‖ ^ 2 = 1) ∧
      (∀ i x, ‖u i x‖ ≤ 1) ∧
      (∀ i, LipschitzWith (K + J) (u i)) ∧
      ∀ x y c, ‖c‖ = 1 → f x = c * f y → (∀ i, v i x = c * v i y) →
        ∀ i, u i x = c * u i y := by
  let t (x : X) : ℂ := Real.sqrt (1 - ‖f x‖ ^ 2)
  have ht (x : X) : ‖t x‖ = Real.sqrt (1 - ‖f x‖ ^ 2) := by
    exact (Complex.norm_real _).trans (Real.norm_of_nonneg (Real.sqrt_nonneg _))
  have htbound (x : X) : ‖t x‖ ≤ 1 := by
    rw [ht]
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ‖f x‖])
  have htsq (x : X) : ‖t x‖ ^ 2 = 1 - ‖f x‖ ^ 2 := by
    rw [ht]
    exact Real.sq_sqrt (by nlinarith [hf x, norm_nonneg (f x)])
  have htLip : LipschitzWith K t := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    change ‖(Real.sqrt (1 - ‖f x‖ ^ 2) : ℂ) - (Real.sqrt (1 - ‖f y‖ ^ 2) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (sqrt_complement_lipschitz (norm_nonneg _) (norm_nonneg _) (hf x) (hf y)).trans
      ((abs_norm_sub_norm_le (f x) (f y)).trans (by
        simpa only [dist_eq_norm] using hfLip.dist_le_mul x y))
  let u : Fin (n + 1) → X → ℂ := Fin.cases f (fun i x => t x * v i x)
  have htailLip (i : Fin n) : LipschitzWith (K + J) (fun x => t x * v i x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    calc
      _ = ‖(t x - t y) * v i x + t y * (v i x - v i y)‖ := by congr 1; ring
      _ ≤ ‖(t x - t y) * v i x‖ + ‖t y * (v i x - v i y)‖ := norm_add_le _ _
      _ ≤ ‖t x - t y‖ + ‖v i x - v i y‖ := by
        simp only [norm_mul]
        exact add_le_add
          (mul_le_of_le_one_right (norm_nonneg _) (hvnorm i x))
          (mul_le_of_le_one_left (norm_nonneg _) (htbound y))
      _ ≤ (K : ℝ) * dist x y + (J : ℝ) * dist x y := add_le_add
        (by simpa only [dist_eq_norm] using htLip.dist_le_mul x y)
        (by simpa only [dist_eq_norm] using (hvLip i).dist_le_mul x y)
      _ = _ := by push_cast; ring
  refine ⟨u, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [Fin.sum_univ_succ, u, Fin.cases_zero, Fin.cases_succ, norm_mul, mul_pow]
    rw [← Finset.mul_sum, hv, mul_one, htsq]
    ring
  · intro i x
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hf x).trans (by norm_num)
    · change ‖t x * v j x‖ ≤ 1
      rw [norm_mul]
      exact (mul_le_mul (htbound x) (hvnorm j x) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  · intro i
    refine Fin.cases ?_ htailLip i
    exact hfLip.weaken (le_add_of_nonneg_right (show 0 ≤ J by positivity))
  · intro x y c hc hfc hvc i
    have htx : t x = t y := by
      dsimp [t]
      rw [hfc, norm_mul, hc, one_mul]
    refine Fin.cases hfc (fun j => ?_) i
    change t x * v j x = c * (t y * v j y)
    rw [htx, hvc]
    ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_correlation_partition_bound {X I : Type*} [Fintype X] [Fintype I]
    (f u : X → ℂ) (v : I → X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖𝔼 x, f x * star (u x)‖ ≤
      (∑ i, ‖𝔼 x, f x * star (v i x)‖) + 𝔼 x, ‖u x - ∑ i, v i x‖ := by
  have he := norm_correlation_sub_le_mean f u (fun x => ∑ i, v i x) hf
  have ht := norm_le_norm_add_norm_sub
    (𝔼 x, f x * star (∑ i, v i x)) (𝔼 x, f x * star (u x))
  have hm : (𝔼 x, f x * star (∑ i, v i x)) = ∑ i, 𝔼 x, f x * star (v i x) := by
    simp only [star_sum, Finset.mul_sum, Finset.expect_sum_comm]
  rw [norm_sub_rev] at ht
  have hsum := norm_sum_le (s := Finset.univ) (f := fun i => 𝔼 x, f x * star (v i x))
  rw [hm] at ht he
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem expect_cyclicHalf_le {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : ZMod N, f (cyclicHalf x)) ≤ 2 * (𝔼 x : ZMod N, f x) := by
  classical
  have hs : (∑ x : ZMod N, f (cyclicHalf x)) ≤ ∑ z : ZMod N × ZMod 2, f z.1 := by
    apply Finset.sum_le_sum_of_injOn (fun x : ZMod N => (cyclicHalf x, (x.val : ZMod 2)))
      cyclicHalf_with_parity_injective.injOn
    · exact Finset.subset_univ _
    · intro x _
      exact le_rfl
    · intro a _ _
      exact hf a.1
  have ht : (∑ z : ZMod N × ZMod 2, f z.1) = 2 * ∑ x : ZMod N, f x := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
  rw [ht] at hs
  simp only [Fintype.expect_eq_sum_div_card, ZMod.card]
  calc
    _ ≤ (2 * ∑ x : ZMod N, f x) / N := div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorSquarePairComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_unit_pair_replacement_error {I J : Type*} [Fintype I] [Fintype J]
    (u : I → ℂ) (v : J → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hv : ∑ j, ‖v j‖ ^ 2 = 1)
    (huc : ∀ i, ‖u i‖ ≤ 1) (hvc : ∀ j, ‖v j‖ ≤ 1)
    (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (G : I → J → ℂ) :
    ‖star a * b - ∑ ij : I × J,
      (star (a * star (u ij.1)) * (b * star (v ij.2))) * G ij.1 ij.2‖ ≤
      ∑ ij : I × J, ‖star (u ij.1) * v ij.2 - G ij.1 ij.2‖ := by
  have hleft := congrArg star (complex_unit_vector_resolution u hu a)
  simp only [star_sum, star_mul] at hleft
  have hright := complex_unit_vector_resolution v hv b
  have hrepr : star a * b = ∑ ij : I × J,
      (star (a * star (u ij.1)) * (b * star (v ij.2))) * (star (u ij.1) * v ij.2) := by
    conv_lhs => rw [hleft, hright]
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [star_mul]
    ring
  rw [hrepr, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij _
  rw [← mul_sub, norm_mul]
  have hcap : ‖star (a * star (u ij.1)) * (b * star (v ij.2))‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
    · rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (huc _)
    · rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hvc _)
  exact mul_le_of_le_one_left (norm_nonneg _) hcap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankDependentInputBudget
namespace OAI

section

namespace Erdos3

theorem rankDependentInputBudget_bounds {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ rankDependentInputBudget z ∧ z ≤ rankDependentInputBudget z ∧
      2 * z ≤ rankDependentInputBudget z ∧
      2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) ≤ rankDependentInputBudget z ∧
      2 * (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) ≤
        Real.exp (rankDependentInputBudget z) := by
  let D := 2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36))
  let L := (z + 2) ^ 3 + (z + 2) ^ 18 + z
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hzL : z ≤ L := by
    dsimp only [L]
    have h₁ : 0 ≤ (z + 2) ^ 3 := by positivity
    have h₂ : 0 ≤ (z + 2) ^ 18 := by positivity
    linarith
  have hL : 0 ≤ L := hz.trans hzL
  have hbudget : rankDependentInputBudget z = 2 * z + D + L + 2 := rfl
  have hLbudget : L + 2 ≤ rankDependentInputBudget z := by rw [hbudget]; linarith
  refine ⟨by rw [hbudget]; linarith, by rw [hbudget]; linarith,
    by rw [hbudget]; linarith, ?_, ?_⟩
  · change D ≤ _
    rw [hbudget]
    linarith
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hsum : Real.exp z + Real.exp L ≤ Real.exp (L + 1) := by
      calc
        Real.exp z + Real.exp L ≤ 2 * Real.exp L := by
          linarith [Real.exp_le_exp.mpr hzL]
        _ ≤ Real.exp 1 * Real.exp L := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
        _ = Real.exp (L + 1) := (mul_comm _ _).trans (Real.exp_add L 1).symm
    calc
      2 * (Real.exp z + Real.exp L) ≤ 2 * Real.exp (L + 1) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ Real.exp 1 * Real.exp (L + 1) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (L + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (rankDependentInputBudget z) := Real.exp_le_exp.mpr hLbudget

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeDependentSelectionBudget
namespace OAI

section

namespace Erdos3

theorem exists_native_dependent_selection_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let P₀ := (p + a) ^ a
      let P := (P₀ + 2) ^ 3 + 2 * P₀
      P₀ ≤ (p + C) ^ C ∧ 2 * P ≤ (p + C) ^ C ∧ (P + c) ^ c ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + Polynomial.C a) ^ a
  let P := (P₀ + 2) ^ 3 + 2 * P₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P₀ + 2 * P + (P + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p hp P₀' P'
  have hP₀ : 0 ≤ P₀' := by dsimp only [P₀']; positivity
  have hP : 0 ≤ P' := by dsimp only [P']; positivity
  have hpow : 0 ≤ (P' + c) ^ c := by positivity
  have hsum : P₀' + 2 * P' + (P' + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, P₀, P, P₀', P', Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hP, hpow, hsum],
    by linarith only [hP₀, hpow, hsum], by linarith only [hP₀, hP, hsum]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedEvaluationJointBounds
namespace OAI

section

namespace Erdos3

open Module

def markedQuotientHeight (s n a d m q H : ℕ) : ℕ :=
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  let Q := rationalKernelHeight m B
  let J := max 1 (max C Q)
  max (rationalLieStructureHeight d (max J (rationalSolveHeight q J)))
    ((d + 1) * (B * Q) ^ d)

end Erdos3

end

section

namespace Erdos3

open Module

def markedEvaluationHeight (s n a d m q H K : ℕ) : ℕ :=
  let T := lieTreeHeight n H s
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let Q := rationalKernelHeight m B
  max (markedQuotientHeight s n a d m q H)
    ((d + 1) * (rationalSolveHeight q Q * max T ((n + 1) * (T * K) ^ n)) ^ d)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MarkedEvaluationHeightBudget
namespace OAI

section

namespace Erdos3

theorem markedShiftInputBudget_le_height (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    markedShiftInputBudget s p ≤ markedShiftHeightBudget s p :=
  le_power_budget (markedShiftInputBudget_nonneg s hp) (by omega)

theorem markedShiftHeightBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ markedShiftHeightBudget s p :=
  (markedShiftInputBudget_nonneg s hp).trans (markedShiftInputBudget_le_height s hp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

open Module

variable {R V ι κ : Type*} [Field R] [AddCommGroup V] [Module R V]

theorem fourCommonModulo_eq_sup (C D : Submodule R V) (hDC : D ≤ C) :
    fourCommonModulo C D = C.map (fourDiagonalMap (R := R)) ⊔
      Submodule.pi Set.univ (fun _ : Fin 4 => D) := by
  ext v
  constructor
  · intro hv
    obtain ⟨hc, hd⟩ := (mem_fourCommonModulo C D v).mp hv
    apply Submodule.mem_sup.mpr
    exact ⟨fourDiagonalMap (R := R) (v 0), ⟨v 0, hc 0, rfl⟩,
      v - fourDiagonalMap (R := R) (v 0), Submodule.mem_pi.mpr (fun k _ => hd k),
      by abel⟩
  · intro hv
    obtain ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    apply (mem_fourCommonModulo C D _).mpr
    refine ⟨fun k => C.add_mem hx (hDC ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))), ?_⟩
    intro k
    change (x + y k) - (x + y 0) ∈ D
    have he : (x + y k) - (x + y 0) = y k - y 0 := by abel
    rw [he]
    exact D.sub_mem ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))
      ((Submodule.mem_pi.mp hy) 0 (Set.mem_univ 0))

end Erdos3

end

section

namespace Erdos3

open Module

variable {R V κ : Type*} [Field R] [AddCommGroup V] [Module R V]

def fourBalanceProjection : (Fin 4 → V) →ₗ[R] (Fin 4 → V) :=
  LinearMap.id + (LinearMap.single R (fun _ : Fin 4 => V) 3).comp (fourAlternatingMap (R := R))

theorem fourBalanceProjection_apply (v : Fin 4 → V) :
    fourBalanceProjection (R := R) v = ![v 0, v 1, v 2, v 0 + v 1 - v 2] := by
  ext k
  fin_cases k <;>
    simp [fourBalanceProjection, fourAlternatingMap_apply]

theorem fourBalanceProjection_image (D : Submodule R V) :
    (Submodule.pi Set.univ (fun _ : Fin 4 => D)).map (fourBalanceProjection (R := R)) =
      fourBalancedDependent D := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have h (k : Fin 4) : v k ∈ D := (Submodule.mem_pi.mp hv) k (Set.mem_univ k)
    apply (mem_fourBalancedDependent D _).mpr
    constructor
    · intro k
      rw [fourBalanceProjection_apply]
      fin_cases k
      · exact h 0
      · exact h 1
      · exact h 2
      · exact D.sub_mem (D.add_mem (h 0) (h 1)) (h 2)
    · rw [fourBalanceProjection_apply]
      dsimp
      abel
  · intro hz
    obtain ⟨hmem, hzero⟩ := (mem_fourBalancedDependent D z).mp hz
    refine ⟨z, Submodule.mem_pi.mpr (fun k _ => hmem k), ?_⟩
    change z + LinearMap.single R (fun _ : Fin 4 => V) 3 (fourAlternatingMap (R := R) z) = z
    rw [fourAlternatingMap_apply, hzero, map_zero, add_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_unit_vector_exchange_error {I : Type*} [Fintype I]
    (v : I → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1) (hcap : ∀ i, ‖v i‖ ≤ 1)
    (a : ℂ) (g : I → ℂ) :
    ‖a - ∑ i, v i * star (g i)‖ ≤ ∑ i, ‖star a * v i - g i‖ := by
  have hsum : (∑ i, v i * star (star a * v i)) = a := by
    calc
      _ = ∑ i, (a * star (v i)) * v i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [star_mul, star_star]
        ring
      _ = a := (complex_unit_vector_resolution v hv a).symm
  have heq : a - ∑ i, v i * star (g i) = ∑ i, v i * star (star a * v i - g i) := by
    simp only [star_sub, mul_sub, Finset.sum_sub_distrib, hsum]
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (hcap i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem cyclicSecondDifference_branches {N : ℕ} [NeZero N]
    (u v : (Fin 2 → ℤ) → ℂ) (k : ZMod N) (h : ℤ) (n : ZMod N) :
    cyclicSecondDifference u v k h n =
      (1 - (cyclicCarry k n : ℂ)) * integerSecondDifference u v k.val ![h, (n.val : ℤ)] +
        (cyclicCarry k n : ℂ) * integerSecondDifference u v ((k.val : ℤ) - N) ![h, (n.val : ℤ)] := by
  have hval : ((n + k).val : ℤ) = (n.val : ℤ) + k.val -
      if N - k.val ≤ n.val then (N : ℤ) else 0 := by
    simpa only [add_comm n k] using cyclic_representative_add k n
  have hk := k.val_lt
  by_cases hw : N ≤ k.val + n.val
  · have hcut : N - k.val ≤ n.val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      cyclicSecondDifference, integerSecondDifference, Matrix.cons_val_zero, Matrix.cons_val_one,
      hval, if_pos hcut]
    rw [add_sub_assoc]
  · have hcut : ¬N - k.val ≤ n.val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      cyclicSecondDifference, integerSecondDifference, Matrix.cons_val_zero, Matrix.cons_val_one,
      hval, if_neg hcut]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeIteratedDifferencing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mean_row_correlation_sq_le_derivative_correlation {H G : Type*}
    [Fintype H] [Nonempty H] [AddCommGroup G] [Fintype G]
    (f g : H → G → ℂ) :
    (𝔼 h, ‖𝔼 n, f h n * star (g h n)‖) ^ 2 ≤
      𝔼 k, 𝔼 h, ‖𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)‖ := by
  let F (h : H) (n : G) := f h n * star (g h n)
  have hid (h : H) :
      (𝔼 k, 𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)).re =
          ‖𝔼 n, f h n * star (g h n)‖ ^ 2 := by
    have heq (k n : G) : crossDerivative (F h) (F h) k n =
        multiplicativeDerivative (f h) k n * star (multiplicativeDerivative (g h) k n) := by
      simp only [crossDerivative, multiplicativeDerivative, F, star_mul, star_star]
      ring
    have hh := congrArg Complex.re (expect_crossDerivative (F h) (F h))
    simpa only [heq, mul_star_re_eq_norm_sq, F] using hh
  have hrow (h : H) : ‖𝔼 n, f h n * star (g h n)‖ ^ 2 ≤
      𝔼 k, ‖𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)‖ := by
    rw [← hid h, expect_re]
    exact Finset.expect_le_expect (fun k _ => Complex.re_le_norm _)
  calc
    _ ≤ 𝔼 h, ‖𝔼 n, f h n * star (g h n)‖ ^ 2 := expect_square_le _
    _ ≤ 𝔼 h, 𝔼 k, ‖𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)‖ :=
      Finset.expect_le_expect (fun h _ => hrow h)
    _ = _ := Finset.expect_comm _ _ _

theorem mean_row_correlation_sq_le_approximated_derivatives {H G : Type*}
    [Fintype H] [Nonempty H] [AddCommGroup G] [Fintype G]
    (f g : H → G → ℂ) (K : G → H → G → ℂ) (hf : ∀ h n, ‖f h n‖ ≤ 1)
    {ε : ℝ} (herr : ∀ k h, (𝔼 n, ‖multiplicativeDerivative (g h) k n - K k h n‖) ≤ ε) :
    (𝔼 h, ‖𝔼 n, f h n * star (g h n)‖) ^ 2 ≤
      (𝔼 k, 𝔼 h, ‖𝔼 n, multiplicativeDerivative (f h) k n * star (K k h n)‖) + ε := by
  have hrow (k : G) (h : H) :
      ‖𝔼 n, multiplicativeDerivative (f h) k n * star (multiplicativeDerivative (g h) k n)‖ ≤
        ‖𝔼 n, multiplicativeDerivative (f h) k n * star (K k h n)‖ + ε := by
    have hfn (n : G) : ‖multiplicativeDerivative (f h) k n‖ ≤ 1 := by
      rw [multiplicativeDerivative, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf h n)).trans (hf h (n + k))
    have he := (norm_correlation_sub_le_mean (multiplicativeDerivative (f h) k)
      (multiplicativeDerivative (g h) k) (K k h) hfn).trans (herr k h)
    have ht := norm_le_norm_add_norm_sub
      (𝔼 n, multiplicativeDerivative (f h) k n * star (K k h n))
      (𝔼 n, multiplicativeDerivative (f h) k n * star (multiplicativeDerivative (g h) k n))
    rw [norm_sub_rev] at ht
    linarith
  apply (mean_row_correlation_sq_le_derivative_correlation f g).trans
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun k _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun h _ => hrow k h))
  simpa only [Finset.expect_add_distrib, Fintype.expect_const] using hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRoundedGraphEnergy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_variable_unrounded_affine {I : Type*} {M : I → ℕ} {r : ℕ}
    [∀ i, NeZero (M i)] (l : I → ℕ) (hl : ∀ i, 0 < l i)
    (b : ∀ i, ZMod (M i)) (Φ : (Fin r → ℤ) →+ (∀ i, ZMod (M i)))
    (x : Fin r → ℤ) (a : I → ℝ) (h : variableRoundedCoefficient M l a = b + Φ x) :
    ∃ q ∈ coordinateDenominatorGrid l, ∀ i,
      |a i - (variableCoefficientLift l b +
        ∑ j, (x j : ℝ) • variableCoefficientLift l (Φ (Pi.single j 1))) i - q i| ≤
          1 / ((M i : ℝ) * l i) := by
  let u : I → ℤ := fun i => ((b i).val : ℤ) + ∑ j, x j * ((Φ (Pi.single j 1) i).val : ℤ)
  have hu : variableRoundedCoefficient M l a = fun i => (u i : ZMod (M i)) := by
    rw [h, map_integer_coordinates Φ x]
    funext i
    simp only [u, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  have heq : (fun i => (u i : ℝ) / ((M i : ℝ) * l i)) = variableCoefficientLift l b +
      ∑ j, (x j : ℝ) • variableCoefficientLift l (Φ (Pi.single j 1)) := by
    funext i
    simp only [u, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      variableCoefficientLift, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      add_div, Finset.sum_div, mul_div_assoc]
  have hi (i : I) := exists_unrounded_scalar (M i) (l i) (hl i) (a i) (u i) (congrFun hu i)
  choose k hk0 hk1 using hi
  let q : I → ℝ := fun i => (k i : ℝ) / l i
  refine ⟨q, ⟨k, ?_⟩, ?_⟩
  · intro i
    have hlR : (0 : ℝ) < l i := by exact_mod_cast hl i
    dsimp [q]
    field_simp
  · intro i
    rw [← heq]
    change |a i - (u i : ℝ) / ((M i : ℝ) * l i) - (k i : ℝ) / l i| ≤ _
    rw [abs_of_nonneg (hk0 i)]
    exact (hk1 i).le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RoundedModelDensityBudget
namespace OAI

section

namespace Erdos3

theorem exp_neg_roundedModelLogBudget_le_density (P : ℝ) (d : ℕ) :
    Real.exp (-roundedModelLogBudget P d) ≤
      (32 * ((2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1)) ^ 16)⁻¹ := by
  let C := (2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : 32 * C ^ 16 ≤ Real.exp (roundedModelLogBudget P d) := by
    calc
      32 * C ^ 16 ≤ Real.exp 32 * (Real.exp (44 + 6 * max P 0 + 94 * d)) ^ 16 := by
        gcongr
        · linarith [Real.add_one_le_exp (32 : ℝ)]
        · exact roundedModelScale_le_exp P d
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        unfold roundedModelLogBudget
        norm_num
        ring
  rw [Real.exp_neg]
  exact inv_le_inv₀ (Real.exp_pos _) (by positivity) |>.mpr hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem finiteFourierCoeff_convolution (f g : G → ℂ) (χ : AddChar G ℂ) :
    finiteFourierCoeff (finiteConvolution f g) χ = finiteFourierCoeff f χ * finiteFourierCoeff g χ := by
  calc
    _ = 𝔼 x, f x * finiteFourierCoeff (fun y => g (y - x)) χ := by
      simp only [finiteFourierCoeff, finiteConvolution, Finset.expect_mul, Finset.mul_expect]
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      ring
    _ = 𝔼 x, f x * (star (χ x) * finiteFourierCoeff g χ) := by
      simp_rw [finiteFourierCoeff_translate]
    _ = _ := by
      change (𝔼 x, f x * (star (χ x) * finiteFourierCoeff g χ)) =
        (𝔼 x, f x * star (χ x)) * finiteFourierCoeff g χ
      rw [Finset.expect_mul]
      apply Finset.expect_congr rfl
      intro x _
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonMarkedFrequencyModel
namespace OAI

section

namespace Erdos3

theorem integral_frequency_grid_allowance_le_exp (K d H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((K * H ^ (d ^ 3) * (l * H ^ d) : ℕ) : ℝ) ≤
      Real.exp (((p + 2) ^ 2 + (K + 5 : ℕ)) ^ (K + 5)) := by
  have hpQ : p ≤ (p + 2) ^ 2 := le_power_budget hp (by decide)
  have hlQ : ((l * H ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    calc
      _ ≤ Real.exp p * Real.exp p ^ d :=
        mul_le_mul hl (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _) (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (p + (d : ℝ) * p) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hp, hd, sq_nonneg p])
  exact integral_grid_allowance_le_exp K d H (l * H ^ d) (hp.trans hpQ) (hd.trans hpQ)
    (hH.trans (Real.exp_le_exp.mpr hpQ)) hlQ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TailReflectionInduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

structure TailReflectionData (n : ℕ) (T G : Type*) where
  kernel : T → G → G → (Fin n → G) → ℂ
  signal : T → G → ℂ
  leftWeight : T → G → (Fin n → G) → ℂ
  rightWeight : T → G → (Fin n → G) → ℂ
  tailWeight : T → Fin n → G → G → (Fin n → G) → ℂ
  signal_norm : ∀ t x, ‖signal t x‖ ≤ 1
  left_norm : ∀ t x v, ‖leftWeight t x v‖ ≤ 1
  right_norm : ∀ t x v, ‖rightWeight t x v‖ ≤ 1
  tail_norm : ∀ t i h m v, ‖tailWeight t i h m v‖ ≤ 1
  tail_misses : ∀ t i h m, MissesBoxCoordinate (tailWeight t i h m) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicMixedReflection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def tripleCarryInterval (N : ℕ) (k : Fin 3) : Finset (ZMod (3 * N)) :=
  cyclicInterval (tripleCarryStart N k : ZMod (3 * N)) N

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteAssignmentPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def assignmentSplitMap (s : ℕ) : Equiv.Perm (Fin s) ⊕ MissingAssignment s → (Fin s → Fin s)
  | Sum.inl e => e
  | Sum.inr v => v.val

theorem assignmentSplitMap_bijective (s : ℕ) : Function.Bijective (assignmentSplitMap s) := by
  classical
  constructor
  · intro a b h
    rcases a with a | a <;> rcases b with b | b
    · apply congrArg Sum.inl
      exact Equiv.ext (congrFun h)
    · exfalso
      apply b.property
      change (a : Fin s → Fin s) = b.val at h
      exact h ▸ a.surjective
    · exfalso
      apply a.property
      change a.val = (b : Fin s → Fin s) at h
      exact h.symm ▸ b.surjective
    · apply congrArg Sum.inr
      exact Subtype.ext h
  · intro v
    by_cases hv : Function.Surjective v
    · exact ⟨Sum.inl (Equiv.ofBijective v (Finite.surjective_iff_bijective.mp hv)), rfl⟩
    · exact ⟨Sum.inr ⟨v, hv⟩, rfl⟩

noncomputable def assignmentSplitEquiv (s : ℕ) :
    Equiv.Perm (Fin s) ⊕ MissingAssignment s ≃ (Fin s → Fin s) :=
  Equiv.ofBijective (assignmentSplitMap s) (assignmentSplitMap_bijective s)

theorem missingAssignment_coordinate {s : ℕ} (v : MissingAssignment s) :
    ∃ j : Fin s, ∀ i : Fin s, v.val i ≠ j := by
  classical
  have h := v.property
  simpa only [Function.Surjective, not_forall, not_exists] using h

theorem assignment_product_split {s : ℕ} {I M : Type*} [CommMonoid M]
    (F : (Fin s → Fin s) → I → M)
    (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → I) :
    (∏ v : Fin s → Fin s, F v (a ((assignmentSplitEquiv s).symm v))) =
      (∏ e : Equiv.Perm (Fin s), F e (a (Sum.inl e))) *
        ∏ v : MissingAssignment s, F v.val (a (Sum.inr v)) := by
  classical
  calc
    _ = ∏ r : Equiv.Perm (Fin s) ⊕ MissingAssignment s,
        F (assignmentSplitEquiv s r) (a r) := by
      have h := (assignmentSplitEquiv s).prod_comp
        (fun v => F v (a ((assignmentSplitEquiv s).symm v)))
      simpa only [Equiv.symm_apply_apply] using h.symm
    _ = _ := by rw [Fintype.prod_sum_type]; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPermutationTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedPermutationTensorIndex {s : ℕ} (d : ℕ)
    (a : Equiv.Perm (Fin s) → Fin d) : Fin (d ^ s.factorial) :=
  tensorIndexEquiv d s.factorial (fun j => a ((mixedPermutationIndex s).symm j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuarticRootExchange
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem complexCrossContraction_unit {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ l, ‖v l‖ ^ 2 = 1) :
    complexCrossContraction a b u v (fun k l => u k * star (v l)) = a * star b := by
  rw [complexCrossContraction_rank_one]
  have hU : ∑ k, star (u k) * u k = (1 : ℂ) := by
    simpa only [one_mul] using (complex_unit_vector_resolution u hu 1).symm
  have hV : ∑ l, star (v l) * v l = (1 : ℂ) := by
    simpa only [one_mul] using (complex_unit_vector_resolution v hv 1).symm
  rw [hU, hV, star_one, mul_one, mul_one]

theorem norm_sub_complexCrossContraction_le_sum {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (hv : ∑ l, ‖v l‖ ^ 2 = 1)
    (hucap : ∀ k, ‖u k‖ ≤ 1) (hvcap : ∀ l, ‖v l‖ ≤ 1) :
    ‖a * star b - complexCrossContraction a b u v G‖ ≤
      ∑ kl : K × L, ‖u kl.1 * star (v kl.2) - G kl.1 kl.2‖ := by
  have hid : a * star b - complexCrossContraction a b u v G =
      ∑ kl : K × L, ((a * star (u kl.1)) * star (b * star (v kl.2))) *
        (u kl.1 * star (v kl.2) - G kl.1 kl.2) := by
    rw [← complexCrossContraction_unit a b u v hu hv]
    simp only [complexCrossContraction, mul_sub, Finset.sum_sub_distrib]
  rw [hid]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro kl _
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_mul, norm_star, norm_star, norm_mul, norm_star]
  refine (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
  · exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hucap kl.1)
  · exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hvcap kl.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mean_complexCrossContraction_error_le_card {K L X : Type*}
    [Fintype K] [Fintype L] [Fintype X]
    (a b : X → ℂ) (u : K → X → ℂ) (v : L → X → ℂ) (G : K → L → X → ℂ) {ε : ℝ}
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ x, ‖b x‖ ≤ 1)
    (hu : ∀ x, ∑ k, ‖u k x‖ ^ 2 = 1) (hv : ∀ x, ∑ l, ‖v l x‖ ^ 2 = 1)
    (hucap : ∀ k x, ‖u k x‖ ≤ 1) (hvcap : ∀ l x, ‖v l x‖ ≤ 1)
    (herr : ∀ k l, (𝔼 x, ‖u k x * star (v l x) - G k l x‖) ≤ ε) :
    (𝔼 x, ‖a x * star (b x) - complexCrossContraction (a x) (b x)
      (fun k => u k x) (fun l => v l x) (fun k l => G k l x)‖) ≤
      (Fintype.card (K × L) : ℝ) * ε := by
  calc
    _ ≤ 𝔼 x, ∑ kl : K × L, ‖u kl.1 x * star (v kl.2 x) - G kl.1 kl.2 x‖ := by
      apply Finset.expect_le_expect
      intro x _
      exact norm_sub_complexCrossContraction_le_sum (a x) (b x)
        (fun k => u k x) (fun l => v l x) (fun k l => G k l x)
        (ha x) (hb x) (hu x) (hv x) (fun k => hucap k x) (fun l => hvcap l x)
    _ = ∑ kl : K × L, 𝔼 x, ‖u kl.1 x * star (v kl.2 x) - G kl.1 kl.2 x‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : K × L, ε := Finset.sum_le_sum (fun kl _ => herr kl.1 kl.2)
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

def mixedPermuteSample {d : ℕ} (e : Equiv.Perm (Fin (d + 2)))
    (π : Fin (d + 3) → Fin 2) : Fin (d + 3) → Fin 2 :=
  Fin.cases (π 0) (fun j => π (e j).succ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedNonconstantCorner_card (s : ℕ) :
    Fintype.card (MixedNonconstantCorner s) = 2 ^ (s + 3) - 1 := by
  simp [MixedNonconstantCorner, Fintype.card_subtype_compl]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3

theorem refined_firstProjection_le_common
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C D : Submodule R V) (hDC : D ≤ C) (K : Submodule R (Fin 4 → V)) :
    (fourRefinedRelation C D K).map (LinearMap.proj 0) ≤ C := by
  rintro v ⟨w, hw, rfl⟩
  exact ((mem_fourCommonModulo C D w).mp (fourRefinedRelation_le_common C D hDC K hw)).1 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalRowTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem unit_row_correlation_bound {H X I J : Type*}
    [Fintype H] [Fintype X] [Fintype I] [Fintype J]
    (f q : H → X → ℂ) (u : I → H → X → ℂ) (v : J → H → ℂ)
    (K : I → J → H → X → ℂ)
    (hf : ∀ h x, ‖f h x‖ ≤ 1)
    (hu : ∀ h x, ∑ i, ‖u i h x‖ ^ 2 = 1) (hv : ∀ h, ∑ j, ‖v j h‖ ^ 2 = 1)
    (huc : ∀ i h x, ‖u i h x‖ ≤ 1) (hvc : ∀ j h, ‖v j h‖ ≤ 1)
    {ε : ℝ} (herr : ∀ i j, (𝔼 h, 𝔼 x, ‖q h x * (u i h x * v j h) - K i j h x‖) ≤ ε) :
    (𝔼 h, ‖𝔼 x, f h x * star (q h x)‖) ≤
      (∑ ij : I × J, 𝔼 h, ‖𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)‖) +
        Fintype.card (I × J) * ε := by
  let z (ij : I × J) (h : H) (x : X) := u ij.1 h x * v ij.2 h
  have hz (h : H) (x : X) : ∑ ij : I × J, ‖z ij h x‖ ^ 2 = 1 := by
    simp only [z, Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, hv, mul_one, hu]
  have hzc (ij : I × J) (h : H) (x : X) : ‖z ij h x‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (huc _ _ _)).trans (hvc _ _)
  let t (ij : I × J) (h : H) (x : X) := star (z ij h x) * K ij.1 ij.2 h x
  have he (h : H) (x : X) : ‖q h x - ∑ ij, t ij h x‖ ≤
      ∑ ij : I × J, ‖q h x * z ij h x - K ij.1 ij.2 h x‖ := by
    have hh := norm_unit_vector_exchange_error (fun ij => star (z ij h x))
      (by simpa only [norm_star] using hz h x)
      (fun ij => by simpa only [norm_star] using hzc ij h x)
      (q h x) (fun ij => star (K ij.1 ij.2 h x))
    simpa only [t, star_star, ← star_mul, ← star_sub, norm_star, mul_comm] using hh
  have hterm (ij : I × J) (h : H) :
      ‖𝔼 x, f h x * star (t ij h x)‖ ≤ ‖𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)‖ := by
    have heq : (𝔼 x, f h x * star (t ij h x)) =
        v ij.2 h * (𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [t, z, star_mul, star_star]
      ring
    rw [heq, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hvc _ _)
  have hp (h : H) : ‖𝔼 x, f h x * star (q h x)‖ ≤
      (∑ ij : I × J, ‖𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)‖) +
        (𝔼 x, ∑ ij : I × J, ‖q h x * z ij h x - K ij.1 ij.2 h x‖) := by
    apply (norm_correlation_partition_bound (f h) (q h) (fun ij => t ij h) (hf h)).trans
    exact add_le_add (Finset.sum_le_sum (fun ij _ => hterm ij h))
      (Finset.expect_le_expect (fun x _ => he h x))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hp h)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm] at hm
  apply hm.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _ij : I × J, ε := Finset.sum_le_sum (fun ij _ => herr ij.1 ij.2)
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicPairPartitionPrecision
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

theorem weighted_partition_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w : I → X → ℝ) (c : I → X → ℂ) (T : X → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (hw : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x, ∑ i, w i x = 1) (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (hT : ∀ x, ‖T x‖ ≤ 1)
    (hgood : ∀ i x, x ∉ E → 0 < w i x → ‖T x - c i x‖ ≤ ε) :
    (𝔼 x, ∑ i, w i x * ‖T x - c i x‖) ≤ ε + 2 * (E.card : ℝ) / Fintype.card X := by
  have hn (x : X) : 0 ≤ ∑ i, w i x * ‖T x - c i x‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i x) (norm_nonneg _))
  have hb (x : X) (d : ℝ) (h : ∀ i, 0 < w i x → ‖T x - c i x‖ ≤ d) :
      (∑ i, w i x * ‖T x - c i x‖) ≤ d := by
    calc
      _ ≤ ∑ i, w i x * d := by
        apply Finset.sum_le_sum
        intro i _
        rcases (hw i x).eq_or_lt with hi | hi
        · rw [← hi, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (h i hi) (hw i x)
      _ = d := by rw [← Finset.sum_mul, hsum, one_mul]
  have ha (x : X) : |∑ i, w i x * ‖T x - c i x‖| = ∑ i, w i x * ‖T x - c i x‖ :=
    abs_of_nonneg (hn x)
  have herr := expect_abs_le_of_exceptional_set E
    (fun x => ∑ i, w i x * ‖T x - c i x‖) hε
    (fun x => by
      rw [ha]
      exact hb x 2 (fun i _ => (norm_sub_le _ _).trans (by linarith [hT x, hc i x])))
    (fun x hx => by rw [ha]; exact hb x ε (fun i hi => hgood i x hx hi))
  simpa only [ha] using herr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedCanonicalSample {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  fun k => if k.val < mixedCornerWeight v then 0 else 1

noncomputable def mixedPreExchangeSample {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  mixedPermuteSample (mixedHeadPermutation v) (mixedCornerSample v)

theorem mixedPermuteSample_eq_comp {s : ℕ} (e : Equiv.Perm (Fin (s + 2)))
    (π : Fin (s + 3) → Fin 2) : mixedPermuteSample e π = π ∘ zeroFixedPermutation e := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem mixedCornerSample_zeroCount {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    binaryZeroCount (mixedCornerSample v) = mixedCornerWeight v := by
  rw [binaryZeroCount, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  change (if (v i).rev = 0 then 1 else 0) = (v i).val
  have H (b : Fin 2) : (if b.rev = 0 then 1 else 0) = b.val := by
    fin_cases b <;> decide
  exact H (v i)

theorem mixedCanonicalSample_eq_sorted {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    mixedCanonicalSample v = binarySorted (mixedCornerSample v) := by
  funext k
  rw [binarySorted_threshold, mixedCornerSample_zeroCount]
  rfl

theorem mixedCanonicalSample_of_first_one {s : ℕ} (v : Fin (s + 3) → Fin 2) (h0 : v 0 = 1) :
    mixedCanonicalSample v = mixedPermuteSample (mixedTailSortPermutation v) (mixedCornerSample v) := by
  rw [mixedCanonicalSample_eq_sorted, mixedPermuteSample_eq_comp]
  exact binarySorted_tail _ (by change (v 0).rev = 0; rw [h0]; rfl)

theorem mixedCorner_exists_tail_one {s : ℕ} (v : MixedNonconstantCorner s) (h0 : v.val 0 = 0) :
    ∃ j : Fin (s + 2), v.val j.succ = 1 := by
  classical
  by_contra h
  apply v.property
  funext j
  refine Fin.cases h0 (fun j => ?_) j
  exact binary_eq_zero_of_ne_one _ (fun hj => h ⟨j, hj⟩)

theorem mixedHeadIndex_one {s : ℕ} (v : MixedNonconstantCorner s) (h0 : v.val 0 = 0) :
    v.val (mixedHeadIndex v.val).succ = 1 := by
  have h := mixedCorner_exists_tail_one v h0
  simp only [mixedHeadIndex, dif_pos h]
  exact Classical.choose_spec h

theorem mixedPreExchangeSample_one {s : ℕ} (v : MixedNonconstantCorner s) (h0 : v.val 0 = 0) :
    mixedPreExchangeSample v.val 1 = 0 := by
  change (v.val ((Equiv.swap 0 (mixedHeadIndex v.val)) 0).succ).rev = 0
  rw [Equiv.swap_apply_left, mixedHeadIndex_one v h0]
  rfl

end Erdos3

end

section

namespace Erdos3

theorem mixedNonconstantCorner_card_eq (s : ℕ) :
    Fintype.card (MixedNonconstantCorner s) = mixedCornerCount s := mixedNonconstantCorner_card s

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedRootCornerExponent (s : ℕ) : ℕ :=
  5 * mixedRootTensorExponent s * mixedCornerCount s + 4 * mixedRootTensorExponent s + 2

def mixedRootCornerCoefficient (s : ℕ) : ℕ :=
  mixedCornerCount s * mixedRootTensorExponent s * (s + 3) ^ 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFrozenMiddleRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedWeightSupportEquiv (s k : ℕ) :
    MixedWeightCorner s k ≃ {S : Finset (Fin (s + 3)) // S.card = k} :=
  (binaryWordSupportEquiv (s + 3)).subtypeEquiv (fun v => by
    change mixedCornerWeight v = k ↔ (binaryWordSupport v).card = k
    rw [binaryWordSupport_card]
    rfl)

theorem mixedWeightCorner_card (s k : ℕ) :
    Fintype.card (MixedWeightCorner s k) = (s + 3).choose k := by
  calc
    _ = Fintype.card {S : Finset (Fin (s + 3)) // S.card = k} :=
      Fintype.card_congr (mixedWeightSupportEquiv s k)
    _ = _ := by simpa only [Fintype.card_fin] using
      Fintype.card_finset_len (α := Fin (s + 3)) k

theorem mixedCornerWeight_zero_iff {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    mixedCornerWeight v = 0 ↔ v = fun _ => 0 := by
  constructor
  · intro h
    have hc : (binaryWordSupport v).card = 0 := by
      simpa only [binaryWordSupport_card, mixedCornerWeight] using h
    apply (binaryWordSupportEquiv (s + 3)).injective
    exact (Finset.card_eq_zero.mp hc).trans (binaryWordSupport_zero (s + 3)).symm
  · rintro rfl
    simp [mixedCornerWeight]

theorem mixedCornerWeight_le {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    mixedCornerWeight v ≤ s + 3 := by
  have h := (binaryWordSupport v).card_le_univ
  simpa only [binaryWordSupport_card, Fintype.card_fin, mixedCornerWeight] using h

theorem mixedCornerWeight_pos {s : ℕ} (v : MixedNonconstantCorner s) :
    0 < mixedCornerWeight v.val := by
  have h : mixedCornerWeight v.val ≠ 0 := fun h => v.property ((mixedCornerWeight_zero_iff _).mp h)
  omega

noncomputable def mixedWeightOneEquiv (s : ℕ) : Fin (s + 3) ≃ MixedWeightCorner s 1 :=
  (Fintype.equivFinOfCardEq (by simp only [mixedWeightCorner_card, Nat.choose_one_right])).symm

end Erdos3

end

section

namespace Erdos3

def mixedWeightBlockCorner {s : ℕ} (z : MixedWeightBlock s) : MixedNonconstantCorner s :=
  ⟨z.2.val, by
    intro h
    have hz := (mixedCornerWeight_zero_iff z.2.val).mpr h
    rw [z.2.property] at hz
    omega⟩

theorem mixedWeightBlockCorner_injective (s : ℕ) :
    Function.Injective (mixedWeightBlockCorner (s := s)) := by
  rintro ⟨i, v⟩ ⟨j, w⟩ h
  have hvw : v.val = w.val := congrArg Subtype.val h
  have hij : i.val + 1 = j.val + 1 :=
    v.property.symm.trans ((congrArg mixedCornerWeight hvw).trans w.property)
  have hi : i = j := Fin.ext (by omega)
  subst j
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hvw))

theorem mixedWeightBlockCorner_surjective (s : ℕ) :
    Function.Surjective (mixedWeightBlockCorner (s := s)) := by
  intro v
  have hp := mixedCornerWeight_pos v
  have hl := mixedCornerWeight_le v.val
  let k : Fin (s + 3) := ⟨mixedCornerWeight v.val - 1, by omega⟩
  have hk : mixedCornerWeight v.val = k.val + 1 := by dsimp [k]; omega
  exact ⟨⟨k, ⟨v.val, hk⟩⟩, Subtype.ext rfl⟩

noncomputable def mixedWeightBlockEquiv (s : ℕ) : MixedWeightBlock s ≃ MixedNonconstantCorner s :=
  Equiv.ofBijective mixedWeightBlockCorner
    ⟨mixedWeightBlockCorner_injective s, mixedWeightBlockCorner_surjective s⟩

theorem mixedWeightBlock_canonical {s : ℕ} (z : MixedWeightBlock s) :
    mixedCanonicalSample (mixedWeightBlockEquiv s z).val = mixedWeightSample s z.1 := by
  change (fun j : Fin (s + 3) => if j.val < mixedCornerWeight z.2.val then (0 : Fin 2) else 1) =
    (fun j : Fin (s + 3) => if j.val < z.1.val + 1 then 0 else 1)
  rw [z.2.property]

noncomputable def mixedWeightMerge {s : ℕ} {I : Type*}
    (a : (k : Fin (s + 3)) → MixedWeightCorner s (k.val + 1) → I)
    (v : MixedNonconstantCorner s) : I :=
  a ((mixedWeightBlockEquiv s).symm v).1 ((mixedWeightBlockEquiv s).symm v).2

theorem mixedWeightMerge_block {s : ℕ} {I : Type*}
    (a : (k : Fin (s + 3)) → MixedWeightCorner s (k.val + 1) → I) (z : MixedWeightBlock s) :
    mixedWeightMerge a (mixedWeightBlockEquiv s z) = a z.1 z.2 := by
  unfold mixedWeightMerge
  rw [Equiv.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedGroupedWeightMerge {s : ℕ} {I : Type*}
    (a : Fin (s + 3) → I) (b : MixedHigherCorner s → I) : MixedNonconstantCorner s → I :=
  mixedWeightMerge (Fin.cases (motive := fun k : Fin (s + 3) => MixedWeightCorner s (k.val + 1) → I)
    (fun v => a ((mixedWeightOneEquiv s).symm v)) (fun k v => b ⟨k, v⟩))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedSplitHigherMerge {s : ℕ} {I : Type*} (b : MixedMiddleCorner s → I) (c : I)
    (z : MixedHigherCorner s) : I :=
  if h : z.1.val < s + 1 then b ⟨⟨z.1.val, h⟩, z.2⟩ else c

theorem mixedSplitHigherMerge_castSucc {s : ℕ} {I : Type*} (b : MixedMiddleCorner s → I) (c : I)
    (k : Fin (s + 1)) (v : MixedWeightCorner s (k.val + 2)) :
    mixedSplitHigherMerge b c ⟨k.castSucc, v⟩ = b ⟨k, v⟩ := by
  simp only [mixedSplitHigherMerge, Fin.val_castSucc, dif_pos k.isLt]

theorem mixedSplitHigherMerge_last {s : ℕ} {I : Type*} (b : MixedMiddleCorner s → I) (c : I)
    (v : MixedWeightCorner s (s + 3)) :
    mixedSplitHigherMerge b c ⟨Fin.last (s + 1), v⟩ = c := by
  unfold mixedSplitHigherMerge
  exact dif_neg (Nat.lt_irrefl (s + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedRowCoordinateCount (s : ℕ) : ℕ := Fintype.card (MixedMiddleCorner s) + 3

theorem mixedRowIndex_card (s D : ℕ) :
    (Fintype.card (((Fin D × Fin D) × (MixedMiddleCorner s → Fin D)) × Fin D) : ℝ) =
      (D : ℝ) ^ mixedRowCoordinateCount s := by
  simp only [mixedRowCoordinateCount, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, pow_add]
  ring

end Erdos3

end

end OAI
end


