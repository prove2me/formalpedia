-- Prove2me | Definitions.Def_OAIE3v2B009
-- name    : OAIE3v2B009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:09.614645+00:00
-- url     : https://prove2.me/theorems/9a22aee7-aa62-418b-8493-e0ad42fda8e6
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 10 of 311
-- statement:
--   Definitions bundle 10 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/LayerRemovalBudgets.lean`, `Estimates/LocalAverageAmplitude.lean`, `Estimates/ModeRemovalThresholds.lean`, `Estimates/ModeShiftLengths.lean`, `Estimates/NativeCrossFactorization.lean`, `Estimates/PairedDiagonalApproximation.lean`, `Estimates/SiteTwistCommonModulus.lean`, `Estimates/SplitSmoothProductProfile.lean`, `Geometry/BoxChartCutoff.lean`, `Geometry/CompactBoxIntegral.lean`, `Geometry/FiniteSupportTranslation.lean`, `Geometry/NativeCoordinateSplitFreezing.lean`, `Geometry/ShiftedBoxSites.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/AffineResidualRecovery.lean`, `Lattices/CRTIntegerRepresentative.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/IntegerBoxObservedMean.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/RectangularLatticeCells.lean`, `Linear/BooleanJetMatrixFactor.lean`, `Linear/CanonicalJointFrameGeometry.lean`, `Polynomial/BoundedRealPolynomialBasis.lean`, `Polynomial/CRTPolynomialPatchComposition.lean`, `Sampling/AllocatedProbabilityGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RectangularLatticeCells
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularLatticeRound (a S x : J → ℝ) : J → ℤ :=
  fun j => ⌊a j + S j * x j⌋

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CompactBoxIntegral
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {J : Type*} [Fintype J]

theorem compactBox_integrable (f : (J → ℝ) → ℝ) (hf : Continuous f) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : J → ℝ) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hx (hsupport x h)

theorem integral_norm_le_box (f : (J → ℝ) → ℝ) {R C : ℝ} (hR : 0 ≤ R)
    (hzero : ∀ x, R < ‖x‖ → f x = 0) (hbound : ∀ x, ‖x‖ ≤ R → ‖f x‖ ≤ C) :
    (∫ x, ‖f x‖) ≤ C * (2 * R) ^ Fintype.card J := by
  let s := Metric.closedBall (0 : J → ℝ) R
  have hs : MeasurableSet s := measurableSet_closedBall
  have hi : Integrable (s.indicator (fun _ : J → ℝ => C)) :=
    (integrableOn_const ((isCompact_closedBall (0 : J → ℝ) R).measure_lt_top.ne)).integrable_indicator hs
  have hb : ∀ x, ‖f x‖ ≤ s.indicator (fun _ : J → ℝ => C) x := by
    intro x
    by_cases hx : x ∈ s
    · have hx' : ‖x‖ ≤ R := by simpa only [s, Metric.mem_closedBall, dist_zero_right] using hx
      simpa only [Set.indicator_of_mem hx] using hbound x hx'
    · have hx' : R < ‖x‖ := by simpa only [s, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      simp only [hzero x hx', norm_zero, Set.indicator_of_notMem hx, le_refl]
  have hv : volume.real s = (2 * R) ^ Fintype.card J := by
    rw [measureReal_def, Real.volume_pi_closedBall 0 hR, ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ ∫ x, s.indicator (fun _ : J → ℝ => C) x :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hi
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_indicator_const C hs, hv, smul_eq_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev BoundedIntegerExponent (K : Type*) (h : ℕ) :=
  {e : K →₀ ℕ // e.sum (fun _ n => n) ≤ h}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteSupportTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem translation_difference_zero_off {G : Type*} [AddCommGroup G] [DecidableEq G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0) (v x : G)
    (hx : x ∉ S ∪ S.image (fun y => y + v)) : w (x - v) - w x = 0 := by
  have hxS : x ∉ S := fun h => hx (Finset.mem_union_left _ h)
  have hyS : x - v ∉ S := by
    intro h
    apply hx
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x - v, h, sub_add_cancel x v⟩)
  rw [hw _ hyS, hw _ hxS, sub_self]

theorem finiteSupport_translation_l1_bound {G : Type*} [AddCommGroup G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0) (v : G)
    {B : ℝ} (hB : 0 ≤ B) (hstep : ∀ x, |w (x - v) - w x| ≤ B) :
    (∑' x, |w (x - v) - w x|) ≤ 2 * (S.card : ℝ) * B := by
  classical
  let U := S ∪ S.image (fun y => y + v)
  have hz (x : G) (hx : x ∉ U) : |w (x - v) - w x| = 0 := by
    rw [translation_difference_zero_off w S hw v x hx, abs_zero]
  have hc : (U.card : ℝ) ≤ 2 * (S.card : ℝ) := by
    have hn : U.card ≤ S.card + S.card :=
      (Finset.card_union_le S (S.image (fun y => y + v))).trans
        (Nat.add_le_add_left Finset.card_image_le _)
    exact_mod_cast (show U.card ≤ 2 * S.card by omega)
  calc
    (∑' x, |w (x - v) - w x|) = ∑ x ∈ U, |w (x - v) - w x| :=
      (hasSum_sum_of_ne_finset_zero hz).tsum_eq
    _ ≤ ∑ _x ∈ U, B := Finset.sum_le_sum (fun x _ => hstep x)
    _ = (U.card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hB

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalAverageAmplitude
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_weighted_test_summable {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) (f : X → ℂ) : Summable (fun x => (w x : ℂ) * f x) := by
  apply (hasSum_sum_of_ne_finset_zero (s := S) _).summable
  intro x hx
  simp only [hw x hx, Complex.ofReal_zero, zero_mul]

theorem finite_weighted_test_norm_le {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖∑' x, (w x : ℂ) * f x‖ ≤ ∑' x, |w x| := by
  have hs : Summable (fun x => |w x|) :=
    (hasSum_sum_of_ne_finset_zero (s := S) (fun x hx => by rw [hw x hx, abs_zero])).summable
  apply tsum_of_norm_bounded hs.hasSum
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)).trans_eq (mul_one _)

theorem finite_weighted_translation_test_le {G : Type*} [AddCommGroup G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (v : G) :
    ‖(∑' x, (w x : ℂ) * f (x + v)) - ∑' x, (w x : ℂ) * f x‖ ≤
      ∑' x, |w (x - v) - w x| := by
  classical
  have hshift (x : G) (hx : x ∉ S.image (fun y => y + v)) : w (x - v) = 0 := by
    apply hw
    intro hy
    exact hx (Finset.mem_image.mpr ⟨x - v, hy, sub_add_cancel x v⟩)
  have hleft : (∑' x, (w x : ℂ) * f (x + v)) = ∑' x, (w (x - v) : ℂ) * f x := by
    simpa using (Equiv.addRight v).tsum_eq (fun x => (w (x - v) : ℂ) * f x)
  have he : (∑' x, (w x : ℂ) * f (x + v)) - ∑' x, (w x : ℂ) * f x =
      ∑' x, ((w (x - v) - w x : ℝ) : ℂ) * f x := by
    rw [hleft, ← (finite_weighted_test_summable _ _ hshift f).tsum_sub
      (finite_weighted_test_summable w S hw f)]
    apply tsum_congr
    intro x
    rw [Complex.ofReal_sub, sub_mul]
  rw [he]
  exact finite_weighted_test_norm_le _ (S ∪ S.image (fun y => y + v))
    (translation_difference_zero_off w S hw v) f hf

theorem normalized_finite_translation_test_le {G : Type*} [AddCommGroup G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (v : G) {Z : ℝ} (hZ : 0 < Z) :
    ‖(∑' x, ((w x / Z : ℝ) : ℂ) * f (x + v)) -
      ∑' x, ((w x / Z : ℝ) : ℂ) * f x‖ ≤ (∑' x, |w (x - v) - w x|) / Z := by
  have h := finite_weighted_translation_test_le (fun x => w x / Z) S
    (fun x hx => by rw [hw x hx, zero_div]) f hf v
  simpa only [← sub_div, abs_div, abs_of_pos hZ, tsum_div_const] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_weighted_expect_comm {G X : Type*} [Fintype X]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0) (F : X → G → ℂ) :
    (𝔼 u, ∑' x, (w x : ℂ) * F u x) = ∑' x, (w x : ℂ) * (𝔼 u, F u x) := by
  have ht (f : G → ℂ) : (∑' x, (w x : ℂ) * f x) = ∑ x ∈ S, (w x : ℂ) * f x := by
    apply (hasSum_sum_of_ne_finset_zero (s := S) _).tsum_eq
    intro x hx
    simp only [hw x hx, Complex.ofReal_zero, zero_mul]
  simp_rw [ht]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.mul_expect _ _ _).symm

theorem finite_probability_test_norm_le {G : Type*}
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∑' x, w x) = 1)
    (f : G → ℂ) {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    ‖∑' x, (w x : ℂ) * f x‖ ≤ B := by
  have hs : Summable w := (hasSum_sum_of_ne_finset_zero hw).summable
  have hm : HasSum (fun x => w x * B) B := by
    simpa only [hmass, one_mul] using hs.hasSum.mul_right B
  apply tsum_of_norm_bounded hm
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
  exact mul_le_mul_of_nonneg_left (hf x) (hw0 x)

theorem finite_probability_shift_transfer {G X : Type*} [AddCommGroup G]
    [Fintype X] [Nonempty X]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∑' x, w x) = 1)
    (shift : X → G) (f : G → ℂ) {ε B : ℝ}
    (hmove : ∀ u, ‖(∑' x, (w x : ℂ) * f (x + shift u)) -
      ∑' x, (w x : ℂ) * f x‖ ≤ ε)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ B) :
    ‖∑' x, (w x : ℂ) * f x‖ ≤ ε + B := by
  let base := ∑' x, (w x : ℂ) * f x
  let mean := 𝔼 u, ∑' x, (w x : ℂ) * f (x + shift u)
  have he : mean - base = 𝔼 u, ((∑' x, (w x : ℂ) * f (x + shift u)) - base) := by
    rw [Finset.expect_sub_distrib, Fintype.expect_const]
  have hdiff : ‖mean - base‖ ≤ ε := by
    rw [he]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun u _ => hmove u)).trans_eq (Fintype.expect_const ε)
  have hmean : ‖mean‖ ≤ B := by
    dsimp only [mean]
    rw [finite_weighted_expect_comm w S hw]
    exact finite_probability_test_norm_le w S hw hw0 hmass _ hlocal
  calc
    ‖base‖ = ‖(base - mean) + mean‖ := by rw [sub_add_cancel]
    _ ≤ ‖base - mean‖ + ‖mean‖ := norm_add_le _ _
    _ ≤ ε + B := add_le_add (by simpa only [norm_sub_rev] using hdiff) hmean

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxChartCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def coordinateBoxCutoff {ι : Type*} [Fintype ι]
    (χ : ℝ → ℝ) (r : ℝ) (v : ι → ℝ) : ℝ := ∏ i, χ (v i / r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def tensorCutoffWeight {ι : Type*} {E : ι → Type*} [Fintype ι] (w : ∀ i, E i → ℝ) (x : ∀ i, E i) : ℝ :=
  ∏ i, w i (x i)

theorem tensorCutoffWeight_integral {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ) :
    (∫ x, tensorCutoffWeight w x) = ∏ i, ∫ y, w i y :=
  integral_fintype_prod_volume_eq_prod w

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ShiftedBoxSites
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def shiftedBoxSite {h : ℕ} {X V : Type*} [AddCommGroup V]
    (base : V) (coefficient : Fin h → ℤ) (shift : X → V) (x : Fin h → X) : V :=
  base + ∑ i, coefficient i • shift (x i)

theorem shiftedBoxSite_update {h : ℕ} {X V : Type*} [AddCommGroup V]
    (base : V) (coefficient : Fin h → ℤ) (shift : X → V) {i : Fin h}
    (hi : coefficient i = 0) (x : Fin h → X) (a : X) :
    shiftedBoxSite base coefficient shift (Function.update x i a) =
      shiftedBoxSite base coefficient shift x := by
  unfold shiftedBoxSite
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp only [hi, zero_smul]
  · simp only [Function.update_of_ne hj]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

open scoped BigOperators

abbrev IntegerScalarCubeBox (I : Type*) (L : ℕ) :=
  Option I → Finset.Ico (-(L : ℤ)) (L : ℤ)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PairedDiagonalApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensorDenominatorBound_le {H I : Type*} [Fintype H] [DecidableEq H] [Fintype I]
    {B S : ℝ} (hB : 0 ≤ B) (s : I → ℝ) (hs : ∀ i, 0 ≤ s i) (hS : ∀ i, s i ≤ S) :
    (∏ j : H → I, (B * ∏ i, s (j i))) ≤ (B * S ^ Fintype.card H) ^ (Fintype.card I ^ Fintype.card H) := by
  have hj (j : H → I) : (∏ i, s (j i)) ≤ S ^ Fintype.card H := by
    calc
      (∏ i, s (j i)) ≤ ∏ _i : H, S := Finset.prod_le_prod (fun i _ => hs (j i)) (fun i _ => hS (j i))
      _ = S ^ Fintype.card H := by simp
  calc
    (∏ j : H → I, (B * ∏ i, s (j i))) ≤ ∏ _j : H → I, (B * S ^ Fintype.card H) :=
      Finset.prod_le_prod (fun j _ => mul_nonneg hB (Finset.prod_nonneg (fun i _ => hs (j i))))
        (fun j _ => mul_le_mul_of_nonneg_left (hj j) hB)
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LayerRemovalBudgets
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def layerRemovalRankBudget (m d : ℕ) (C D B A S : ℝ) : ℝ :=
  1 + ∑ i : Fin m,
    (((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) +
      (B * S ^ (i.val + 1)) ^ (d ^ (i.val + 1)) +
      (d : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B))

theorem layerRemovalRankBudget_bounds {m : ℕ} (i : Fin m) (d : ℕ)
    {C D B A S : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B) (hA : 0 ≤ A) (hS : 0 ≤ S) :
    ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) ≤ layerRemovalRankBudget m d C D B A S ∧
    (B * S ^ (i.val + 1)) ^ (d ^ (i.val + 1)) ≤ layerRemovalRankBudget m d C D B A S ∧
    (d : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B) ≤ layerRemovalRankBudget m d C D B A S := by
  let cost (j : Fin m) :=
    ((j.val + 1).factorial : ℝ) * (C * D ^ (j.val + 1)) +
      (B * S ^ (j.val + 1)) ^ (d ^ (j.val + 1)) +
      (d : ℝ) ^ (j.val + 1) * (A ^ (j.val + 1) * B)
  have hcost j : 0 ≤ cost j := by dsimp [cost]; positivity
  have hs : cost i ≤ ∑ j : Fin m, cost j :=
    Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ i)
  have ht : cost i ≤ layerRemovalRankBudget m d C D B A S := by
    exact hs.trans (le_add_of_nonneg_left zero_le_one)
  have hrow : 0 ≤ ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) := by positivity
  have hden : 0 ≤ (B * S ^ (i.val + 1)) ^ (d ^ (i.val + 1)) := by positivity
  have hcoeff : 0 ≤ (d : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B) := by positivity
  dsimp [cost] at ht
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModeRemovalThresholds
namespace OAI

section

namespace Erdos3

noncomputable def modeRemovalBeta (ε : ℝ) : ℝ := min (1 / 2) (ε / 2)

theorem modeRemovalBeta_pos {ε : ℝ} (hε : 0 < ε) : 0 < modeRemovalBeta ε := by
  exact lt_min (by norm_num) (by positivity)

theorem modeRemovalBeta_le_one (ε : ℝ) : modeRemovalBeta ε ≤ 1 :=
  (min_le_left _ _).trans (by norm_num)

noncomputable def modeRemovalBias (m : ℕ) (ε : ℝ) : ℝ := modeRemovalBeta ε ^ (2 ^ m)

theorem modeRemovalBias_pos (m : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < modeRemovalBias m ε :=
  pow_pos (modeRemovalBeta_pos hε) _

theorem modeRemovalBias_le {m : ℕ} (i : Fin m) {ε : ℝ} (hε : 0 < ε) :
    modeRemovalBias m ε ≤ modeRemovalBeta ε ^ (2 ^ (i.val + 1)) := by
  apply pow_le_pow_of_le_one (modeRemovalBeta_pos hε).le (modeRemovalBeta_le_one ε)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.succ_le_of_lt i.isLt)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModeShiftLengths
namespace OAI

section

namespace Erdos3

noncomputable def modeShiftLength (H T : ℝ) (stride : ℕ) : ℕ :=
  ⌊H / ((stride : ℝ) * T)⌋₊

theorem modeShiftLength_bounds {H T B : ℝ} {stride : ℕ}
    (hs : 0 < stride) (hT : 0 < T) (hB : 1 ≤ B)
    (hsize : (stride : ℝ) * T * (B + 1) ≤ H) :
    B ≤ (modeShiftLength H T stride : ℝ) ∧
      ((stride : ℝ) * T) * (modeShiftLength H T stride : ℝ) ≤ H ∧
      H ≤ (2 * T) * ((stride : ℝ) * (modeShiftLength H T stride : ℝ)) := by
  have hs' : 0 < (stride : ℝ) := by exact_mod_cast hs
  have hd : 0 < (stride : ℝ) * T := mul_pos hs' hT
  have hx : B + 1 ≤ H / ((stride : ℝ) * T) :=
    (le_div_iff₀ hd).mpr (by nlinarith [hsize])
  have hx0 : 0 ≤ H / ((stride : ℝ) * T) := by linarith
  have hf := Nat.lt_floor_add_one (H / ((stride : ℝ) * T))
  have hnb : B < (modeShiftLength H T stride : ℝ) := by
    dsimp [modeShiftLength]
    linarith
  have hu := (le_div_iff₀ hd).mp (Nat.floor_le hx0)
  have hl := (div_lt_iff₀ hd).mp hf
  have hn1 : 1 ≤ (modeShiftLength H T stride : ℝ) := hB.trans hnb.le
  have hprod := mul_le_mul_of_nonneg_left hn1 hd.le
  refine ⟨hnb.le, ?_, ?_⟩
  · change ((stride : ℝ) * T) * (⌊H / ((stride : ℝ) * T)⌋₊ : ℝ) ≤ H
    nlinarith [hu]
  · change H ≤ (2 * T) * ((stride : ℝ) * (⌊H / ((stride : ℝ) * T)⌋₊ : ℝ))
    dsimp [modeShiftLength] at hprod
    nlinarith [hl]

theorem exists_mode_shift_lengths {I K : Type*} (m : ℕ) {D T B ρ r : ℝ}
    (hT : 0 < T) (hB : 1 ≤ B) (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hmove : (m : ℝ) * D ≤ r * ρ * T)
    (H : I → ℝ) (stride : I → ℕ) (hs : ∀ j, 0 < stride j)
    (hsize : ∀ j, (stride j : ℝ) * T * (B + 1) ≤ H j)
    (V : K × I → ℝ) (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ N : I → ℕ, (∀ j, B ≤ (N j : ℝ)) ∧
      (∀ j, H j ≤ (2 * T) * ((stride j : ℝ) * (N j : ℝ))) ∧
      ∀ z, (m : ℝ) * D * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z := by
  let N := fun j => modeShiftLength (H j) T (stride j)
  have hn j := modeShiftLength_bounds (hs j) hT hB (hsize j)
  refine ⟨N, (fun j => (hn j).1), (fun j => (hn j).2.2), ?_⟩
  intro z
  have hn0 : 0 ≤ (stride z.2 : ℝ) * (N z.2 : ℝ) := by positivity
  calc
    _ ≤ (r * ρ * T) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hmove hn0
    _ = (r * ρ) * (((stride z.2 : ℝ) * T) * (N z.2 : ℝ)) := by ring
    _ ≤ (r * ρ) * H z.2 := mul_le_mul_of_nonneg_left (hn z.2).2.1 (mul_nonneg hr hρ.le)
    _ = r * (ρ * H z.2) := by ring
    _ ≤ r * V z := mul_le_mul_of_nonneg_left (hwidth z) hr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def integerBasisOfReal (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) : Basis I ℤ Λ :=
  (b.restrictScalars ℤ).map (LinearEquiv.ofEq _ _ hb)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def booleanJetExtractionMatrix {α O : Type*} [DecidableEq α]
    (rows : O → Finset α) : Matrix O (Finset α) ℤ :=
  fun o t => if t ⊆ rows o then (-1 : ℤ) ^ (rows o \ t).card else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

noncomputable def physicalSiteWidth {K I : Type*} [Fintype K]
    (root : K → ℤ) (W : Option K × I → ℝ) (i : I) : ℝ :=
  W (none,i) + ∑ k, |(root k : ℝ)| * W (some k,i)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def centeredSpatialWidths {K I : Type*} (B σ : ℝ) (N : I → ℕ) : Option K × I → ℝ :=
  fun z => match z.1 with
    | none => (N z.2 : ℝ)/8
    | some _ => σ*(N z.2 : ℝ)/(8*(1+B))

namespace BooleanCubeKernel

theorem centeredSpatialWidths_fit {K I : Type*} [Fintype K] {B σ : ℝ}
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (N : I → ℕ) (i : I) :
    4 * physicalSiteWidth root (centeredSpatialWidths B σ N) i ≤ (N i : ℝ) := by
  have hn := Nat.cast_nonneg (α := ℝ) (N i)
  have hb : 1+B ≠ 0 := ne_of_gt (by linarith)
  have hv : 0 ≤ σ*(N i : ℝ)/(8*(1+B)) := by positivity
  have ht : B*(σ*(N i : ℝ)/(8*(1+B))) ≤ (N i : ℝ)/8 := by
    calc
      _ ≤ (1+B)*(σ*(N i : ℝ)/(8*(1+B))) :=
        mul_le_mul_of_nonneg_right (by linarith) hv
      _ = σ*(N i : ℝ)/8 := by field_simp
      _ ≤ (N i : ℝ)/8 := by
        exact div_le_div_of_nonneg_right (by nlinarith) (by norm_num)
  simp only [physicalSiteWidth, centeredSpatialWidths, ← Finset.sum_mul]
  have hs := mul_le_mul_of_nonneg_right hroot hv
  nlinarith

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def trimmedSpatialWidths {K I : Type*} (B τ : ℝ) (N : I → ℕ) : Option K × I → ℝ :=
  fun z => τ * centeredSpatialWidths B 1 N z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Add G]

noncomputable def fourPointProduct (f₁ f₂ f₃ f₄ : G → ℂ) (a x : G) : ℂ :=
  star (f₁ x) * f₂ (x + a) * f₃ x * star (f₄ (x + a))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

universe u v

structure ScalarSiteExpansion (S : Type u) where
  Term : Type v
  [termFinite : Fintype Term]
  period : Term → ℕ
  coefficient : Term → ℂ
  factor : (i : Term) → S → ZMod (period i) → ℝ → ℂ

attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateSplitFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

def coordinateSplitBound (s : ℕ) (i : σ) (b : Bool) (j : σ) : ℕ :=
  if b then (if j = i then s - 1 else s) else (if j = i then s else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidualRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def recoveredSmallLift {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (a : Fin d → ℝ) (c : Fin m → ℤ) (e : Fin d → ℝ) : Fin m → ℝ :=
  fun i => (∑ j, (M i j : ℝ) * (a j - e j)) - c i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTIntegerRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open _root_.MvPolynomial

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtIntegerCoefficient (j : J) : ℤ :=
  ((ZMod.prodEquivPi N hN).symm (Pi.single j (1 : ZMod (N j)))).val

noncomputable def crtRepresentativePolynomial : MvPolynomial J ℝ :=
  ∑ j, ((crtIntegerCoefficient N hN j : ℝ) / (∏ i, N i : ℕ)) • X j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def cyclicBranchOffset {N : ℕ} (h : ZMod N) (branch : Bool) : ℤ :=
  (h.val : ℤ) - if branch then (N : ℤ) else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalJointFrameGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def canonicalJointFrameWindowConstant (d : ℕ) (τ : ℝ) : ℝ :=
  16 * (2 * (d : ℝ) + 1) / τ

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialPatchComposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtLiftPolynomial : MvPolynomial (J ⊕ Fin 1) ℝ :=
  (∑ j, (crtIntegerCoefficient N hN j : ℝ) • X (Sum.inl j)) -
    ((∏ j, N j : ℕ) : ℝ) • X (Sum.inr 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

abbrev JetAmbientIndex {m : ℕ} (O J : Fin m → Type*) := Σ j, O j × J j

end Erdos3.VectorPolynomial

end

end OAI
end


