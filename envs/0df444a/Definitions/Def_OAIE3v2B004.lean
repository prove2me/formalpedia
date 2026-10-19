-- Prove2me | Definitions.Def_OAIE3v2B004
-- name    : OAIE3v2B004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:31.00671+00:00
-- url     : https://prove2.me/theorems/bd19e402-9add-43f5-bd3c-121939410cea
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 5 of 311
-- statement:
--   Definitions bundle 5 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/FiniteProductBudget.lean`, `Dynamics/VerticalDecompositionBudget.lean`, `Estimates/BufferedSiteExpansion.lean`, `Estimates/ComplexUnitLocalLipschitz.lean`, `Estimates/FrozenCosetVariation.lean`, `Estimates/NativeCentralSeed.lean`, `Estimates/NativeEquivalenceTransitivity.lean`, `Estimates/NativeGraphSmallDifference.lean`, `Estimates/PeriodicIsometricAction.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/PinnedSectionMeans.lean`, `Estimates/PowerSubgroup.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/RealSubquotientEquiv.lean`, `Estimates/RelativeFiberSlicePatch.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/RiemannianLipschitz.lean`, `Estimates/SplitGroupRelative.lean`, `Estimates/SquarefreePermutationFiltration.lean`, `Estimates/TangentModelVector.lean`, `Estimates/UnitExpansionCorrelation.lean`, `Estimates/WeightedPatchReparam.lean`, `Estimates/WeightedTwistedTranslationLipschitz.lean`, `FixedDensity/OrderedPatternPartition.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/ExponentialBohrVolume.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Fourier/PivotAnnihilatorFrequencyCode.lean`, `Fourier/RationalLiftCharacterTwist.lean`, `Geometry/CommonStrideCoordinates.lean`, `Geometry/CoordinateQuotientModel.lean`, `Geometry/CoordinateSupNorm.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/ProductSectionSupport.lean`, `Geometry/RiemannianLocalCoordinates.lean`, `Lattices/BufferedIntegerLift.lean`, `Lattices/ResidueEventOrDescent.lean`, `Lattices/ResidueSliceCountingCost.lean`, `Linear/BasisCoordinateBounds.lean`, `Linear/CircleFejerKernel.lean`, `Linear/SquareBasisGeometry.lean`, `Nilpotent/BCHConjugationLinear.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Polynomial/RealPolynomialEvaluationMass.lean`, `Polynomial/SquarefreeTotalDegree.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FiniteProductBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sigma_card_le_budget {α : Type*} [Fintype α] {κ : α → Type*}
    [∀ a, Fintype (κ a)] {p : ℝ} (hp : 0 ≤ p)
    (hα : (Fintype.card α : ℝ) ≤ p) (hκ : ∀ a, (Fintype.card (κ a) : ℝ) ≤ p) :
    (Fintype.card (Σ a, κ a) : ℝ) ≤ p ^ 2 := by
  classical
  calc
    _ = ∑ a, (Fintype.card (κ a) : ℝ) := by rw [Fintype.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _a : α, p := Finset.sum_le_sum (fun a _ => hκ a)
    _ = (Fintype.card α : ℝ) * p := by simp
    _ ≤ p * p := mul_le_mul_of_nonneg_right hα hp
    _ = p ^ 2 := by ring

theorem product_denominator_le_budget {α : Type*} [Fintype α] (m : α → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hα : (Fintype.card α : ℝ) ≤ p)
    (hm : ∀ a, (m a : ℝ) ≤ Real.exp p) :
    ((∏ a, m a : ℕ) : ℝ) ≤ Real.exp (p ^ 2) := by
  classical
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _a : α, Real.exp p := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun index _ => hm index)
    _ = Real.exp ((Fintype.card α : ℝ) * p) := by rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
    _ ≤ Real.exp (p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VerticalDecompositionBudget
namespace OAI

section

namespace Erdos3

def centralActionBudget (p : ℝ) : ℝ := (p + 3) ^ 9 + 2 * p + 2

def verticalDecompositionBudget (p : ℝ) : ℝ :=
  let q := centralActionBudget p
  2 * q * (2 * q + 2) ^ 4 + ((2 * q + 2) ^ 4 + q + (p + 3) ^ 5 + 2) ^ 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_mul_star_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℂ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * star (g x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he : f x * star (g x) - f y * star (g y) =
      f x * star (g x - g y) + (f x - f y) * star (g y) := by
    rw [star_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖f x * star (g x - g y)‖ + ‖(f x - f y) * star (g y)‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul, norm_star, norm_star]
    _ ≤ Bf * (Kg * dist x y) + (Kf * dist x y) * Bg := by
      apply add_le_add
      · exact mul_le_mul (hBf x) (by simpa only [dist_eq_norm] using hg.dist_le_mul x y)
          (norm_nonneg _) Bf.coe_nonneg
      · exact mul_le_mul (by simpa only [dist_eq_norm] using hf.dist_le_mul x y) (hBg y)
          (norm_nonneg _) (mul_nonneg Kf.coe_nonneg dist_nonneg)
    _ = _ := by push_cast; ring

end Erdos3

end

section

open scoped NNReal BigOperators

namespace Erdos3

theorem lipschitz_mul_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℂ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) := by
  have hstar : LipschitzWith Kg (fun x => star (g x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using hg.dist_le_mul x y
  simpa only [star_star] using lipschitz_mul_star_of_bounds f (fun x => star (g x)) hf hstar
    hBf (fun x => by simpa only [norm_star] using hBg x)

theorem bounded_lipschitz_finset_prod {ι X : Type*} [PseudoMetricSpace X]
    (s : Finset ι) (f : ι → X → ℂ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i ∈ s, LipschitzWith K (f i)) (hn : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ B) :
    (∀ x, ‖∏ i ∈ s, f i x‖ ≤ (B : ℝ) ^ s.card) ∧
      LipschitzWith (s.card * K * B ^ s.card) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · intro x
      simp
    · simpa only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero, zero_mul] using
        (LipschitzWith.const (α := X) (1 : ℂ))
  | @insert a s ha ih =>
    obtain ⟨hns, hls⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hn i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    constructor
    · intro x
      rw [norm_mul, pow_succ']
      exact mul_le_mul (hn a (Finset.mem_insert_self _ _) x) (hns x) (norm_nonneg _) B.coe_nonneg
    · have hm := lipschitz_mul_of_bounds (f a) (fun x => ∏ i ∈ s, f i x)
        (hf a (Finset.mem_insert_self _ _)) hls (hn a (Finset.mem_insert_self _ _))
        (Bg := B ^ s.card) (fun x => by simpa only [NNReal.coe_pow] using hns x)
      apply hm.weaken
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ K * B ^ s.card from zero_le)
      nlinarith

theorem bounded_lipschitz_fintype_prod {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (f : ι → X → ℂ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, ‖f i x‖ ≤ B) :
    (∀ x, ‖∏ i, f i x‖ ≤ (B : ℝ) ^ Fintype.card ι) ∧
      LipschitzWith (Fintype.card ι * K * B ^ Fintype.card ι) (fun x => ∏ i, f i x) := by
  simpa only [Finset.card_univ] using
    bounded_lipschitz_finset_prod Finset.univ f hB (fun i _ => hf i) (fun i _ => hn i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexUnitLocalLipschitz
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem separated_complex_tsum_lipschitz {ι X : Type*} [PseudoMetricSpace X]
    (f : ι → X → ℂ) {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (hsep : ∀ x i j, f i x ≠ 0 → f j x ≠ 0 → i = j) :
    LipschitzWith (2 * K) (fun x => ∑' i, f i x) := by
  have hsingle (x : X) (i : ι) (hi : f i x ≠ 0) : (∑' j, f j x) = f i x := by
    apply tsum_eq_single i
    intro j hji
    by_contra hj
    exact hji (hsep x j i hj hi)
  have hzero (x : X) (hx : ¬∃ i, f i x ≠ 0) : (∑' i, f i x) = 0 := by
    have hz : ∀ i, f i x = 0 := fun i => not_ne_iff.mp (fun hi => hx ⟨i, hi⟩)
    simp only [hz, tsum_zero]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hK : (K : ℝ) * dist x y ≤ (2 * K : ℝ≥0) * dist x y := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    nlinarith [K.coe_nonneg, dist_nonneg (x := x) (y := y)]
  by_cases hx : ∃ i, f i x ≠ 0
  · obtain ⟨i, hi⟩ := hx
    rw [hsingle x i hi]
    by_cases hy : ∃ j, f j y ≠ 0
    · obtain ⟨j, hj⟩ := hy
      rw [hsingle y j hj]
      by_cases hij : i = j
      · subst j
        exact ((hf i).dist_le_mul x y).trans hK
      · have hiy : f i y = 0 := by
          by_contra h
          exact hij (hsep y i j h hj)
        have hjx : f j x = 0 := by
          by_contra h
          exact hij (hsep x i j hi h)
        have h1 := (hf i).dist_le_mul x y
        have h2 := (hf j).dist_le_mul x y
        rw [hiy] at h1
        rw [hjx] at h2
        have ht := dist_triangle (f i x) 0 (f j y)
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        linarith
    · rw [hzero y hy]
      have hiy : f i y = 0 := not_ne_iff.mp (fun h => hy ⟨i, h⟩)
      simpa only [hiy] using ((hf i).dist_le_mul x y).trans hK
  · rw [hzero x hx]
    by_cases hy : ∃ j, f j y ≠ 0
    · obtain ⟨j, hj⟩ := hy
      rw [hsingle y j hj]
      have hjx : f j x = 0 := not_ne_iff.mp (fun h => hx ⟨j, h⟩)
      simpa only [hjx] using ((hf j).dist_le_mul x y).trans hK
    · rw [hzero y hy, dist_self]
      positivity

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem lipschitzWith_of_complex_unit_near {X : Type*} [PseudoMetricSpace X]
    (f : X → ℂ) (C L : ℝ≥0) (hbound : ∀ x, ‖f x‖ ≤ 1)
    (hnear : ∀ x y, (C : ℝ) * dist x y < 1 →
      ‖f x - f y‖ ≤ (L : ℝ) * dist x y) :
    LipschitzWith (max (2 * C) L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  by_cases hclose : (C : ℝ) * dist x y < 1
  · exact (hnear x y hclose).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right (2 * C) L) dist_nonneg)
  · have hxy : ‖f x - f y‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hbound x, hbound y])
    have hfar : 2 ≤ ((2 * C : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      linarith [le_of_not_gt hclose]
    exact hxy.trans (hfar.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_left (2 * C) L) dist_nonneg))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenCosetVariation
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G]

theorem central_smul_eq_self_of_mem (Γ : Subgroup G) {g : G}
    (hg : g ∈ Γ) (hc : ∀ a : G, Commute g a) (x : G ⧸ Γ) : g • x = x := by
  induction x using Quotient.inductionOn with
  | h a =>
    change (QuotientGroup.mk (g * a) : G ⧸ Γ) = QuotientGroup.mk a
    rw [(hc a).eq]
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using Γ.inv_mem hg

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RiemannianLipschitz
namespace OAI

section

namespace Erdos3

open Manifold MeasureTheory _root_.Set
open scoped Manifold ContDiff ENNReal NNReal Bundle

variable {E F H K M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : N, ENorm (TangentSpace J x)]

theorem pathELength_comp_le_mul_of_mfderiv_bound {φ : M → N} {C : ℝ≥0}
    (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ C * ‖v‖ₑ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (a b : ℝ) :
    pathELength J (φ ∘ γ) a b ≤ C * pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc,
    ← lintegral_const_mul' (C : ℝ≥0∞) _ (by simp)]
  apply lintegral_mono
  intro t
  exact (congrArg (fun v : TangentSpace J (φ (γ t)) => ‖v‖ₑ)
    (mfderiv_comp_apply t (hφ.mdifferentiableAt one_ne_zero)
      (hγ.mdifferentiableAt one_ne_zero) 1)).trans_le (hbound (γ t) _)

variable [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
  [∀ x : N, ENormSMulClass ℝ (TangentSpace J x)]

theorem riemannianEDist_le_mul_of_mfderiv_bound {φ : M → N} {C : ℝ≥0}
    (hC : 0 < C) (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ C * ‖v‖ₑ)
    (x y : M) : riemannianEDist J (φ x) (φ y) ≤ C * riemannianEDist I x y := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hCt : (C : ℝ≥0∞) ≠ ⊤ := by simp
  apply le_of_forall_gt
  intro r hr
  have hinput : riemannianEDist I x y < r / C := by
    apply (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mpr
    simpa only [mul_comm] using hr
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hinput zero_lt_one
  have hends : riemannianEDist J (φ x) (φ y) ≤ pathELength J (φ ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply, hγ0])
      (by simp only [Function.comp_apply, hγ1]) zero_le_one
  have hmul : (C : ℝ≥0∞) * pathELength I γ 0 1 < r := by
    simpa only [mul_comm] using
      (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mp hlen
  exact (hends.trans (pathELength_comp_le_mul_of_mfderiv_bound hφ hbound hγ 0 1)).trans_lt hmul

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TangentModelVector
namespace OAI

section

namespace Erdos3

open scoped Manifold

def tangentModelVector {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {x : M} (v : TangentSpace I x) : E := v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RiemannianLocalCoordinates
namespace OAI

section

namespace Erdos3

open Manifold MeasureTheory _root_.Set
open scoped Manifold ContDiff ENNReal NNReal Bundle Topology

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]

theorem coordinate_edist_le_mul_pathELength {f : M → F} {C : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, ∀ v : TangentSpace I (γ t),
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f (γ t) v)‖ₑ ≤ C * ‖v‖ₑ) :
    edist (f (γ a)) (f (γ b)) ≤ C * pathELength I γ a b := by
  have hsmooth : ContDiff ℝ 1 (f ∘ γ) := (hf.comp hγ).contDiff
  calc
    _ = ‖(f ∘ γ) b - (f ∘ γ) a‖ₑ := by rw [edist_comm, edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc a b, ‖deriv (f ∘ γ) t‖ₑ :=
      enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hsmooth.contDiffOn hab
    _ ≤ ∫⁻ t in Icc a b, C * ‖mfderiv 𝓘(ℝ) I γ t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hchain := mfderiv_comp_apply t (hf.mdifferentiableAt one_ne_zero)
        (hγ.mdifferentiableAt one_ne_zero) 1
      rw [mfderiv_eq_fderiv] at hchain
      change deriv (f ∘ γ) t = tangentModelVector
        (mfderiv I 𝓘(ℝ, F) f (γ t) (mfderiv 𝓘(ℝ) I γ t 1)) at hchain
      rw [hchain]
      exact hbound t ht _
    _ = C * pathELength I γ a b := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, pathELength_eq_lintegral_mfderiv_Icc]

theorem coordinate_path_stays_in_closedBall {f : M → F} {C r : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    (hbound : ∀ x, f x ∈ Metric.closedBall (f (γ 0)) r → ∀ v : TangentSpace I x,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f x v)‖ₑ ≤ C * ‖v‖ₑ)
    (hshort : (C : ℝ≥0∞) * pathELength I γ 0 1 < r) :
    ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) ∈ Metric.closedBall (f (γ 0)) r := by
  let A := {t : ℝ | f (γ t) ∈ Metric.closedBall (f (γ 0)) r}
  have hA : IsClosed (A ∩ Icc 0 1) :=
    ((Metric.isClosed_closedBall).preimage (hf.continuous.comp hγ.continuous)).inter isClosed_Icc
  have hzero : (0 : ℝ) ∈ A := Metric.mem_closedBall_self r.coe_nonneg
  apply hA.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hzero
  intro t ht hAt
  have hvariation := coordinate_edist_le_mul_pathELength hf hγ ht.1
    (fun u hu => hbound (γ u) (hAt hu))
  have hlength : (C : ℝ≥0∞) * pathELength I γ 0 t ≤ C * pathELength I γ 0 1 := by
    gcongr
    exact ht.2.le
  have hlt : edist (f (γ 0)) (f (γ t)) < r := hvariation.trans_lt
    (hlength.trans_lt hshort)
  have hball : f (γ t) ∈ Metric.ball (f (γ 0)) r := by
    rw [← Metric.eball_coe, Metric.mem_eball, edist_comm]
    exact hlt
  have hnhds : {u | f (γ u) ∈ Metric.ball (f (γ 0)) r} ∈ 𝓝 t :=
    (Metric.isOpen_ball.preimage (hf.continuous.comp hγ.continuous)).mem_nhds hball
  exact Filter.mem_of_superset (nhdsWithin_le_nhds hnhds)
    (fun u hu => Metric.ball_subset_closedBall hu)

theorem coordinate_edist_le_of_short_path {f : M → F} {C r : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    (hbound : ∀ x, f x ∈ Metric.closedBall (f (γ 0)) r → ∀ v : TangentSpace I x,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f x v)‖ₑ ≤ C * ‖v‖ₑ)
    (hshort : (C : ℝ≥0∞) * pathELength I γ 0 1 < r) :
    edist (f (γ 0)) (f (γ 1)) ≤ C * pathELength I γ 0 1 :=
  coordinate_edist_le_mul_pathELength hf hγ zero_le_one
    (fun t ht => hbound (γ t) (coordinate_path_stays_in_closedBall hf hγ hbound hshort t ht))

end Erdos3

end

section

namespace Erdos3

open Manifold MeasureTheory _root_.Set
open scoped Manifold ContDiff ENNReal NNReal Bundle Topology

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

theorem coordinate_edist_le_of_riemannianEDist_lt {f : M → F} {C r : ℝ≥0}
    (hC : 0 < C) (hf : ContMDiff I 𝓘(ℝ, F) 1 f) (x y : M)
    (hbound : ∀ z, f z ∈ Metric.closedBall (f x) r → ∀ v : TangentSpace I z,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f z v)‖ₑ ≤ C * ‖v‖ₑ)
    (hnear : (C : ℝ≥0∞) * riemannianEDist I x y < r) :
    edist (f x) (f y) ≤ C * riemannianEDist I x y := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hCt : (C : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  apply le_of_forall_gt
  intro q hq
  have hmin : (C : ℝ≥0∞) * riemannianEDist I x y < min q r := lt_min hq hnear
  have hinput : riemannianEDist I x y < min q r / C := by
    apply (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mpr
    simpa only [mul_comm] using hmin
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hinput zero_lt_one
  have hmul : (C : ℝ≥0∞) * pathELength I γ 0 1 < min q r := by
    simpa only [mul_comm] using
      (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mp hlen
  have hb : ∀ z, f z ∈ Metric.closedBall (f (γ 0)) r → ∀ v : TangentSpace I z,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f z v)‖ₑ ≤ C * ‖v‖ₑ := by
    simpa only [hγ0] using hbound
  have hv := coordinate_edist_le_of_short_path hf hγ hb (hmul.trans_le (min_le_right q r))
  rw [hγ0, hγ1] at hv
  exact hv.trans_lt (hmul.trans_le (min_le_left q r))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateSupNorm
namespace OAI

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def coordinateL2Norm (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

theorem coordinateL2Norm_nonneg (v : ι → ℝ) : 0 ≤ coordinateL2Norm v := Real.sqrt_nonneg _

theorem coordinateL2Norm_matrix_le (A : κ → ι → ℝ) (v : ι → ℝ) :
    coordinateL2Norm (fun k => ∑ i, A k i * v i) ≤
      Real.sqrt (∑ k, ∑ i, A k i ^ 2) * coordinateL2Norm v := by
  have h : (∑ k, (∑ i, A k i * v i) ^ 2) ≤
      (∑ k, ∑ i, A k i ^ 2) * ∑ i, v i ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A k) v)
  exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_mul
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) _)

theorem coordinateL2Norm_matrix_entry_bound (A : κ → ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ k i, |A k i| ≤ B) (v : ι → ℝ) :
    coordinateL2Norm (fun k => ∑ i, A k i * v i) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) * coordinateL2Norm v := by
  have hsum : (∑ k, ∑ i, A k i ^ 2) ≤
      (Fintype.card κ : ℝ) * Fintype.card ι * B ^ 2 := by
    calc
      (∑ k, ∑ i, A k i ^ 2) ≤ ∑ _k : κ, ∑ _i : ι, B ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq.mpr ((hA k i).trans_eq (abs_of_nonneg hB).symm)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hm : 0 ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hdim : (Fintype.card κ : ℝ) * Fintype.card ι ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) ^ 2 := by nlinarith [sq_nonneg ((Fintype.card κ : ℝ) - Fintype.card ι)]
  have hsq : B ^ 2 ≤ (B + 1) ^ 2 := by nlinarith
  have hroot : Real.sqrt (∑ k, ∑ i, A k i ^ 2) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, hsum.trans ?_⟩
    rw [mul_pow]
    exact mul_le_mul hdim hsq (sq_nonneg _) (sq_nonneg _)
  exact (coordinateL2Norm_matrix_le A v).trans
    (mul_le_mul_of_nonneg_right hroot (coordinateL2Norm_nonneg v))

end Erdos3

end

section

namespace Erdos3

theorem abs_coordinate_le_coordinateL2Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) :
    |v i| ≤ coordinateL2Norm v := by
  have hsq : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have hsum : 0 ≤ ∑ j, (v j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (v j)
  have hroot := Real.sq_sqrt hsum
  have hnonneg := coordinateL2Norm_nonneg v
  unfold coordinateL2Norm at *
  nlinarith [sq_abs (v i), abs_nonneg (v i)]

theorem norm_le_coordinateL2Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖ ≤ coordinateL2Norm v := by
  apply (pi_norm_le_iff_of_nonneg (coordinateL2Norm_nonneg v)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using abs_coordinate_le_coordinateL2Norm v i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalLiftCharacterTwist
namespace OAI

section

namespace Erdos3

theorem real_fourierChar_norm_sub_le (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ ≤
      2 * Real.pi * |a - b| := by
  have hmul : (Real.fourierChar a : ℂ) =
      (Real.fourierChar (a - b) : ℂ) * (Real.fourierChar b : ℂ) := by
    rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul, sub_add_cancel]
  calc
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ =
        ‖((Real.fourierChar (a - b) : ℂ) - 1) * (Real.fourierChar b : ℂ)‖ := by
      rw [sub_mul, one_mul, ← hmul]
    _ = ‖(Real.fourierChar (a - b) : ℂ) - 1‖ := by
      rw [norm_mul, Circle.norm_coe, mul_one]
    _ ≤ ‖2 * Real.pi * (a - b)‖ := by
      rw [Real.fourierChar_apply, mul_comm _ Complex.I]
      exact Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |a - b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_pair_coefficient_norms_le {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d : ∀ i, J i → ℂ)
    {C D : ℝ} (hD : 0 ≤ D) (hc : (∑ i, ‖c i‖) ≤ C)
    (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D) :
    (∑ p : Sigma J, ‖c p.1 * d p.1 p.2‖) ≤ C * D := by
  rw [Fintype.sum_sigma]
  simp_rw [norm_mul, ← Finset.mul_sum]
  calc
    _ ≤ ∑ i, ‖c i‖ * D := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (norm_nonneg _))
    _ = (∑ i, ‖c i‖) * D := (Finset.sum_mul _ _ _).symm
    _ ≤ C * D := mul_le_mul_of_nonneg_right hc hD

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem complex_unit_vector_resolution {K : Type*} [Fintype K] (u : K → ℂ)
    (hu : ∑ k, ‖u k‖ ^ 2 = 1) (z : ℂ) : z = ∑ k, (z * star (u k)) * u k := by
  have hunit : (∑ k, star (u k) * u k) = (1 : ℂ) := by
    calc
      _ = ∑ k, ((‖u k‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
      _ = ((∑ k, ‖u k‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_sum _ _).symm
      _ = 1 := by rw [hu, Complex.ofReal_one]
  rw [show (∑ k, (z * star (u k)) * u k) = z * ∑ k, star (u k) * u k by
    rw [Finset.mul_sum]; simp only [mul_assoc], hunit, mul_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def realPolynomialMass {I : Type*} (p : MvPolynomial I ℝ) : ℝ :=
  ∑ m ∈ p.support, |p.coeff m|

theorem realPolynomialMass_nonneg {I : Type*} (p : MvPolynomial I ℝ) : 0 ≤ realPolynomialMass p :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem realPolynomialMass_zero {I : Type*} : realPolynomialMass (0 : MvPolynomial I ℝ) = 0 := by
  simp [realPolynomialMass]

theorem realPolynomialMass_monomial {I : Type*} (m : I →₀ ℕ) (c : ℝ) :
    realPolynomialMass (MvPolynomial.monomial m c) = |c| := by
  classical
  by_cases hc : c = 0 <;> simp [realPolynomialMass, MvPolynomial.support_monomial, hc]

theorem realPolynomialMass_X {I : Type*} (i : I) :
    realPolynomialMass (MvPolynomial.X i : MvPolynomial I ℝ) = 1 := by
  simpa only [MvPolynomial.X, abs_one] using realPolynomialMass_monomial (Finsupp.single i 1) 1

theorem realPolynomialMass_eq_sum_of_support_subset {I : Type*}
    (p : MvPolynomial I ℝ) (s : Finset (I →₀ ℕ)) (hs : p.support ⊆ s) :
    realPolynomialMass p = ∑ m ∈ s, |p.coeff m| := by
  classical
  apply Finset.sum_subset hs
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]

theorem realPolynomialMass_add_le {I : Type*} (p q : MvPolynomial I ℝ) :
    realPolynomialMass (p + q) ≤ realPolynomialMass p + realPolynomialMass q := by
  classical
  rw [realPolynomialMass_eq_sum_of_support_subset (p + q) (p.support ∪ q.support)
    (MvPolynomial.support_add),
    realPolynomialMass_eq_sum_of_support_subset p (p.support ∪ q.support) Finset.subset_union_left,
    realPolynomialMass_eq_sum_of_support_subset q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun monomial _ => by
    simpa only [MvPolynomial.coeff_add] using
      abs_add_le (p.coeff monomial) (q.coeff monomial))

theorem realPolynomialMass_sum_le {I J : Type*} (s : Finset J) (p : J → MvPolynomial I ℝ) :
    realPolynomialMass (∑ j ∈ s, p j) ≤ ∑ j ∈ s, realPolynomialMass (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, realPolynomialMass_zero, le_refl]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (realPolynomialMass_add_le _ _).trans (add_le_add le_rfl ih)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realPolynomialMass_mul_le {I : Type*} (p q : MvPolynomial I ℝ) :
    realPolynomialMass (p * q) ≤ realPolynomialMass p * realPolynomialMass q := by
  classical
  have he : p * q = ∑ m ∈ p.support, ∑ n ∈ q.support,
      MvPolynomial.monomial (m + n) (p.coeff m * q.coeff n) := by
    conv_lhs => rw [p.as_sum, q.as_sum]
    simp only [Finset.sum_mul, Finset.mul_sum, MvPolynomial.monomial_mul]
    exact Finset.sum_comm
  rw [he]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ p.support, ∑ n ∈ q.support,
        realPolynomialMass (MvPolynomial.monomial (m + n) (p.coeff m * q.coeff n)) :=
      Finset.sum_le_sum (fun _ _ => realPolynomialMass_sum_le _ _)
    _ = realPolynomialMass p * realPolynomialMass q := by
      simp_rw [realPolynomialMass_monomial]
      simp only [abs_mul, realPolynomialMass,
        Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem realPolynomialMass_smul (c : ℝ) (P : MvPolynomial σ ℝ) :
    realPolynomialMass (c • P) = |c| * realPolynomialMass P := by
  classical
  by_cases hc : c = 0
  · simp [hc, realPolynomialMass_zero]
  · simp only [realPolynomialMass, support_smul_eq hc, coeff_smul,
      smul_eq_mul, abs_mul, Finset.mul_sum]

theorem realPolynomialMass_pderiv (i : σ) (P : MvPolynomial σ ℝ)
    {s : ℕ} (hP : P.totalDegree ≤ s) :
    realPolynomialMass (pderiv i P) ≤ s * realPolynomialMass P := by
  classical
  conv_lhs => rw [← P.support_sum_monomial_coeff, map_sum]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ P.support, s * |P.coeff a| := by
      apply Finset.sum_le_sum
      intro a ha
      rw [pderiv_monomial, realPolynomialMass_monomial, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (a i : ℝ) from Nat.cast_nonneg _)]
      have h : (a i : ℝ) ≤ s := by
        exact_mod_cast (monomial_le_degreeOf i ha).trans ((degreeOf_le_totalDegree P i).trans hP)
      nlinarith [abs_nonneg (P.coeff a)]
    _ = _ := by rw [realPolynomialMass, Finset.mul_sum]

theorem polynomialDerivation_eq_sum [Fintype σ]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) :
    D = ∑ i, D (X i) • pderiv i := by
  classical
  apply MvPolynomial.derivation_ext
  intro j
  change D (X j) = (Derivation.coeFnAddMonoidHom (∑ i, D (X i) • pderiv i)) (X j)
  rw [map_sum]
  simp [pderiv_X, smul_eq_mul, Pi.single_apply]

theorem realPolynomialMass_derivation [Fintype σ]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hD : ∀ i, realPolynomialMass (D (X i)) ≤ M)
    {P : MvPolynomial σ ℝ} {s : ℕ} (hP : P.totalDegree ≤ s) :
    realPolynomialMass (D P) ≤ (Fintype.card σ * M * s) * realPolynomialMass P := by
  classical
  have he : D P = ∑ i, D (X i) * pderiv i P := by
    conv_lhs => rw [polynomialDerivation_eq_sum D]
    change (Derivation.coeFnAddMonoidHom (∑ i, D (X i) • pderiv i)) P = _
    rw [map_sum]
    simp [smul_eq_mul]
  rw [he]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : σ, M * (s * realPolynomialMass P) := by
      apply Finset.sum_le_sum
      intro i _
      exact (realPolynomialMass_mul_le _ _).trans
        (mul_le_mul (hD i) (realPolynomialMass_pderiv i P hP)
          (realPolynomialMass_nonneg _) hM)
    _ = _ := by simp; ring

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem abs_aeval_le_mass_box {σ : Type*} (P : MvPolynomial σ ℝ) (x : σ → ℝ)
    {B : ℝ} {n : ℕ} (hB : 1 ≤ B) (hx : ∀ i, |x i| ≤ B) (hP : P.totalDegree ≤ n) :
    |aeval x P| ≤ realPolynomialMass P * B ^ n := by
  classical
  change |P.eval₂ (RingHom.id ℝ) x| ≤ _
  rw [eval₂_eq]
  calc
    _ ≤ ∑ a ∈ P.support, |P.coeff a * ∏ i ∈ a.support, x i ^ a i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ P.support, |P.coeff a| * B ^ n := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ = ∏ i ∈ a.support, |x i| ^ a i := by simp only [abs_pow]
        _ ≤ ∏ i ∈ a.support, B ^ a i :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hx i) _)
        _ = B ^ (a.sum fun _ m => m) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
        _ ≤ B ^ n := pow_le_pow_right₀ hB ((le_totalDegree ha).trans hP)
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

abbrev CompatibleAuxResidue (M d : ℕ) (u : ℤ) :=
  {v : Fin d // ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ (v.val : ℤ) [ZMOD (d : ℤ)]}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]

theorem realification_ker (f : V →ₗ[ℚ] W) :
    (LinearMap.ker f).baseChange ℝ = LinearMap.ker (f.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have h : Function.Exact ((LinearMap.ker f).subtype.baseChange ℝ) (f.baseChange ℝ) :=
    Module.Flat.lTensor_exact ℝ f.exact_subtype_ker_map
  exact (LinearMap.exact_iff.mp h).symm

theorem realification_mkQ_eq_zero_iff (P : Submodule ℚ V) (x : ℝ ⊗[ℚ] V) :
    P.mkQ.baseChange ℝ x = 0 ↔ x ∈ P.baseChange ℝ := by
  change x ∈ LinearMap.ker (P.mkQ.baseChange ℝ) ↔ _
  rw [← realification_ker, Submodule.ker_mkQ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
namespace OAI

section

namespace Erdos3

open Module

noncomputable def basisCoordinateMap {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]
    (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ[ℝ] M) : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  LinearMap.toContinuousLinearMap
    (f.equivFun.toLinearMap.comp (φ.comp e.equivFun.symm.toLinearMap))

@[simp] theorem basisCoordinateMap_apply {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]
    (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ[ℝ] M) (x : ι → ℝ) :
    basisCoordinateMap e f φ x = f.equivFun (φ (e.equivFun.symm x)) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]

theorem basisCoordinateMap_apply_eq_sum (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ[ℝ] M) (v : ι → ℝ) (k : κ) :
    basisCoordinateMap e f φ v k = ∑ i, f.repr (φ (e i)) k * v i := by
  rw [basisCoordinateMap_apply, Basis.equivFun_symm_apply]
  change f.repr (φ (∑ i, v i • e i)) k = _
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, mul_comm]

theorem basisCoordinateMap_L2_bound (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ[ℝ] M) (B : ℝ) (hB : 0 ≤ B)
    (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) (v : ι → ℝ) :
    coordinateL2Norm (basisCoordinateMap e f φ v) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) * coordinateL2Norm v := by
  have heq : basisCoordinateMap e f φ v = fun k => ∑ i, f.repr (φ (e i)) k * v i :=
    funext (basisCoordinateMap_apply_eq_sum e f φ v)
  rw [heq]
  exact coordinateL2Norm_matrix_entry_bound (fun k i => f.repr (φ (e i)) k) B hB hφ v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3

open scoped NNReal

def coordinateLipschitzBound (m n : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ((m : ℝ≥0) + n + 1) * (B + 1)

theorem coordinateLipschitzBound_pos (m n : ℕ) (B : ℝ≥0) :
    0 < coordinateLipschitzBound m n B := by
  unfold coordinateLipschitzBound
  positivity

theorem coordinateLipschitzBound_le_exp (m n : ℕ) (B : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp p) :
    (coordinateLipschitzBound m n B : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  have hdim : (m : ℝ) + n + 1 ≤ Real.exp (2 * p) := by
    linarith [Real.add_one_le_exp (2 * p)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hheight : (B : ℝ) + 1 ≤ Real.exp (p + 1) := by
    calc
      _ ≤ Real.exp p * 2 := by linarith [Real.one_le_exp_iff.mpr hp]
      _ ≤ Real.exp p * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
      _ = Real.exp (p + 1) := (Real.exp_add _ _).symm
  change ((m : ℝ) + n + 1) * ((B : ℝ) + 1) ≤ _
  calc
    _ ≤ Real.exp (2 * p) * Real.exp (p + 1) :=
      mul_le_mul hdim hheight (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((p + 2) ^ 2) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3

open Module

theorem coordinateL2Norm_smul {ι : Type*} [Fintype ι] (r : ℝ) (v : ι → ℝ) :
    coordinateL2Norm (r • v) = |r| * coordinateL2Norm v := by
  unfold coordinateL2Norm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PowerSubgroup
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G]

def powerSubgroup (G : Type*) [Group G] (m : ℕ) : Subgroup G :=
  Subgroup.closure (Set.range (fun g : G => g ^ m))

theorem pow_mem_powerSubgroup (g : G) (m : ℕ) : g ^ m ∈ powerSubgroup G m :=
  Subgroup.subset_closure ⟨g, rfl⟩

def subgroupPowerCover (Γ : Subgroup G) (m : ℕ) : Subgroup G :=
  (powerSubgroup Γ m).map Γ.subtype

theorem pow_mem_subgroupPowerCover (Γ : Subgroup G) {g : G} (hg : g ∈ Γ) (m : ℕ) :
    g ^ m ∈ subgroupPowerCover Γ m :=
  Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : Γ) ^ m, pow_mem_powerSubgroup _ _, rfl⟩

theorem subgroupPowerCover_le_iff (Γ Λ : Subgroup G) (m : ℕ) :
    subgroupPowerCover Γ m ≤ Λ ↔ ∀ g ∈ Γ, g ^ m ∈ Λ := by
  constructor
  · intro h g hg
    exact h (pow_mem_subgroupPowerCover Γ hg m)
  · intro h
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, rfl⟩
    exact h g g.property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CircleFejerKernel
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real
open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

def fejerPairFrequency {N : ℕ} (p : Fin N × Fin N) : ℤ :=
  (p.1.val : ℤ) - p.2.val

def fejerCoefficient (N : ℕ) (h : ℤ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun p : Fin N × Fin N =>
    fejerPairFrequency p = h).card : ℝ) / N

end
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeriodicIsometricAction
namespace OAI

section

namespace Erdos3.CircleFourier

open Function
open scoped NNReal

variable {X : Type*}

theorem realFlow_periodic (flow : ℝ → X → X)
    (hadd : ∀ r t x, flow (r + t) x = flow r (flow t x))
    (hperiod : ∀ x, flow 1 x = x) (x : X) : Periodic (fun r => flow r x) 1 := by
  intro r
  change flow (r + 1) x = flow r x
  rw [hadd, hperiod]

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeTotalDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem exponent_total_eq_zero_iff (a : ι →₀ ℕ) :
    (∑ i, a i) = 0 ↔ a = 0 := by
  classical
  constructor
  · intro h
    ext i
    have hi : a i ≤ ∑ j, a j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h] at hi
    exact Nat.eq_zero_of_le_zero hi
  · rintro rfl
    simp only [Finsupp.zero_apply, Finset.sum_const_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*}
  [Fintype ι]
  [Fintype σ]
  [LieRing L]
  [LieAlgebra ℚ L]
  {s : ℕ}
  {bound : σ → ℕ}
  (π : ι → σ)

omit [Fintype ι] [Fintype σ] in
theorem blockPermutation_symm (e : ι ≃ ι) (he : ∀ i, π (e i) = π i) :
    ∀ i, π (e.symm i) = π i := by
  intro i
  simpa only [Equiv.apply_symm_apply] using (he (e.symm i)).symm

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem realification_map {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (U : Submodule ℚ V) (f : V →ₗ[ℚ] W) :
    (U.map f).baseChange ℝ = (U.baseChange ℝ).map (f.baseChange ℝ) := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  apply congrArg (Submodule.span ℝ)
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(1 : ℝ) ⊗ₜ[ℚ] x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} (bound : σ → ℕ)

abbrev ReplicatedPermutation := ∀ i, Equiv.Perm (Fin (bound i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3

theorem one_le_ceil_exp (p : ℝ) : 1 ≤ ⌈Real.exp p⌉₊ :=
  Nat.one_le_ceil_iff.mpr (Real.exp_pos p)

theorem ceil_exp_le_exp_add_one {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := by
  have h1 : 1 ≤ Real.exp p := by simpa using Real.exp_le_exp.mpr hp
  calc
    _ ≤ Real.exp p + 1 := (Nat.ceil_lt_add_one (Real.exp_pos p).le).le
    _ ≤ 2 * Real.exp p := by linarith
    _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos p).le
    _ = Real.exp (p + 1) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCentralSeed
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def realifyFunctional (η : L →ₗ[ℚ] ℚ) : (ℝ ⊗[ℚ] L) →ₗ[ℝ] ℝ :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight
    ((Algebra.linearMap ℚ ℝ).comp η))

@[simp]
theorem realifyFunctional_tmul (η : L →ₗ[ℚ] ℚ) (r : ℝ) (v : L) :
    realifyFunctional η (r ⊗ₜ[ℚ] v) = r * (η v : ℝ) := by
  simp [realifyFunctional]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open scoped NNReal

namespace Erdos3

noncomputable def productExpBound (p : ℝ) : ℝ≥0 := ⟨Real.exp p, Real.exp_nonneg p⟩

@[simp] theorem coe_productExpBound (p : ℝ) : (productExpBound p : ℝ) = Real.exp p := rfl

def productObservableLipBudget (p : ℝ) : ℝ := p + (p ^ 2 + p + 3) ^ 2

def productNiltestBudget (p : ℝ) : ℝ :=
  (p + 2) ^ 2 + p + productObservableLipBudget p + p ^ 2 + 4

theorem productObservableLipBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ productObservableLipBudget p := by
  unfold productObservableLipBudget
  positivity

theorem productNiltestBudget_geometry {p : ℝ} (hp : 0 ≤ p) :
    (p + 2) ^ 2 ≤ productNiltestBudget p := by
  have hr := productObservableLipBudget_nonneg hp
  unfold productNiltestBudget
  nlinarith [sq_nonneg p]

theorem productNiltestBudget_observable {p : ℝ} (hp : 0 ≤ p) (m : ℕ) (hm : (m : ℝ) ≤ p) :
    2 + Real.exp p ^ m + (m : ℝ) * Real.exp (productObservableLipBudget p) * Real.exp p ^ m ≤
      Real.exp (productNiltestBudget p) := by
  let A := p + productObservableLipBudget p + p ^ 2
  have hR := productObservableLipBudget_nonneg hp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : Real.exp p ^ m ≤ Real.exp (p ^ 2) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
  have hB' : Real.exp p ^ m ≤ Real.exp A := hB.trans (Real.exp_le_exp.mpr (by dsimp [A]; linarith))
  have hK : (m : ℝ) * Real.exp (productObservableLipBudget p) * Real.exp p ^ m ≤ Real.exp A := by
    calc
      _ ≤ Real.exp p * Real.exp (productObservableLipBudget p) * Real.exp (p ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp A := by linarith [Real.one_le_exp_iff.mpr hA]
    _ ≤ Real.exp 4 * Real.exp A := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = Real.exp (4 + A) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by unfold productNiltestBudget; dsimp [A]; nlinarith [sq_nonneg (p + 2)])

end Erdos3

end

section

universe u v

namespace Erdos3

def optionLieSpace {ι : Type v} (L₀ : Type u) (L : ι → Type u) : Option ι → Type u
  | none => L₀
  | some i => L i

instance optionLieRing {ι : Type v} {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] (i : Option ι) : LieRing (optionLieSpace L₀ L i) := by
  cases i <;> dsimp [optionLieSpace] <;> infer_instance

instance optionLieAlgebra {ι : Type v} {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
    (i : Option ι) : LieAlgebra ℚ (optionLieSpace L₀ L i) := by
  cases i <;> dsimp [optionLieSpace] <;> infer_instance

def optionDimension {ι : Type v} (d₀ : ℕ) (d : ι → ℕ) : Option ι → ℕ
  | none => d₀
  | some i => d i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeEquivalenceTransitivity
namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

def BoolLieFamily (L₁ L₂ : Type u) : Bool → Type u
  | false => L₂
  | true => L₁

namespace BoolLieFamily

variable {L₁ L₂ : Type u} [LieRing L₁] [LieAlgebra ℚ L₁]
    [LieRing L₂] [LieAlgebra ℚ L₂]

instance instLieRing (b : Bool) : LieRing (BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : LieRing L₂)
  · exact (inferInstance : LieRing L₁)

instance instLieAlgebra (b : Bool) : LieAlgebra ℚ (BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : LieAlgebra ℚ L₂)
  · exact (inferInstance : LieAlgebra ℚ L₁)

variable [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₂)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂)] [T2Space (ℝ ⊗[ℚ] L₂)]

instance instTopologicalSpace (b : Bool) :
    TopologicalSpace (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₁))

instance instIsTopologicalAddGroup (b : Bool) :
    IsTopologicalAddGroup (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁))

instance instContinuousSMul (b : Bool) :
    ContinuousSMul ℝ (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁))

instance instT2Space (b : Bool) : T2Space (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₁))

end BoolLieFamily
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

noncomputable def realQuotientCoordinateMap (f : Basis ι ℚ (L ⧸ V)) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi (fun i => ((f.baseChange ℝ).coord i).comp (V.mkQ.baseChange ℝ))

@[simp] theorem realQuotientCoordinateMap_apply (f : Basis ι ℚ (L ⧸ V))
    (x : ℝ ⊗[ℚ] L) (i : ι) :
    realQuotientCoordinateMap f x i = (f.baseChange ℝ).repr (V.mkQ.baseChange ℝ x) i := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonStrideCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def commonStridePoint {I : Type*} (c : I → ℤ) (m : ℕ) (x : I → ℤ) : I → ℤ :=
  fun i => c i + (m : ℤ) * x i

def commonStrideIndex {I : Type*} (c : I → ℤ) (m : ℕ) (y : I → ℤ) : I → ℤ :=
  fun i => (y i - c i) / (m : ℤ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitGroupRelative
namespace OAI

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H] (q : G →* H) (d : H →* G)

def splitRelativePart (g : G) : G := g * (d (q g))⁻¹

theorem splitRelativePart_projection (hd : ∀ h, q (d h) = h) (g : G) :
    q (splitRelativePart q d g) = 1 := by
  simp only [splitRelativePart, map_mul, map_inv, hd, mul_inv_cancel]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s : ℕ}

def squareBasisWeight (w : ι → ℕ) : (ι ⊕ {i // 2 ≤ w i}) → ℕ :=
  Sum.elim w (fun i => w i - 1)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BufferedIntegerLift
namespace OAI

section

namespace Erdos3

noncomputable def nearestIntegerLift {m : ℕ} (x : Fin m → ℝ) : Fin m → ℤ :=
  fun i => round (x i)

theorem nearestIntegerLift_close {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    |x i - (nearestIntegerLift x i : ℝ)| ≤ 1 / 2 := abs_sub_round (x i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

def finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) :
    List J → Submodule ℚ V
  | [] => P
  | j :: js => LinearMap.ker (eta j) ⊓ finiteFrequencyKernel P eta js

theorem mem_finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    (js : List J) (v : V) :
    v ∈ finiteFrequencyKernel P eta js ↔ v ∈ P ∧ ∀ j ∈ js, eta j v = 0 := by
  induction js with
  | nil => simp [finiteFrequencyKernel]
  | cons j js ih =>
    simp only [finiteFrequencyKernel, Submodule.mem_inf, LinearMap.mem_ker, ih,
      List.forall_mem_cons]
    tauto

theorem finiteFrequencyKernel_le (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    finiteFrequencyKernel P eta js ≤ P := fun v hv => (mem_finiteFrequencyKernel P eta js v).mp hv |>.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTwistedTranslationLipschitz
namespace OAI

section

namespace Erdos3

theorem complex_mul_sub_mul_le_unit (a b c e : ℂ)
    (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖a * b - c * e‖ ≤ ‖a - c‖ + ‖b - e‖ := by
  rw [show a * b - c * e = (a - c) * b + c * (b - e) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  exact add_le_add
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (norm_nonneg (a - c)))
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (b - e)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
namespace OAI

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

noncomputable def character (r : ZMod N) : AddChar (ZMod N) ℂ :=
  AddChar.zmodAddEquiv r

@[simp] lemma character_zero (r : ZMod N) : character r 0 = 1 := by
  exact AddChar.map_zero_eq_one _

@[simp] lemma character_add (r x y : ZMod N) :
    character r (x + y) = character r x * character r y := by
  exact AddChar.map_add_eq_mul _ _ _

@[simp] lemma norm_character (r x : ZMod N) : ‖character r x‖ = 1 := by
  simp [character]

lemma character_comm (r x : ZMod N) : character r x = character x r := by
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective r
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
  change (↑(AddChar.zmod N (r : ZMod N) (x : ZMod N)) : ℂ) =
    ↑(AddChar.zmod N (x : ZMod N) (r : ZMod N))
  rw [AddChar.zmod_intCast, AddChar.zmod_intCast]
  congr 1
  ring_nf
  rfl

@[simp] lemma character_zero_index (x : ZMod N) : character 0 x = 1 := by
  rw [character_comm, character_zero]

@[simp] lemma character_add_index (r s x : ZMod N) :
    character (r + s) x = character r x * character s x := by
  rw [character_comm, character_add, character_comm x r, character_comm x s]

structure Set (N : ℕ) [NeZero N] where
  frequencies : Finset (ZMod N)
  radius : ℝ
  radius_nonneg : 0 ≤ radius

namespace Set

noncomputable def carrier (B : Set N) : Finset (ZMod N) :=
  Finset.univ.filter fun x ↦
    ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius

instance instMembershipZMod : Membership (ZMod N) (Set N) := ⟨fun B x ↦ x ∈ B.carrier⟩

@[simp] lemma mem_carrier {B : Set N} {x : ZMod N} :
    x ∈ B.carrier ↔
      ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius := by
  simp [carrier]

lemma mem_iff {B : Set N} {x : ZMod N} :
    x ∈ B ↔ ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius :=
  mem_carrier

def rank (B : Set N) : ℕ := B.frequencies.card

def dilate (ρ : ℝ) (B : Set N) : Set N where
  frequencies := B.frequencies
  radius := |ρ| * B.radius
  radius_nonneg := mul_nonneg (abs_nonneg _) B.radius_nonneg

def ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) : Set N where
  frequencies := Γ
  radius := ρ
  radius_nonneg := hρ

def meet (B C : Set N) : Set N where
  frequencies := B.frequencies ∪ C.frequencies
  radius := min B.radius C.radius
  radius_nonneg := le_min B.radius_nonneg C.radius_nonneg

@[simp] lemma frequencies_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).frequencies = Γ := rfl

@[simp] lemma radius_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).radius = ρ := rfl

@[simp] lemma rank_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).rank = Γ.card := rfl

@[simp] lemma frequencies_meet (B C : Set N) :
    (B.meet C).frequencies = B.frequencies ∪ C.frequencies := rfl

@[simp] lemma radius_meet (B C : Set N) :
    (B.meet C).radius = min B.radius C.radius := rfl

@[simp] lemma frequencies_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).frequencies = B.frequencies := rfl

@[simp] lemma radius_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).radius = |ρ| * B.radius := rfl

@[simp] lemma rank_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).rank = B.rank := rfl

@[simp] lemma zero_mem (B : Set N) : (0 : ZMod N) ∈ B := by
  rw [mem_iff]
  intro r hr
  simp [B.radius_nonneg]

end Set
end CyclicBohr
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateQuotientModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  [Fintype ι]
  {s t : ℕ}
  (b : Basis ι ℚ L)
  (w : ι → ℕ)
  (I : LieIdeal ℚ L)
  (S : Set ι)
  [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

noncomputable def quotientFinWeight : Fin (Fintype.card {i // i ∉ S}) → ℕ :=
  fun i => w ((Fintype.equivFin {i // i ∉ S}).symm i)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open Module

def Algebra (d : ℕ) := Fin d → ℚ

instance instAddCommGroupAlgebra (d : ℕ) : AddCommGroup (Algebra d) :=
  inferInstanceAs (AddCommGroup (Fin d → ℚ))

instance instModuleRatAlgebra (d : ℕ) : Module ℚ (Algebra d) :=
  inferInstanceAs (Module ℚ (Fin d → ℚ))

instance instLieRingAlgebra (d : ℕ) : LieRing (Algebra d) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (Fin d → ℚ))
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

instance instLieAlgebraRatAlgebra (d : ℕ) : LieAlgebra ℚ (Algebra d) where
  toModule := inferInstanceAs (Module ℚ (Fin d → ℚ))
  lie_smul _ _ _ := by
    change (0 : Algebra d) = _ • (0 : Algebra d)
    exact (smul_zero _).symm

theorem lie_eq_zero {d : ℕ} (x y : Algebra d) : ⁅x, y⁆ = 0 := rfl

noncomputable def basis (d : ℕ) : Basis (Fin d) ℚ (Algebra d) := by
  change Basis (Fin d) ℚ (Fin d → ℚ)
  exact Pi.basisFun ℚ (Fin d)

theorem basis_repr (d : ℕ) (x : Algebra d) (i : Fin d) : (basis d).repr x i = x i := by
  change Fin d → ℚ at x
  exact Pi.basisFun_repr ℚ (Fin d) x i

theorem basis_equivFun (d : ℕ) (x : Algebra d) : (basis d).equivFun x = x := by
  ext i
  exact basis_repr d x i

end Erdos3.RationalTorus

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
namespace OAI

section

namespace Erdos3

variable {I X : Type*}

def finiteSplitPoint (p : I → Prop) [DecidablePred p]
    (u : {i // p i} → X) (v : {i // ¬p i} → X) : I → X :=
  fun i => if h : p i then u ⟨i, h⟩ else v ⟨i, h⟩

theorem finiteSplitPoint_fixed (p : I → Prop) [DecidablePred p]
    (u : {i // p i} → X) (v : {i // ¬p i} → X) (i : {i // p i}) :
    finiteSplitPoint p u v i = u i := by
  simp only [finiteSplitPoint, dif_pos i.property]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

def productCoordinateMix (S : Finset I) (x y : ∀ i, X i) : ∀ i, X i :=
  fun i => if i ∈ S then x i else y i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterSlots

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {d : ℕ} {w : Fin d → ℕ}

noncomputable def parameterSubstitution (f : σ → MvPolynomial τ ℝ) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => aeval (fun b => X (Sum.inl b)) (f a)) (fun j => X (Sum.inr j))

end WeightedParameterSlots

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PivotAnnihilatorFrequencyCode
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

def frequencyCodeKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    {D : ℕ} (code : Fin D → Option J) : Submodule ℚ V :=
  finiteFrequencyKernel P (fun i => (code i).elim 0 eta) (List.finRange D)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

abbrev ProductCylinder {ι : Type*} (X : ι → Type*) := Σ S : Finset ι, ∀ i : S, X i.val

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

def assignment (c : ProductCylinder X) (base : ∀ i, X i) : ∀ i, X i :=
  fun i => if hi : i ∈ c.1 then c.2 ⟨i, hi⟩ else base i

end ProductCylinder

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGraphSmallDifference
namespace OAI

section

namespace Finset
open scoped _root_.Finset

variable {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]

def addEnergy' (s t : Finset G) : ℚ≥0 :=
  #{x ∈ ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 + x.2.1 = x.1.2 + x.2.2} / Fintype.card G ^ 3

end Finset

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPatternPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev OrderedRegularityBudget (r : ℕ) := Fin r → ℕ

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueEventOrDescent
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

def residuePairStep {I : Type*} (J : I → ℕ) (flag : Bool) : I → ℕ :=
  if flag then J else fun _ => 1

def residuePairValue {I : Type*} (u v : I → ℤ) (flag : Bool) : I → ℤ :=
  if flag then v else u

end Erdos3

end

end OAI
end


