-- Prove2me | Definitions.Def_OAIE3v2B077
-- name    : OAIE3v2B077
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:19:55.979935+00:00
-- url     : https://prove2.me/theorems/7125806c-6b62-43dd-8143-8c962ef5587b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 78 of 311
-- statement:
--   Definitions bundle 78 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B041`, `OAIE3v2B042`, `OAIE3v2B044`, `OAIE3v2B045`, `OAIE3v2B046`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B050`, `OAIE3v2B054`, `OAIE3v2B055`, `OAIE3v2B056` of this split.
--
--   Modules: `Dynamics/IntervalSplitBudget.lean`, `Dynamics/MarkedEvaluationHeightBudget.lean`, `Dynamics/NativeHorizontalLiftBudget.lean`, `Dynamics/SymmetricUnitBudget.lean`, `Estimates/AmbientImageExtension.lean`, `Estimates/AnchoredReflectedFamily.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/BoundedNativeDependentApproximations.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/FamilyDerivativeCorrelation.lean`, `Estimates/HigherResidualRowDifferences.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/NativeCoveredCommonFactorization.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/TailReflectionInduction.lean`, `Estimates/UnitVerticalMeanRowCorrelation.lean`, `Fourier/NativeMixedFourierProfiles.lean`, `Fourier/QuadraticFrequencyCoordinates.lean`, `Fourier/RealQuarterTorusExtension.lean`, `Fourier/RectangularGridCharacter.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/FiniteChoiceLeafCoordinates.lean`, `Geometry/NativeCoordinateErrorReduction.lean`, `Geometry/NativeCoordinateEstimates.lean`, `Geometry/NativeMixedCoordinateSlices.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Lattices/NativeIntegerDivision.lean`, `Linear/CommonCoefficientBasisBudget.lean`, `Linear/FurstenbergWeissProjection.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/RealSparseFourProjection.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B041
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B046
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B050
import Definitions.Def_OAIE3v2B054
import Definitions.Def_OAIE3v2B055
import Definitions.Def_OAIE3v2B056

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem norm_derivativeCorrelation_le (f u : H → ℂ) {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖u x‖ ≤ B) (h : H) :
    ‖finiteCorrelation Finset.univ
      (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ≤ B ^ 2 := by
  apply norm_finiteCorrelation_le Finset.univ_nonempty
  · intro x _
    simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
      mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · intro x _
    have hB : 0 ≤ B := (norm_nonneg (u x)).trans (hu x)
    simpa only [multiplicativeDerivative, norm_mul, norm_star, pow_two] using
      mul_le_mul (hu x) (hu (x + h)) (norm_nonneg _) hB

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def conjugationCoord (g : NilpotentLieBCHGroup L s hnil) (x : L) : L :=
  (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators NNReal

theorem norm_character_real_sub_one_le (r : ℝ) :
    ‖CircleFourier.character (r : CircleFourier.Circle) - 1‖ ≤
      (CircleFourier.characterLipConstant : ℝ) * |r| := by
  apply (CircleFourier.norm_character_sub_one_le _).trans
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using
      (show ‖(r : CircleFourier.Circle)‖ ≤ ‖r‖ from QuotientAddGroup.norm_mk_le_norm))
    (by positivity : 0 ≤ 2 * Real.pi)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

namespace Erdos3

variable {G : Type*} [AddCommGroup G]

theorem cubeProduct_norm_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hs : List G) (x : G) : ‖cubeProduct f hs x‖ ≤ 1 := by
  induction hs generalizing x with
  | nil => simpa only [cubeProduct_nil] using hf x
  | cons h hs ih =>
    rw [cubeProduct_cons, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ih x)).trans (ih (x + h))

theorem cubeProduct_mul (f g : G → ℂ) (hs : List G) (x : G) :
    cubeProduct (fun y => f y * g y) hs x = cubeProduct f hs x * cubeProduct g hs x := by
  induction hs generalizing x with
  | nil => simp only [cubeProduct_nil]
  | cons h hs ih =>
    simp only [cubeProduct_cons, ih, star_mul]
    ring

theorem cubeProduct_star (f : G → ℂ) (hs : List G) (x : G) :
    cubeProduct (fun y => star (f y)) hs x = star (cubeProduct f hs x) := by
  induction hs generalizing x with
  | nil => simp only [cubeProduct_nil]
  | cons h hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    exact mul_comm _ _

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

theorem lieTreeLength_relabel (f : I → J) (a : FreeMagma I) :
    (FreeMagma.map f a).length = a.length := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change (FreeMagma.map f a).length + (FreeMagma.map f b).length = _
    exact congrArg₂ (· + ·) ha hb

instance lieTreeOccurrencesFintype (a : FreeMagma I) : Fintype (LieTreeOccurrences a) := by
  induction a using FreeMagma.rec with
  | of i => exact inferInstanceAs (Fintype Unit)
  | mul a b ha hb =>
    let := ha
    let := hb
    exact inferInstanceAs (Fintype (LieTreeOccurrences a ⊕ LieTreeOccurrences b))

def lieTreeOccurrenceTree : (a : FreeMagma I) → FreeMagma (LieTreeOccurrences a)
  | .of _ => .of ()
  | .mul a b => .mul (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a))
    (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b))

theorem lieTreeOccurrenceTree_length (a : FreeMagma I) :
    (lieTreeOccurrenceTree a).length = a.length := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)).length +
      (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b)).length = _
    rw [lieTreeLength_relabel, lieTreeLength_relabel]
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeOccurrenceTree_support (a : FreeMagma I) :
    lieTreeSupport (lieTreeOccurrenceTree a) = Set.univ := by
  induction a using FreeMagma.rec with
  | of i =>
    ext j
    cases j
    exact iff_of_true rfl trivial
  | mul a b ha hb =>
    change lieTreeSupport (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)) ∪
      lieTreeSupport (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b)) = _
    rw [lieTreeSupport_relabel, lieTreeSupport_relabel, ha, hb]
    ext j
    constructor
    · intro _; trivial
    · intro _
      cases j with
      | inl j => exact Or.inl ⟨j, Set.mem_univ _, rfl⟩
      | inr j => exact Or.inr ⟨j, Set.mem_univ _, rfl⟩

end Erdos3

end

section

namespace Erdos3

variable {I : Type*}

theorem lieTreeMarkedCount_le_length (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMarkedCount marked a ≤ a.length := by
  induction a using FreeMagma.rec with
  | of i => simp only [lieTreeMarkedCount_leaf, FreeMagma.length]; split <;> omega
  | mul a b ha hb => exact Nat.add_le_add ha hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FurstenbergWeissProjection
namespace OAI

section

namespace Erdos3

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem fourSparseFirstProjection_map (f : V →ₗ[ℚ] W) (hf : Function.Injective f)
    (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) :
    fourSparseFirstProjection (J.map (fourLinearMap f)) S = (fourSparseFirstProjection J S).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, ⟨v, hv, rfl⟩, hzero, hS⟩ := (mem_fourSparseFirstProjection _ _ _).mp hy
    refine ⟨v 0, (mem_fourSparseFirstProjection _ _ _).mpr ⟨v, hv, rfl, ?_⟩, hzero⟩
    intro k hk
    exact hf ((hS k hk).trans (map_zero f).symm)
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, hv, rfl, hS⟩ := (mem_fourSparseFirstProjection _ _ _).mp hx
    refine (mem_fourSparseFirstProjection _ _ _).mpr
      ⟨fourLinearMap f v, ⟨v, hv, rfl⟩, rfl, ?_⟩
    intro k hk
    change f (v k) = 0
    rw [hS k hk, map_zero]

theorem fourDependentProjection_map (f : V →ₗ[ℚ] W) (hf : Function.Injective f)
    (J : Submodule ℚ (Fin 4 → V)) :
    fourDependentProjection (J.map (fourLinearMap f)) = (fourDependentProjection J).map f := by
  rw [fourDependentProjection, fourSparseFirstProjection_map f hf, fourSparseFirstProjection_map f hf]
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have hxz : x = z := hf (hxy.trans hzy.symm)
    exact ⟨x, ⟨hx, hxz.symm ▸ hz⟩, hxy⟩
  · rintro ⟨x, ⟨hx, hz⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hz, rfl⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmbientImageExtension
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {H G E : Type*} [Group H] [Group G] [MetricSpace H] [MetricSpace G]
  [IsIsometricSMul Hᵐᵒᵖ H] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]
  [NormedAddCommGroup E]

theorem cosetImage_local_lifts (φ : H →* G) (Λ : Subgroup G)
    (hΛ : IsClosed (Λ : Set G)) (S : Set G) (K δ ε : ℝ≥0)
    (hrep : ∀ y : CosetImage φ Λ, ∃ x : H, projectToCosetImage φ Λ x = y ∧ φ x ∈ S)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, ∀ γ ∈ Λ, dist a (b * γ) < ε → γ ∈ φ.range)
    (hlift : ∀ g ∈ φ.range, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∀ y z : CosetImage φ Λ, dist y z < min δ ε / 2 →
      ∃ x x' : H, projectToCosetImage φ Λ x = y ∧ projectToCosetImage φ Λ x' = z ∧
        dist x x' ≤ (2 * K) * dist y z := by
  let := rightCosetMetricSpace Λ hΛ
  intro y z hyz
  obtain ⟨x, hx, hxS⟩ := hrep y
  obtain ⟨w, hw, hwS⟩ := hrep z
  by_cases heq : y = z
  · refine ⟨x, x, hx, hx.trans heq, ?_⟩
    simp only [heq, dist_self, mul_zero, le_refl]
  have hd : 0 < dist y z := dist_pos.mpr heq
  have hqx : (QuotientGroup.mk (φ x) : G ⧸ Λ) = y.val := congrArg Subtype.val hx
  have hqw : (QuotientGroup.mk (φ w) : G ⧸ Λ) = z.val := congrArg Subtype.val hw
  obtain ⟨b, hb, hbq⟩ := rightCosetMetricSpace_exists_lift Λ hΛ (φ x) (2 * dist y z) z.val (by
    rw [hqx, dist_comm]
    change dist y z < 2 * dist y z
    linarith)
  let γ := (φ w)⁻¹ * b
  have hγ : γ ∈ Λ := QuotientGroup.eq.mp (hqw.trans hbq.symm)
  have hprod : φ w * γ = b := by simp only [γ, mul_inv_cancel_left]
  have hγrange : γ ∈ φ.range := by
    apply hgap (φ x) hxS (φ w) hwS γ hγ
    rw [hprod, dist_comm]
    have hmin : (min δ ε : ℝ≥0) ≤ ε := min_le_right _ _
    have hminr : ((min δ ε : ℝ≥0) : ℝ) ≤ ε := hmin
    linarith
  have hbrange : b ∈ φ.range := by
    rw [← hprod]
    exact φ.range.mul_mem ⟨w, rfl⟩ hγrange
  let g := b * (φ x)⁻¹
  have hgrange : g ∈ φ.range := φ.range.mul_mem hbrange (φ.range.inv_mem ⟨x, rfl⟩)
  have hgdist : dist 1 g = dist b (φ x) := by
    simpa only [g, mul_inv_cancel, dist_comm] using dist_mul_right (φ x) b (φ x)⁻¹
  have hgnear : dist 1 g < δ := by
    rw [hgdist]
    have hmin : (min δ ε : ℝ≥0) ≤ δ := min_le_left _ _
    have hminr : ((min δ ε : ℝ≥0) : ℝ) ≤ δ := hmin
    linarith
  obtain ⟨u, hu, hudist⟩ := hlift g hgrange hgnear
  refine ⟨x, u * x, hx, ?_, ?_⟩
  · apply Subtype.ext
    change (QuotientGroup.mk (φ (u * x)) : G ⧸ Λ) = z.val
    rw [map_mul, hu]
    simpa only [g, inv_mul_cancel_right] using hbq
  · have hdist : dist x (u * x) = dist 1 u := by
      simpa only [one_mul] using dist_mul_right (1 : H) u x
    rw [hdist]
    calc
      dist 1 u ≤ (K : ℝ) * dist 1 g := hudist
      _ ≤ K * (2 * dist y z) := mul_le_mul_of_nonneg_left (by rw [hgdist]; exact hb.le) K.coe_nonneg
      _ = (2 * K) * dist y z := by ring

theorem exists_lipschitz_cosetImage_reconstruction (φ : H →* G)
    (Γ : Subgroup H) (Λ : Subgroup G) (hΛ : IsClosed (Λ : Set G))
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → E)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x)
    (S : Set G) (L K B δ ε : ℝ≥0) (hδ : 0 < δ) (hε : 0 < ε)
    (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hrep : ∀ y : CosetImage φ Λ, ∃ x : H, projectToCosetImage φ Λ x = y ∧ φ x ∈ S)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, ∀ γ ∈ Λ, dist a (b * γ) < ε → γ ∈ φ.range)
    (hlift : ∀ g ∈ φ.range, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∃ F : CosetImage φ Λ → E,
      (∀ x, F (projectToCosetImage φ Λ x) = f x) ∧
      LipschitzWith (max (L * (2 * K)) (2 * B / (min δ ε / 2))) F ∧ ∀ y, ‖F y‖ ≤ B := by
  let := rightCosetMetricSpace Λ hΛ
  obtain ⟨F, hF, _⟩ := exists_unique_cosetImage_reconstruction φ Γ Λ hcover f hker hΓ
  have hπ := projectToCosetImage_surjective φ Λ
  refine ⟨F, hF, ?_, reconstruction_norm_le _ hπ f F hF hbound⟩
  apply lipschitz_reconstruction_of_local_lifts (projectToCosetImage φ Λ) hπ f F hF
    L (2 * K) B (min δ ε / 2) (by positivity) hf hbound
  exact cosetImage_local_lifts φ Λ hΛ S K δ ε hrep hgap hlift

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {H G : Type*} [Group H] [Group G] [MetricSpace H] [MetricSpace G]
  [IsIsometricSMul Hᵐᵒᵖ H] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem exists_ambient_image_reconstruction (φ : H →* G)
    (Γ : Subgroup H) (Λ : Subgroup G) (hΛ : IsClosed (Λ : Set G))
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → ℂ)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x)
    (S : Set G) (L K B δ ε : ℝ≥0) (hδ : 0 < δ) (hε : 0 < ε)
    (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hrep : ∀ y : CosetImage φ Λ, ∃ x : H, projectToCosetImage φ Λ x = y ∧ φ x ∈ S)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, ∀ γ ∈ Λ, dist a (b * γ) < ε → γ ∈ φ.range)
    (hlift : ∀ g ∈ φ.range, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∃ F : G ⧸ Λ → ℂ,
      (∀ x, F (QuotientGroup.mk (φ x)) = f x) ∧
      LipschitzWith (2 * max (L * (2 * K)) (2 * B / (min δ ε / 2))) F ∧
      ∀ y, ‖F y‖ ≤ 2 * B := by
  let := rightCosetMetricSpace Λ hΛ
  obtain ⟨F, hF, hLip, hb⟩ := exists_lipschitz_cosetImage_reconstruction φ Γ Λ hΛ hcover
    f hker hΓ S L K B δ ε hδ hε hf hbound hrep hgap hlift
  obtain ⟨u, hu, heq, hub⟩ := exists_complex_extension_from_subset (CosetImage φ Λ) F
    (max (L * (2 * K)) (2 * B / (min δ ε / 2))) B hLip hb
  exact ⟨u, fun x => (heq (projectToCosetImage φ Λ x)).trans (hF x), hu, hub⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def boxCornerProduct {n : ℕ} {X : Type*} (F : (Fin n → X) → ℂ) (u v : Fin n → X) : ℂ :=
  ∏ ω : Fin n → Bool, conjugationPower (booleanWeight ω) (F (boxCorner u v ω))

theorem boxCornerProduct_mul {n : ℕ} {X : Type*} (F G : (Fin n → X) → ℂ) (u v : Fin n → X) :
    boxCornerProduct (fun x => F x * G x) u v = boxCornerProduct F u v * boxCornerProduct G u v := by
  simp only [boxCornerProduct, map_mul, Finset.prod_mul_distrib]

theorem boxCornerProduct_star {n : ℕ} {X : Type*} (F : (Fin n → X) → ℂ) (u v : Fin n → X) :
    boxCornerProduct (fun x => star (F x)) u v = star (boxCornerProduct F u v) := by
  simp only [boxCornerProduct, conjugationPower_star, star_prod]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def boxCornerAnchor {n : ℕ} {X : Type*}
    (F : (Fin n → X) → ℂ) (a z : Fin n → X) : ℂ := by
  classical
  exact ∏ ω ∈ (Finset.univ.erase (fun _ : Fin n => false)),
    conjugationPower (booleanWeight ω) (F (boxCorner z a ω))

theorem boxCornerProduct_eq_mul_anchor {n : ℕ} {X : Type*}
    (F : (Fin n → X) → ℂ) (z a : Fin n → X) :
    boxCornerProduct F z a = F z * boxCornerAnchor F a z := by
  classical
  have h := (Finset.mul_prod_erase Finset.univ
    (fun ω => conjugationPower (booleanWeight ω) (F (boxCorner z a ω)))
    (Finset.mem_univ (fun _ : Fin n => false))).symm
  have hz : boxCorner z a (fun _ => false) = z := rfl
  simpa [boxCornerProduct, boxCornerAnchor, booleanWeight, hz, conjugationPower] using h

theorem boxCornerAnchor_prod_equiv {n m : ℕ} {X : Type*}
    (e : Fin m ≃ (Finset.univ.erase (fun _ : Fin n => false)))
    (F : (Fin n → X) → ℂ) (a z : Fin n → X) :
    (∏ l, conjugationPower (booleanWeight (e l).val) (F (boxCorner z a (e l).val))) =
      boxCornerAnchor F a z := by
  classical
  calc
    _ = ∏ ω : (Finset.univ.erase (fun _ : Fin n => false)),
        conjugationPower (booleanWeight ω.val) (F (boxCorner z a ω.val)) :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      unfold boxCornerAnchor
      exact Finset.prod_coe_sort (Finset.univ.erase (fun _ : Fin n => false))
        (fun ω : Fin n → Bool => conjugationPower (booleanWeight ω) (F (boxCorner z a ω)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
namespace OAI

section

namespace Erdos3

theorem exists_native_horizontal_lift_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let Q := (p + a) ^ a
      let P := (Q + 3) ^ 4
      Q ≤ (p + C) ^ C ∧ separationBudget P ≤ (p + C) ^ C ∧
        (P + 2) ^ 3 + (P + 2) ^ 18 + P ≤ (p + C) ^ C ∧
        Q + s * (P + ((P + 2) ^ 3 + (P + 2) ^ 36)) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let P := (Q + 3) ^ 4
  let B := (P + 2) ^ 48 + (P + 2) ^ 24 + P + 1
  let E := (P + 2) ^ 3 + (P + 2) ^ 18 + P
  let M := Q + Polynomial.C s * (P + ((P + 2) ^ 3 + (P + 2) ^ 36))
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + B + E + M)
  refine ⟨C, hC, ?_⟩
  intro p hp Q' P'
  have hQ : 0 ≤ Q' := by dsimp only [Q']; positivity
  have hP : 0 ≤ P' := by dsimp only [P']; positivity
  have hB := separationBudget_nonneg hP
  have hE : 0 ≤ (P' + 2) ^ 3 + (P' + 2) ^ 18 + P' := by positivity
  have hM : 0 ≤ Q' + s * (P' + ((P' + 2) ^ 3 + (P' + 2) ^ 36)) := by positivity
  have hsum : Q' + separationBudget P' + ((P' + 2) ^ 3 + (P' + 2) ^ 18 + P') +
      (Q' + s * (P' + ((P' + 2) ^ 3 + (P' + 2) ^ 36))) ≤ (p + C) ^ C := by
    simpa [X, Q, P, B, E, M, Q', P', separationBudget, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hsum, hB, hE, hM],
    by linarith only [hsum, hQ, hE, hM],
    by linarith only [hsum, hQ, hB, hM], by linarith only [hsum, hQ, hB, hE]⟩

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

theorem replicatedPermutation_injective : Function.Injective (replicatedPermutation bound) := by
  intro e f h
  funext i
  apply Equiv.ext
  intro j
  have hh := congrArg (fun g : Equiv.Perm (ReplicatedIndex bound) => g ⟨i, j⟩) h
  change (⟨i, e i j⟩ : ReplicatedIndex bound) = ⟨i, f i j⟩ at hh
  exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2

theorem replicatedPermutation_card_le [Fintype σ] :
    Fintype.card (ReplicatedPermutation bound) ≤ (∑ i, bound i).factorial := by
  classical
  have h := Fintype.card_le_of_injective _ (replicatedPermutation_injective bound)
  simpa only [Fintype.card_perm, replicatedIndex_card] using h

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

def integerCubeProductWithShift {d : ℕ} (R : ℤ → ℂ) (k : Fin d → ℤ)
    (c : (Fin d → Bool) → ℤ) (n : ℤ) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (R (n + cubeShift k ω + c ω))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module

def rankQuotientFrequencyHeight (n m u H : ℕ) : ℕ :=
  (u + 1) * (rationalSolveHeight u (rankQuotientLayerHeight n m H) *
    ((n + 1) * (H * H) ^ n)) ^ u

def rankQuotientHeight (n m q u H : ℕ) : ℕ :=
  max 1 (max (rationalKernelHeight m H)
    (max (rationalLieStructureHeight n (max H (max (rationalKernelHeight m H)
      (rationalSolveHeight q (rationalKernelHeight m H)))))
      (max (rankQuotientLayerHeight n m H) (rankQuotientFrequencyHeight n m u H))))

end Erdos3

end

section

namespace Erdos3

theorem rankQuotientHeight_le_exp (n m q u H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hu : (u : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rankQuotientHeight n m q u H : ℝ) ≤ Real.exp ((p + 2) ^ 424) := by
  let Q := rationalKernelHeight m H
  let E := rankQuotientLayerHeight n m H
  let V := (n + 1) * (H * H) ^ n
  let P := (p + 2) ^ 51
  have hpP : p ≤ P := le_power_budget hp (by decide : 1 ≤ 51)
  have hP : 0 ≤ P := hp.trans hpP
  have hbase : 1 ≤ p + 2 := by linarith
  have hQ : (Q : ℝ) ≤ Real.exp ((p + 2) ^ 7) := rationalKernelHeight_le_budget m H hp hm hH
  have hH7 : (H : ℝ) ≤ Real.exp ((p + 2) ^ 7) :=
    hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide)))
  have hprod {A B : ℕ} (hA : (A : ℝ) ≤ Real.exp ((p + 2) ^ 7))
      (hB : (B : ℝ) ≤ Real.exp ((p + 2) ^ 7)) :
      ((A * B : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 8) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 7) * Real.exp ((p + 2) ^ 7) :=
        mul_le_mul hA hB (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * (p + 2) ^ 7) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        calc
          _ ≤ (p + 2) * (p + 2) ^ 7 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by ring)
  have hE10 : (E : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
    exact rational_sum_cost_le_exp n (H * Q) hp 8 1 (hprod hH7 hQ)
      (by simpa only [pow_one] using hn.trans (show p ≤ p + 2 by linarith))
  have hV10 : (V : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
    exact rational_sum_cost_le_exp n (H * H) hp 8 1 (hprod hH7 hH7)
      (by simpa only [pow_one] using hn.trans (show p ≤ p + 2 by linarith))
  have hEP : (E : ℝ) ≤ Real.exp P :=
    hE10.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 10 ≤ 51)))
  have hVP : (V : ℝ) ≤ Real.exp P :=
    hV10.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 10 ≤ 51)))
  have hfreq0 := embedding_coordinate_height_budget u u E V hP
    (hu.trans hpP) (hu.trans hpP) hEP hVP
  have hfreq : (rankQuotientFrequencyHeight n m u H : ℝ) ≤ Real.exp ((p + 2) ^ 424) :=
    exponential_budget_comp hp hP 51 8 le_rfl hfreq0
  have h51 : P ≤ (p + 2) ^ 424 := pow_le_pow_right₀ hbase (by decide : 51 ≤ 424)
  have hstructure := rationalLieQuotientStructureHeight_le_exp n m q H hp hn hm hq hH
  simp only [rankQuotientHeight, Nat.cast_max, Nat.cast_one]
  refine max_le (Real.one_le_exp (by positivity)) (max_le ?_ (max_le ?_ (max_le ?_ hfreq)))
  · exact hQ.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 7 ≤ 424)))
  · exact hstructure.trans (Real.exp_le_exp.mpr h51)
  · exact hEP.trans (Real.exp_le_exp.mpr h51)

theorem dependentQuotientHeight_le_exp (s n m q u H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hu : (u : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rankQuotientHeight n m q u (lieTreeHeight n H s) : ℝ) ≤
      Real.exp ((p + 2) ^ ((6 * s + 4) * 424)) := by
  let P := (p + 2) ^ (6 * s + 2)
  have hpP : p ≤ P := le_power_budget hp (by omega : 1 ≤ 6 * s + 2)
  have hP : 0 ≤ P := hp.trans hpP
  have h := rankQuotientHeight_le_exp n m q u (lieTreeHeight n H s) hP
    (hn.trans hpP) (hm.trans hpP) (hq.trans hpP) (hu.trans hpP)
    (lieTreeHeight_le_exp n H s hp hn hH)
  have hc := exponential_budget_comp hp hP (6 * s + 2) 424 le_rfl h
  simpa only [show 6 * s + 2 + 2 = 6 * s + 4 by omega] using hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
namespace OAI

section

namespace Erdos3

open Module

noncomputable def properCyclicCoordinateBound (r : ℕ) (δ : ℝ) : ℝ :=
  (r : ℝ) * r.factorial * properCyclicKernelBasisBound r δ ^ (r - 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3

noncomputable def halvingPolynomial {σ : Type*} (r : σ → ℤ) (i : σ) : MvPolynomial σ ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) * (MvPolynomial.X i - MvPolynomial.C (r i : ℚ))

theorem halvingPolynomial_eval {σ : Type*} (r x : σ → ℤ)
    (hr : ∀ i, x i % 2 = r i) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (halvingPolynomial r i) =
      ((x i / 2 : ℤ) : ℚ) := by
  have hi : x i = 2 * (x i / 2) + r i := by
    have h := hr i
    omega
  have hiq : (x i : ℚ) = 2 * ((x i / 2 : ℤ) : ℚ) + (r i : ℚ) := by exact_mod_cast hi
  simp only [halvingPolynomial, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  change (1 / 2 : ℚ) * ((x i : ℚ) - (r i : ℚ)) = ((x i / 2 : ℤ) : ℚ)
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SymmetricUnitBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem symmetricUnitBudget_bounds (m n : ℕ) (K : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) :
    ((n ^ m * (m * m + 1) : ℕ) : ℝ) ≤ Real.exp (symmetricUnitBudget m p) ∧
      (symmetricUnitFamilyLip m n K : ℝ) ≤ Real.exp (symmetricUnitBudget m p) := by
  let D := ⌈2 / momentLowerConstant m⌉₊
  let B := momentWeightBound m
  have hc := momentLowerConstant_pos m
  have hnplus : (n + 1 : ℝ) ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hexp := Real.one_le_exp hp
    nlinarith
  have hnpow : (n : ℝ) ^ m ≤ Real.exp ((m : ℝ) * p) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg n) hn m
  have hnpowplus : (n + 1 : ℝ) ^ m ≤ Real.exp ((m : ℝ) * (p + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hnplus m
  have hd : 2 / momentLowerConstant m ≤ Real.exp D :=
    (Nat.le_ceil _).trans (by linarith [Real.add_one_le_exp (D : ℝ)])
  have hout : (n : ℝ) ^ m * (m * m + 1) + 1 ≤ Real.exp ((m : ℝ) * p + (m * m + 2)) := by
    rw [Real.exp_add]
    have hcoef : (m * m + 2 : ℝ) ≤ Real.exp (m * m + 2 : ℝ) := by
      linarith [Real.add_one_le_exp (m * m + 2 : ℝ)]
    have hmul := mul_le_mul_of_nonneg_right hnpow (by positivity : (0 : ℝ) ≤ m * m + 1)
    have heone := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg m) hp)
    nlinarith
  have hradius : 2 / (symmetricEvaluationRadius m n : ℝ) ≤
      Real.exp ((D : ℝ) + m * (p + 1)) := by
    change 2 / (momentLowerConstant m / (n + 1 : ℝ) ^ m) ≤ _
    rw [Real.exp_add]
    calc
      _ = (2 / momentLowerConstant m) * (n + 1 : ℝ) ^ m := by field_simp
      _ ≤ _ := mul_le_mul hd hnpowplus (by positivity) (Real.exp_pos _).le
  have hB : (B : ℝ) ≤ Real.exp B := by linarith [Real.add_one_le_exp (B : ℝ)]
  have hBpow : (B : ℝ) ^ (m + 1) ≤ Real.exp ((m + 1 : ℝ) * B) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg B) hB (m + 1)
    rw [← Real.exp_nat_mul] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hraw : (symmetricEvaluationLip m K : ℝ) ≤
      Real.exp ((m : ℝ) + (m + 1) * B + p) := by
    change (m : ℝ) * ((B : ℝ) * K) * (B : ℝ) ^ m ≤ _
    rw [Real.exp_add, Real.exp_add]
    calc
      _ = (m : ℝ) * (B : ℝ) ^ (m + 1) * K := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul
        (by linarith [Real.add_one_le_exp (m : ℝ)]) hBpow (by positivity) (Real.exp_pos _).le)
        hK K.coe_nonneg (by positivity)
  have htotal : (symmetricUnitFamilyLip m n K : ℝ) ≤ Real.exp
      ((D : ℝ) + m * (p + 1) + (m * p + (m * m + 2)) + (m + (m + 1) * B + p)) := by
    change (2 / (symmetricEvaluationRadius m n : ℝ)) *
      (((n : ℝ) ^ m * (m * m + 1) + 1) * (symmetricEvaluationLip m K : ℝ)) ≤ _
    calc
      _ ≤ Real.exp ((D : ℝ) + m * (p + 1)) *
          (Real.exp (m * p + (m * m + 2)) * Real.exp (m + (m + 1) * B + p)) :=
        mul_le_mul hradius (mul_le_mul hout hraw (by positivity) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hbudget : (D : ℝ) + m * (p + 1) + (m * p + (m * m + 2)) +
      (m + (m + 1) * B + p) ≤ symmetricUnitBudget m p := by
    dsimp [symmetricUnitBudget, symmetricUnitConstant, D, B]
    push_cast
    nlinarith
  constructor
  · have hle : (m : ℝ) * p + (m * m + 2) ≤ symmetricUnitBudget m p := by
      dsimp [symmetricUnitBudget, symmetricUnitConstant]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) ⌈2 / momentLowerConstant m⌉₊,
        Nat.cast_nonneg (α := ℝ) (momentWeightBound m)]
    push_cast
    exact (le_add_of_nonneg_right zero_le_one).trans (hout.trans (Real.exp_le_exp.mpr hle))
  · exact htotal.trans (Real.exp_le_exp.mpr hbudget)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3

theorem squarefreeInputBudget_le_positive (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeInputBudget t p ≤ positivePolynomialInputBudget t p :=
  le_add_of_nonneg_left (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem prod_fin_succ_function {n m : ℕ} (f : (Fin (n + 1) → Fin m) → ℂ) :
    (∏ v, f v) = ∏ a : Fin m, ∏ v : Fin n → Fin m, f (Fin.cons a v) := by
  calc
    _ = ∏ a : Fin m × (Fin n → Fin m), f (Fin.cons a.1 a.2) :=
      ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin m)).prod_comp f).symm
    _ = _ := Fintype.prod_prod_type _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ I : Type*} [DecidableEq σ] {n : ℕ}

def finiteChoiceLeafInput : (l : List σ) → (Fin l.length → Fin (n + 1)) →
    ((Fin (n + 1) × σ) → ℤ) → σ → ℤ
  | [], _, x => fun j => x (0, j)
  | i :: l, v, x => finiteChoiceLeafInput l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x)

noncomputable def finiteChoiceExpansion (f : I → (σ → ℤ) → ℂ) (l : List σ)
    (a : (Fin l.length → Fin (n + 1)) → I) (x : (Fin (n + 1) × σ) → ℤ) : ℂ :=
  ∏ v : Fin l.length → Fin (n + 1), f (a v) (finiteChoiceLeafInput l v x)

theorem finiteChoiceExpansion_cons (f : I → (σ → ℤ) → ℂ) (l : List σ) (i : σ)
    (a : (Fin (i :: l).length → Fin (n + 1)) → I) (x : (Fin (n + 1) × σ) → ℤ) :
    finiteChoiceExpansion f (i :: l) a x = ∏ j : Fin (n + 1),
      finiteChoiceExpansion f l (fun v => a (Fin.cons j v)) (finiteChoiceReplaceInput i j x) := by
  simp only [finiteChoiceExpansion, List.length_cons, prod_fin_succ_function, finiteChoiceLeafInput,
    Fin.cons_zero, Fin.tail_cons]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.IntervalSplitBudget
namespace OAI

section

namespace Erdos3

theorem mixedErrorPairBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    mixedErrorPairBudget p ≤ mixedErrorPairBudget q := by
  unfold mixedErrorPairBudget productNiltestBudget productObservableLipBudget
  gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateErrorReduction
namespace OAI

section

namespace Erdos3

theorem exists_coordinate_reduction_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a ≤ (p + C) ^ C ∧
      ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C ∧
      3 * p + (p + a) ^ a + 1 ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (3 * X + Y + (Y + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hY : 0 ≤ (p + a) ^ a := by positivity
  have hZ : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hb : 3 * p + (p + a) ^ a + ((p + a) ^ a + b) ^ b + 2 ≤ (p + C) ^ C := by
    simpa [X, Y, Polynomial.eval₂_pow] using hbudget p hp
  constructor
  · linarith only [hp, hY, hZ, hb]
  constructor <;> linarith only [hp, hY, hZ, hb]

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

theorem expect_fin_two {G M : Type*} [Fintype G] [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (Fin 2 → G) → M) : (𝔼 x, F x) = 𝔼 h : G, 𝔼 n : G, F ![h, n] := by
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro h _
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro n _
  have hc (y : Fin 0 → G) : F (Fin.cons h (Fin.cons n y)) = F ![h, n] := by
    congr 1
    funext k
    fin_cases k <;> rfl
  simp only [hc, Fintype.expect_const]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateEstimates
namespace OAI

section

namespace Erdos3

noncomputable def nativeCoordinateSeparationBudget (s : ℕ) (P : ℝ) : ℝ :=
  separationBudget (nativeCoordinateInputBudget s P) + separationBudget (nativeDependentBudget s P)

noncomputable def nativeDependentDenominatorBudget (s : ℕ) (P : ℝ) : ℝ :=
  nativeDependentBudget s P + (nativeDependentBudget s P + 2) ^ 3 +
    (nativeDependentBudget s P + 2) ^ 36

noncomputable def nativeDependentSlowBudget (s : ℕ) (P : ℝ) : ℝ :=
  (nativeDependentBudget s P + 2) ^ 3 + (nativeDependentBudget s P + 2) ^ 18 +
    nativeDependentBudget s P + 1

theorem nativeCoordinateInputBudget_bounds (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    nativeCoordinateBaseBudget s P ≤ nativeCoordinateInputBudget s P ∧
      (nativeCoordinateBaseBudget s P + 2) ^ 3 + P ≤ nativeCoordinateInputBudget s P ∧
      1 + (nativeCoordinateBaseBudget s P + 2) ^ 3 + nativeCoordinateBaseBudget s P ≤
        nativeCoordinateInputBudget s P := by
  have hU := (nativeCoordinateBaseBudget_bounds s hP).1
  have hc : 0 ≤ (nativeCoordinateBaseBudget s P + 2) ^ 3 := by positivity
  unfold nativeCoordinateInputBudget
  constructor
  · linarith
  constructor <;> linarith

theorem nativeCoordinateInputBudget_nonneg (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ nativeCoordinateInputBudget s P :=
  (nativeCoordinateBaseBudget_bounds s hP).1.trans (nativeCoordinateInputBudget_bounds s hP).1

theorem nativeDependentBudget_nonneg (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ nativeDependentBudget s P := by
  have hZ := (rankDependentInputBudget_bounds (nativeCoordinateInputBudget_nonneg s hP)).1
  exact add_nonneg hZ (sparseGeneratorBudget_nonneg hZ)

theorem nativeCoordinateSeparationBudget_cutoffs (s : ℕ) {P N : ℝ} (hP : 0 ≤ P)
    (hN : Real.exp (nativeCoordinateSeparationBudget s P) ≤ N) :
    Real.exp (separationBudget (nativeCoordinateInputBudget s P)) ≤ N ∧
      Real.exp (separationBudget (nativeDependentBudget s P)) ≤ N := by
  have h₁ := separationBudget_nonneg (nativeCoordinateInputBudget_nonneg s hP)
  have h₂ := separationBudget_nonneg (nativeDependentBudget_nonneg s hP)
  constructor
  · exact (Real.exp_le_exp.mpr (le_add_of_nonneg_right h₂)).trans hN
  · exact (Real.exp_le_exp.mpr (le_add_of_nonneg_left h₁)).trans hN

theorem nativeDependentSlowBudget_bound (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    Real.exp (nativeDependentBudget s P) +
        Real.exp ((nativeDependentBudget s P + 2) ^ 3 + (nativeDependentBudget s P + 2) ^ 18 +
          nativeDependentBudget s P) ≤ Real.exp (nativeDependentSlowBudget s P) := by
  let Q := nativeDependentBudget s P
  let L := (Q + 2) ^ 3 + (Q + 2) ^ 18 + Q
  have hQ : 0 ≤ Q := nativeDependentBudget_nonneg s hP
  have hQL : Q ≤ L := by
    have h₁ : 0 ≤ (Q + 2) ^ 3 := by positivity
    have h₂ : 0 ≤ (Q + 2) ^ 18 := by positivity
    dsimp only [L]
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    Real.exp Q + Real.exp L ≤ 2 * Real.exp L := by linarith [Real.exp_le_exp.mpr hQL]
    _ ≤ Real.exp 1 * Real.exp L := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (L + 1) := (mul_comm _ _).trans (Real.exp_add L 1).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealSparseFourProjection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {ι : Type*} [Fintype ι]

theorem realRationalCoordinateSpan_inf (U V : Submodule ℚ (ι → ℚ)) :
    realRationalCoordinateSpan (U ⊓ V) =
      realRationalCoordinateSpan U ⊓ realRationalCoordinateSpan V := by
  unfold realRationalCoordinateSpan
  rw [realification_inf]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hv⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hv, rfl⟩⟩
  · rintro ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have hxz : x = z := realRationalCoordinateEquiv.injective (hxy.trans hzy.symm)
    exact ⟨x, ⟨hx, hxz.symm ▸ hz⟩, hxy⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_simultaneous_four_point_anchors (T : Finset (G × G × G)) {δ : ℝ}
    (hδ : 0 < δ) (hsize : δ * (Fintype.card G : ℝ) ^ 3 ≤ T.card) :
    ∃ (a b c d : G) (S : Finset G), S.Nonempty ∧
      δ ^ 2 * Fintype.card G ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, (b - h, b, a) ∈ T ∧ (c - d, h + (c - d), c) ∈ T := by
  classical
  let w (t : G × G × G) : ℝ := if t ∈ T then 1 else 0
  let f (u : G × G) (h : G) := w (u.2 - h, u.2, u.1)
  let g (u : G × G) (h : G) := w (u.1 - u.2, h + (u.1 - u.2), u.1)
  have hmarginal (h : G) : (𝔼 u, f u h) = 𝔼 u, g u h := by
    apply Fintype.expect_equiv (fourSparseAnchorChange h)
    intro u
    change w (u.2 - h, u.2, u.1) =
      w (u.1 - (u.1 - u.2 + h), h + (u.1 - (u.1 - u.2 + h)), u.1)
    congr 1
    apply Prod.ext
    · abel_nf
    · apply Prod.ext
      · abel_nf
      · rfl
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hmean : δ ≤ 𝔼 h, 𝔼 u, f u h := by
    have htotal : δ ≤ 𝔼 t, w t := by
      rw [Fintype.expect_eq_sum_div_card]
      have hsum : (∑ t, w t) = (T.card : ℝ) := by simp [w]
      rw [hsum]
      have hcard : (Fintype.card (G × G × G) : ℝ) = (Fintype.card G : ℝ) ^ 3 := by
        simp only [Fintype.card_prod, Nat.cast_mul]
        ring
      rw [hcard]
      exact (le_div_iff₀ (by positivity)).mpr hsize
    have he : (𝔼 u : (G × G) × G, f u.1 u.2) = 𝔼 t, w t := by
      apply Fintype.expect_equiv (fourSparse12Equiv G).symm
      intro u
      rfl
    have hsplit : (𝔼 u : (G × G) × G, f u.1 u.2) = 𝔼 u, 𝔼 h, f u h := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (G × G)) (Finset.univ : Finset G) f)
    rw [Finset.expect_comm, ← hsplit, he]
    exact htotal
  obtain ⟨⟨a, b⟩, ⟨c, d⟩, hpair⟩ :=
    exists_common_slice_of_equal_marginals f g hδ.le hmarginal hmean
  let S := Finset.univ.filter (fun h => (b - h, b, a) ∈ T ∧ (c - d, h + (c - d), c) ∈ T)
  have hind (h : G) : f (a, b) h * g (c, d) h = if h ∈ S then 1 else 0 := by
    simp only [f, g, w, S, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp_all
  have hSsize : δ ^ 2 * Fintype.card G ≤ (S.card : ℝ) := by
    simp_rw [hind] at hpair
    rw [Fintype.expect_eq_sum_div_card] at hpair
    have hsum : (∑ h : G, if h ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by simp
    rw [hsum] at hpair
    exact (le_div_iff₀ hG).mp hpair
  have hpos : (0 : ℝ) < S.card := (mul_pos (sq_pos_of_pos hδ) hG).trans_le hSsize
  exact ⟨a, b, c, d, S, Finset.card_pos.mp (by exact_mod_cast hpos), hSsize,
    fun h hh => (Finset.mem_filter.mp hh).2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCoveredCommonFactorization
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem exists_native_periodic_factorization_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a ≤ (p + C) ^ C ∧
      ((p + a) ^ a + 1 + b) ^ b ≤ (p + C) ^ C := by
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B + (B + 1 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hB : 0 ≤ (p + a) ^ a := by positivity
  have hM : 0 ≤ ((p + a) ^ a + 1 + b) ^ b := by positivity
  have hsum : (p + a) ^ a + ((p + a) ^ a + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hsum, hM], by linarith only [hsum, hB]⟩

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem exists_common_reference_correction_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let B := (p + a) ^ a
      B ≤ (p + C) ^ C ∧ B + ((B + 3) ^ 2 + s * B) + 2 ≤ (p + C) ^ C := by
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B + ((B + 3) ^ 2 + Polynomial.C s * B) + 2)
  refine ⟨C, hC, ?_⟩
  intro p hp B'
  have hB : 0 ≤ B' := by dsimp only [B']; positivity
  have hrest : 0 ≤ (B' + 3) ^ 2 + s * B' := by positivity
  have hcost : B' + ((B' + 3) ^ 2 + s * B') + 2 ≤ (p + C) ^ C := by
    simpa [B, B', Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hcost, hrest], hcost⟩

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_frozen_common_factorization_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a ≤ (p + C) ^ C ∧
      ((p + a) ^ a + 2 + b) ^ b ≤ (p + C) ^ C := by
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B + (B + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hB : 0 ≤ (p + a) ^ a := by positivity
  have hF : 0 ≤ ((p + a) ^ a + 2 + b) ^ b := by positivity
  have hsum : (p + a) ^ a + ((p + a) ^ a + 2 + b) ^ b ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hsum, hF], by linarith only [hsum, hB]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonCoefficientBasisBudget
namespace OAI

section

namespace Erdos3

theorem coefficientSpaceBasisBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → coefficientSpaceBasisBudget p ≤ (p + C) ^ C := by
  let S (x : Polynomial ℕ) := x + x * ((x + 2) ^ 7 + x)
  let B (x : Polynomial ℕ) := S (x + (x + (x + 3) ^ 7 + 2) ^ 4 + 1)
  let D (x : Polynomial ℕ) := B (x + S (4 * x + 1))
  let R : Polynomial ℕ := ((Polynomial.X + 1 + (Polynomial.X + 3) ^ 7 + 2) ^ 9 +
    Polynomial.X + 4) ^ 4
  let H : Polynomial ℕ := Polynomial.X + Polynomial.X * (R + 1 + (Polynomial.X + 3) ^ 7)
  let A : Polynomial ℕ := Polynomial.X + 4 * Polynomial.X + H + (Polynomial.X + 3) ^ 7 + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (B (A + (A + 2) ^ 4 + D A))
  refine ⟨C, hC, fun p hp => ?_⟩
  have h := hbound p hp
  simpa [S, B, D, R, H, A, coefficientSpaceBasisBudget, coefficientSpaceInputBudget,
    dependentCoordinateBudget, preimageBasisBudget, sparseGeneratorBudget,
    horizontalCoordinateBudget, refiltrationCoordinateBudget, Polynomial.eval₂_pow] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MarkedEvaluationHeightBudget
namespace OAI

section

namespace Erdos3

theorem markedQuotient_source_height_bound (s n a d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s + 1 : ℕ) ≤ p) (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    let T := lieTreeHeight n H s
    let U := max T (s + 1)
    (((a + 1) * (rationalSolveHeight d T * T) ^ a : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ ((6 * s + 4) * 11)) ∧
      (rationalLieStructureHeight a (max U (rationalSolveHeight d U)) : ℝ) ≤
        Real.exp ((p + 2) ^ ((6 * s + 4) * 11)) := by
  let k := 6 * s + 2
  let K := (p + 2) ^ k
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  have hpK : p ≤ K := le_power_budget hp (by dsimp [k]; omega)
  have hT : (T : ℝ) ≤ Real.exp K := lieTreeHeight_le_exp n H s hp hn hH
  have hU : (U : ℝ) ≤ Real.exp K := by
    change ((max T (s + 1) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max]
    refine max_le hT ?_
    calc
      (s + 1 : ℕ) ≤ p := hs
      _ ≤ p + 1 := by linarith
      _ ≤ Real.exp p := Real.add_one_le_exp p
      _ ≤ Real.exp K := Real.exp_le_exp.mpr hpK
  have hB₀ := embedding_coordinate_height_budget a d T T
    (show 0 ≤ K by dsimp [K]; positivity) (ha.trans hpK) (hd.trans hpK) hT hT
  have hB := exponential_budget_comp hp (show 0 ≤ K by dsimp [K]; positivity) k 8 le_rfl hB₀
  have hC₀ := rationalLieStructureHeight_inverse_budget a d U
    (show 0 ≤ K by dsimp [K]; positivity) (ha.trans hpK) (hd.trans hpK) hU
  have hC := exponential_budget_comp hp (show 0 ≤ K by dsimp [K]; positivity) k 11 le_rfl hC₀
  refine ⟨hB.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) ?_)), ?_⟩
  · dsimp [k]
    omega
  · simpa only [k, show 6 * s + 2 + 2 = 6 * s + 4 by omega] using hC

theorem markedQuotient_projection_height_bound (m B C v : ℕ) (hv : 1 ≤ v)
    {p : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp ((p + 2) ^ v))
    (hC : (C : ℝ) ≤ Real.exp ((p + 2) ^ v)) :
    (rationalKernelHeight m B : ℝ) ≤ Real.exp ((p + 2) ^ ((v + 2) * 7)) ∧
      ((max 1 (max C (rationalKernelHeight m B)) : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ ((v + 2) * 7)) := by
  have hQ₀ := rationalKernelHeight_le_budget m B
    (show 0 ≤ (p + 2) ^ v by positivity) (hm.trans (le_power_budget hp hv)) hB
  have hQ := exponential_budget_comp hp (show 0 ≤ (p + 2) ^ v by positivity) v 7 le_rfl hQ₀
  refine ⟨hQ, ?_⟩
  rw [Nat.cast_max, Nat.cast_max, Nat.cast_one]
  refine max_le (Real.one_le_exp (by positivity)) (max_le ?_ hQ)
  exact hC.trans (Real.exp_le_exp.mpr
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by omega : v ≤ (v + 2) * 7)))

theorem markedQuotient_final_height_bound (d q B Q J w : ℕ) (hw : 1 ≤ w)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hQ : (Q : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hJ : (J : ℝ) ≤ Real.exp ((p + 2) ^ w)) :
    ((max (rationalLieStructureHeight d (max J (rationalSolveHeight q J)))
      ((d + 1) * (B * Q) ^ d) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ ((w + 2) * 11)) := by
  let W := (p + 2) ^ w
  have hpW : p ≤ W := le_power_budget hp hw
  have hCQ₀ := rationalLieStructureHeight_inverse_budget d q J
    (show 0 ≤ W by dsimp [W]; positivity) (hd.trans hpW) (hq.trans hpW) hJ
  have hCQ := exponential_budget_comp hp (show 0 ≤ W by dsimp [W]; positivity) w 11 le_rfl hCQ₀
  have hproduct : ((B * Q : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 1)) := by
    rw [Nat.cast_mul]
    calc
      (B : ℝ) * Q ≤ Real.exp W * Real.exp W :=
        mul_le_mul hB hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (W + W) := (Real.exp_add W W).symm
      _ ≤ Real.exp ((p + 2) ^ (w + 1)) := by
        apply Real.exp_le_exp.mpr
        calc
          W + W = 2 * W := by ring
          _ ≤ (p + 2) * W := mul_le_mul_of_nonneg_right (by linarith) (by dsimp [W]; positivity)
          _ = (p + 2) ^ (w + 1) := by dsimp [W]; rw [pow_succ]; ring
  have hLQ := rational_sum_cost_le_exp d (B * Q) hp (w + 1) 1 hproduct
    (by simpa only [pow_one] using hd.trans (by linarith : p ≤ p + 2))
  rw [Nat.cast_max]
  refine max_le hCQ (hLQ.trans (Real.exp_le_exp.mpr ?_))
  exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by omega : w + 1 + 1 + 1 ≤ (w + 2) * 11)

theorem markedQuotientHeight_le_exp (s n a d m q H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s + 1 : ℕ) ≤ p) (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (markedQuotientHeight s n a d m q H : ℝ) ≤ Real.exp ((p + 2) ^ (5082 * s + 3564)) := by
  let v := (6 * s + 4) * 11
  let w := (v + 2) * 7
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  let Q := rationalKernelHeight m B
  let J := max 1 (max C Q)
  obtain ⟨hB, hC⟩ := markedQuotient_source_height_bound s n a d H hp hs hn ha hd hH
  obtain ⟨hQ, hJ⟩ := markedQuotient_projection_height_bound m B C v
    (by dsimp [v]; omega) hp hm hB hC
  have hBW : (B : ℝ) ≤ Real.exp ((p + 2) ^ w) := hB.trans (Real.exp_le_exp.mpr
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by dsimp [w]; omega : v ≤ w)))
  have h := markedQuotient_final_height_bound d q B Q J w (by dsimp [w]; omega) hp hd hq hBW hQ hJ
  have he : (w + 2) * 11 = 5082 * s + 3564 := by dsimp [w, v]; omega
  change ((max (rationalLieStructureHeight d (max J (rationalSolveHeight q J)))
    ((d + 1) * (B * Q) ^ d) : ℕ) : ℝ) ≤ _
  simpa only [he] using h

end Erdos3

end

section

namespace Erdos3

theorem markedEvaluation_extra_height_bound (n d q T Q K w : ℕ) (hw : 1 ≤ w)
    {p : ℝ} (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hT : (T : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hQ : (Q : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hK' : (K : ℝ) ≤ Real.exp ((p + 2) ^ w)) :
    (((d + 1) * (rationalSolveHeight q Q * max T ((n + 1) * (T * K) ^ n)) ^ d : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ ((w + 3 + 2) * 8)) := by
  let W := (p + 2) ^ w
  have hpW : p ≤ W := le_power_budget hp hw
  have hW : 0 ≤ W := hp.trans hpW
  have hproduct : ((T * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 1)) := by
    rw [Nat.cast_mul]
    calc
      (T : ℝ) * K ≤ Real.exp W * Real.exp W :=
        mul_le_mul hT hK' (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (W + W) := (Real.exp_add W W).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          W + W = 2 * W := by ring
          _ ≤ (p + 2) * W := mul_le_mul_of_nonneg_right (by linarith) hW
          _ = (p + 2) ^ (w + 1) := by dsimp [W]; rw [pow_succ]; ring
  have hinner : (((n + 1) * (T * K) ^ n : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 3)) := by
    simpa only [show w + 1 + 1 + 1 = w + 3 by omega] using
      rational_sum_cost_le_exp n (T * K) hp (w + 1) 1 hproduct
        (by simpa only [pow_one] using hn.trans (by linarith : p ≤ p + 2))
  have hWW : W ≤ (p + 2) ^ (w + 3) :=
    pow_le_pow_right₀ (by linarith) (by omega : w ≤ w + 3)
  have hA : ((max T ((n + 1) * (T * K) ^ n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 3)) := by
    rw [Nat.cast_max]
    exact max_le (hT.trans (Real.exp_le_exp.mpr hWW)) hinner
  have hpV : p ≤ (p + 2) ^ (w + 3) := hpW.trans hWW
  have hV : 0 ≤ (p + 2) ^ (w + 3) := hp.trans hpV
  have heval := embedding_coordinate_height_budget d q Q (max T ((n + 1) * (T * K) ^ n))
    hV (hd.trans hpV) (hq.trans hpV) (hQ.trans (Real.exp_le_exp.mpr hWW)) hA
  exact exponential_budget_comp hp hV (w + 3) 8 le_rfl heval

theorem markedEvaluationHeight_le_exp (s n a d m q H K : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s + 1 : ℕ) ≤ p) (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) :
    (markedEvaluationHeight s n a d m q H K : ℝ) ≤
      Real.exp ((p + 2) ^ (5082 * s + 3564)) := by
  let v := (6 * s + 4) * 11
  let w := (v + 2) * 7
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  let Q := rationalKernelHeight m B
  have hw : 1 ≤ w := by dsimp [w, v]; omega
  have hpW : p ≤ (p + 2) ^ w := le_power_budget hp hw
  obtain ⟨hB, hC⟩ := markedQuotient_source_height_bound s n a d H hp hs hn ha hd hH
  obtain ⟨hQ, _⟩ := markedQuotient_projection_height_bound m B C v
    (by dsimp [v]; omega) hp hm hB hC
  have hT : (T : ℝ) ≤ Real.exp ((p + 2) ^ w) :=
    (lieTreeHeight_le_exp n H s hp hn hH).trans (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by dsimp [w, v]; omega : 6 * s + 2 ≤ w)))
  have heval := markedEvaluation_extra_height_bound n d q T Q K w hw hp hn hd hq hT hQ
    (hK.trans (Real.exp_le_exp.mpr hpW))
  change ((max (markedQuotientHeight s n a d m q H)
    ((d + 1) * (rationalSolveHeight q Q * max T ((n + 1) * (T * K) ^ n)) ^ d) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max]
  refine max_le (markedQuotientHeight_le_exp s n a d m q H hp hs hn ha hd hm hq hH) ?_
  exact heval.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith)
    (by dsimp [w, v]; omega : (w + 3 + 2) * 8 ≤ 5082 * s + 3564)))

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

namespace TailReflectionData

noncomputable def reflectedKernel {n : ℕ} {T G : Type*} (D : TailReflectionData n T G)
    (t : T) (u v : Fin n → G) (h m : G) : ℂ :=
  iteratedBoxDifference n (fun x (a : G × G) => D.kernel t a.1 a.2 x) u v (h, m)

end TailReflectionData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReflectedFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

universe u

noncomputable def mixedTailDifference {n : ℕ} {G : Type*}
    (K : G → G → (Fin n → G) → ℂ) (u v : Fin n → G) (h m : G) : ℂ :=
  iteratedBoxDifference n (fun x (a : G × G) => K a.1 a.2 x) u v (h, m)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedReflectedCorner {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (c : G) (a : Fin n → G) (ω : Fin n → Bool)
    (x : Fin (n + 2) → G) : ℂ :=
  conjugationPower (booleanWeight ω)
      (K (x 0) (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω)) *
    star (conjugationPower (booleanWeight ω)
      (K (x 1) (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω)))

theorem mixedReflectedCorner_norm {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (hK : ∀ h m x, ‖K h m x‖ ≤ 1)
    (c : G) (a : Fin n → G) (ω : Fin n → Bool) (x : Fin (n + 2) → G) :
    ‖mixedReflectedCorner K c a ω x‖ ≤ 1 := by
  have hc (h m : G) (v : Fin n → G) :
      ‖conjugationPower (booleanWeight ω) (K h m v)‖ ≤ 1 := by
    rw [conjugationPower_eq_if_mod]
    split_ifs <;> simpa only [norm_star] using hK h m v
  rw [mixedReflectedCorner, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hc _ _ _)).trans (hc _ _ _)

theorem mixedReflectedCorner_independent {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (c : G) (a : Fin n → G) (ω : Fin n → Bool)
    (j : Fin n) (hj : ω j = true) (x y : Fin (n + 2) → G)
    (hxy : ∀ k, k ≠ j.succ.succ → x k = y k) :
    mixedReflectedCorner K c a ω x = mixedReflectedCorner K c a ω y := by
  have h0 : x 0 = y 0 := hxy 0 (Fin.succ_ne_zero j.succ).symm
  have hne : j.succ.succ ≠ (1 : Fin (n + 2)) := by
    intro heq
    exact Fin.succ_ne_zero j (Fin.succ_injective (n + 1) heq)
  have h1 : x 1 = y 1 := hxy 1 hne.symm
  have hcorner : boxCorner (fun i => x i.succ.succ) a ω =
      boxCorner (fun i => y i.succ.succ) a ω := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [boxCorner, hj]
    · have hk : k.succ.succ ≠ j.succ.succ := by
        intro heq
        exact hkj (Fin.succ_injective n (Fin.succ_injective (n + 1) heq))
      simp only [boxCorner, hxy k.succ.succ hk]
  simp only [mixedReflectedCorner, h0, h1, hcorner]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FamilyDerivativeCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_many_family_derivative_correlations {I G : Type*}
    [Fintype I] [Nonempty I] [AddCommGroup G] [Fintype G]
    (f g : I → G → ℂ) (H : Finset I)
    (hf : ∀ i n, ‖f i n‖ ≤ 1) (hg : ∀ i n, ‖g i n‖ ≤ 1)
    {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card I ≤ (H.card : ℝ))
    (hcorr : ∀ i ∈ H, δ ≤ ‖finiteCorrelation Finset.univ (f i) (g i)‖) :
    ∃ Q : Finset (I × G), Q.Nonempty ∧
      α * δ ^ 2 / 2 * Fintype.card I * Fintype.card G ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 ∈ H ∧ α * δ ^ 2 / 2 ≤
        ‖finiteCorrelation Finset.univ
          (multiplicativeDerivative (f t.1) t.2) (multiplicativeDerivative (g t.1) t.2)‖ := by
  classical
  let value (t : I × G) := if t.1 ∈ H then
    ‖finiteCorrelation Finset.univ
      (multiplicativeDerivative (f t.1) t.2) (multiplicativeDerivative (g t.1) t.2)‖ else 0
  have hrow (i : I) : (if i ∈ H then δ ^ 2 else 0) ≤ 𝔼 k : G, value (i, k) := by
    by_cases hi : i ∈ H
    · simp only [value, hi, ite_true]
      exact (pow_le_pow_left₀ hδ.le (hcorr i hi) 2).trans
        (correlation_sq_le_expect_norm_derivative (f i) (g i))
    · simp only [value, hi, ite_false, Fintype.expect_const, le_refl]
  have hcard : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hindicator : (𝔼 i : I, if i ∈ H then δ ^ 2 else 0) =
      (H.card : ℝ) * δ ^ 2 / Fintype.card I := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : α * δ ^ 2 ≤ 𝔼 t : I × G, value t := by
    calc
      _ ≤ (H.card : ℝ) * δ ^ 2 / Fintype.card I := by
        apply (le_div_iff₀ hcard).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense (sq_nonneg δ)]
      _ = (𝔼 i : I, if i ∈ H then δ ^ 2 else 0) := hindicator.symm
      _ ≤ 𝔼 i : I, 𝔼 k : G, value (i, k) := Finset.expect_le_expect (fun i _ => hrow i)
      _ = _ := by rw [← Finset.expect_product, Finset.univ_product_univ]
  have hcap (t : I × G) : value t ≤ 1 := by
    by_cases ht : t.1 ∈ H
    · simp only [value, ht, ite_true]
      simpa only [one_pow] using norm_derivativeCorrelation_le (f t.1) (g t.1) (hf t.1) (hg t.1) t.2
    · simp only [value, ht, ite_false, zero_le_one]
  obtain ⟨Q, hQsize, hQcorr⟩ :=
    exists_dense_level_set value (by positivity : 0 ≤ α * δ ^ 2) hcap hmean
  have hsize : α * δ ^ 2 / 2 * Fintype.card I * Fintype.card G ≤ (Q.card : ℝ) := by
    simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc] using hQsize
  have hI : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hG : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le
      (by positivity : 0 < α * δ ^ 2 / 2 * (Fintype.card I : ℝ) * Fintype.card G) hsize
  refine ⟨Q, hQ, hsize, ?_⟩
  intro t ht
  have hm : t.1 ∈ H := by
    by_contra hn
    have hpos : 0 < value t := lt_of_lt_of_le (by positivity) (hQcorr t ht)
    simp only [value, hn, ite_false, lt_self_iff_false] at hpos
  exact ⟨hm, by simpa only [value, hm, ite_true] using hQcorr t ht⟩

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

theorem finiteFourierCoeff_reflected_conjugate (f : G → ℂ) (χ : AddChar G ℂ) :
    finiteFourierCoeff (fun x => star (f (-x))) χ = star (finiteFourierCoeff f χ) := by
  rw [finiteFourierCoeff, star_finiteFourierCoeff]
  apply Fintype.expect_equiv (Equiv.neg G)
  intro x
  simp only [Equiv.neg_apply, AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem cross_correlation_fourier_energy (f g : G → ℂ) :
    (𝔼 h, ‖𝔼 x, f x * star (g (x + h))‖ ^ 2) =
      ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ ^ 2 * ‖finiteFourierCoeff g χ‖ ^ 2 := by
  let C := finiteConvolution f (fun x => star (g (-x)))
  calc
    _ = 𝔼 h, ‖C h‖ ^ 2 := by
      apply Fintype.expect_equiv (Equiv.neg G)
      intro h
      simp only [C, finiteConvolution, Equiv.neg_apply, neg_sub, sub_neg_eq_add]
    _ = ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff C χ‖ ^ 2 := (finiteFourier_parseval C).symm
    _ = _ := by
      simp only [C, finiteFourierCoeff_convolution, finiteFourierCoeff_reflected_conjugate,
        norm_mul, norm_star, mul_pow]

theorem exists_large_fourier_of_mean_cross_correlation (f g : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ χ : AddChar G ℂ, (𝔼 h, ‖𝔼 x, f x * star (g (x + h))‖) ≤ ‖finiteFourierCoeff g χ‖ := by
  classical
  obtain ⟨χ, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun χ : AddChar G ℂ => ‖finiteFourierCoeff g χ‖) Finset.univ_nonempty
  have hmass : (∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2) ≤ 1 := by
    rw [finiteFourier_parseval]
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2
  have henergy : (𝔼 h, ‖𝔼 x, f x * star (g (x + h))‖ ^ 2) ≤ ‖finiteFourierCoeff g χ‖ ^ 2 := by
    rw [cross_correlation_fourier_energy]
    calc
      _ ≤ ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2 * ‖finiteFourierCoeff g χ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ψ _
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hmax ψ (Finset.mem_univ ψ)) 2) (sq_nonneg _)
      _ = (∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2) * ‖finiteFourierCoeff g χ‖ ^ 2 :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ ‖finiteFourierCoeff g χ‖ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hmass
  refine ⟨χ, (sq_le_sq₀ (Finset.expect_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _)).mp ?_⟩
  exact (expect_square_le (fun h => ‖𝔼 x, f x * star (g (x + h))‖)).trans henergy

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteChoiceLeafCoordinates
namespace OAI

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ] {n : ℕ}

theorem finiteChoiceLeafInput_of_not_mem (l : List σ) :
    ∀ (v : Fin l.length → Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ) (j : σ),
      j ∉ l → finiteChoiceLeafInput l v x j = x (0, j) := by
  induction l with
  | nil => intro v x j _; rfl
  | cons i l ih =>
      intro v x j hj
      simp only [List.mem_cons, not_or] at hj
      rw [finiteChoiceLeafInput, ih (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) j hj.2]
      simp [finiteChoiceReplaceInput, finiteChoiceReplaceIndex, hj.1]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerDivision
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def divisionPolynomial {σ : Type*} (d : ℕ) (r : σ → ℤ) (i : σ) : MvPolynomial σ ℚ :=
  MvPolynomial.C (d : ℚ)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (r i : ℚ))

theorem divisionPolynomial_eval {σ : Type*} (d : ℕ) [NeZero d] (r x : σ → ℤ)
    (hr : ∀ i, x i % (d : ℤ) = r i) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (divisionPolynomial d r i) =
      ((x i / (d : ℤ) : ℤ) : ℚ) := by
  have hi : x i = (d : ℤ) * (x i / (d : ℤ)) + r i := by
    calc
      _ = x i % (d : ℤ) + (d : ℤ) * (x i / (d : ℤ)) := (Int.emod_add_mul_ediv _ _).symm
      _ = _ := by rw [hr i]; ring
  have hiq : (x i : ℚ) = (d : ℚ) * ((x i / (d : ℤ) : ℤ) : ℚ) + (r i : ℚ) := by
    exact_mod_cast hi
  simp only [divisionPolynomial, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  change (d : ℚ)⁻¹ * ((x i : ℚ) - (r i : ℚ)) = ((x i / (d : ℤ) : ℤ) : ℚ)
  rw [hiq, add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d)), one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeMixedCoordinateSlices
namespace OAI

section

namespace Erdos3

theorem mixedExchangeCoordinate_involutive (n : ℕ) :
    Function.Involutive (mixedExchangeCoordinate n) := by
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

theorem mixedExchangeCoordinate_update (n : ℕ) {α : Type*}
    (x : Fin (n + 2) → α) (d : Fin (n + 2)) (c : α) :
    Function.update (fun k => x (mixedExchangeCoordinate n k)) (mixedExchangeCoordinate n d) c =
      fun k => (Function.update x d c) (mixedExchangeCoordinate n k) := by
  funext k
  have hi (k : Fin (n + 2)) :
      mixedExchangeCoordinate n (mixedExchangeCoordinate n k) = k :=
    mixedExchangeCoordinate_involutive n k
  by_cases h : k = mixedExchangeCoordinate n d
  · subst k
    simp only [Function.update_self, hi]
  · have hk : mixedExchangeCoordinate n k ≠ d := by
      intro heq
      apply h
      have h' := congrArg (mixedExchangeCoordinate n) heq
      simpa only [hi] using h'
    simp only [Function.update_of_ne h, Function.update_of_ne hk]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HigherResidualRowDifferences
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem dense_set_mean_lower_bound {I : Type*} [Fintype I] [Nonempty I]
    (H : Finset I) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) {α δ : ℝ} (hδ : 0 ≤ δ)
    (hdensity : α * Fintype.card I ≤ (H.card : ℝ))
    (hlarge : ∀ i ∈ H, δ ≤ f i) : α * δ ≤ 𝔼 i, f i := by
  classical
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hindicator : (𝔼 i : I, if i ∈ H then δ else 0) =
      (H.card : ℝ) * δ / Fintype.card I := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  calc
    _ ≤ (H.card : ℝ) * δ / Fintype.card I := by
      apply (le_div_iff₀ hcard).mpr
      nlinarith [mul_le_mul_of_nonneg_right hdensity hδ]
    _ = _ := hindicator.symm
    _ ≤ _ := by
      apply Finset.expect_le_expect
      intro i _
      split_ifs with hi
      · exact hlarge i hi
      · exact hf i

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

def mixedExchangePermutation (s : ℕ) : Equiv.Perm (Fin (s + 3)) where
  toFun := mixedExchangeCoordinate (s + 1)
  invFun := mixedExchangeCoordinate (s + 1)
  left_inv := mixedExchangeCoordinate_involutive (s + 1)
  right_inv := mixedExchangeCoordinate_involutive (s + 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NativeMixedFourierProfiles
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_fourier_of_twisted_unit_shift {N : ℕ} [NeZero N]
    (q f : ZMod N → ℂ) (ζ : ℂ) (hq : ∀ n, ‖q n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hζ : ‖ζ‖ = 1) (hstep : (𝔼 n : ZMod N, ‖q (n + 1) - ζ * q n‖) ≤ 2 / N)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 n, f n * star (q n)‖) :
    ∃ χ : AddChar (ZMod N) ℂ, ρ ^ 2 / 16 ≤ ‖finiteFourierCoeff f χ‖ := by
  let C (h : ZMod N) := 𝔼 n : ZMod N, q n * star (f (n + h))
  let c := 𝔼 n : ZMod N, q n * star (f n)
  have hc : ρ ≤ ‖c‖ := by
    have heq : c = star (𝔼 n : ZMod N, f n * star (q n)) := by
      rw [← expect_star]
      apply Finset.expect_congr rfl
      intro n _
      simp only [star_mul, star_star]
    rw [heq, norm_star]
    exact hcorr
  have hrow (m : ℕ) : ρ - (m : ℝ) * (2 / N) ≤ ‖C (m : ZMod N)‖ := by
    have hshift : c = 𝔼 n : ZMod N, q (n + m) * star (f (n + m)) :=
      (Fintype.expect_equiv (Equiv.addRight (m : ZMod N)) _ _ (fun _ => rfl)).symm
    have hmul : ζ ^ m * C (m : ZMod N) =
        𝔼 n : ZMod N, (ζ ^ m * q n) * star (f (n + m)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      ring
    have herr : ‖c - ζ ^ m * C (m : ZMod N)‖ ≤ (m : ℝ) * (2 / N) := by
      rw [hshift, hmul, ← Finset.expect_sub_distrib]
      apply (RCLike.norm_expect_le (K := ℂ)).trans
      apply le_trans _ (mean_twisted_nat_translate_error q ζ hζ.le hstep m)
      apply Finset.expect_le_expect
      intro n _
      rw [← sub_mul, norm_mul, norm_star]
      exact mul_le_of_le_one_right (norm_nonneg _) (hf _)
    have hnorm : ‖ζ ^ m * C (m : ZMod N)‖ = ‖C (m : ZMod N)‖ := by
      rw [norm_mul, norm_pow, hζ, one_pow, one_mul]
    have htriangle : ‖c‖ ≤ ‖c - ζ ^ m * C (m : ZMod N)‖ + ‖C (m : ZMod N)‖ := by
      rw [← hnorm]
      exact norm_le_norm_sub_add _ _
    linarith
  let δ := ρ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨K, hK, hKN, hsmall, hratio⟩ := exists_smoothing_scale (NeZero.pos N) hδ hδ1
  let H := cyclicInterval (0 : ZMod N) K
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hdense : (ρ / 8) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    have hh := (div_le_div_iff₀ hKpos hδ).mp hratio
    dsimp only [δ] at hh
    rw [show H.card = K from cyclicInterval_card 0 hKN, ZMod.card]
    nlinarith
  have hlarge (h : ZMod N) (hh : h ∈ H) : ρ / 2 ≤ ‖C h‖ := by
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hh
    have hmK : m ≤ K - 1 := by have := Finset.mem_range.mp hm; omega
    have hmreal : (m : ℝ) ≤ δ * N := (Nat.cast_le.mpr hmK).trans hsmall
    have he' : (m : ZMod N) = h := by simpa using he
    have heps : (m : ℝ) * (2 / N) ≤ ρ / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hNpos).mpr
      dsimp only [δ] at hmreal
      nlinarith
    rw [← he']
    linarith [hrow m]
  have hmass := dense_set_mean_lower_bound H (fun h => ‖C h‖) (fun _ => norm_nonneg _)
    (show 0 ≤ ρ / 2 by positivity) hdense hlarge
  obtain ⟨χ, hχ⟩ := exists_large_fourier_of_mean_cross_correlation q f hq
  refine ⟨χ, ?_⟩
  have heq : (ρ / 8) * (ρ / 2) = ρ ^ 2 / 16 := by ring
  rw [heq] at hmass
  exact hmass.trans hχ

end Erdos3

end

end OAI
end


