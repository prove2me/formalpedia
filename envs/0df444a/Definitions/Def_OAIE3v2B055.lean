-- Prove2me | Definitions.Def_OAIE3v2B055
-- name    : OAIE3v2B055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:12:43.174644+00:00
-- url     : https://prove2.me/theorems/2ed3fc1f-c372-458f-8fed-335add7891fc
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 56 of 311
-- statement:
--   Definitions bundle 56 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B007`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B012`, `OAIE3v2B013`, `OAIE3v2B016`, `OAIE3v2B017`, `OAIE3v2B018`, `OAIE3v2B023`, `OAIE3v2B024` of this split.
--
--   Modules: `Dynamics/ImageReconstructionLogBudget.lean`, `Dynamics/SparseGeneratorBudget.lean`, `Dynamics/SquarefreeModelBudget.lean`, `Estimates/CommonFreeSunflower.lean`, `Estimates/ComplexFiniteMeans.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/ImageCosetReconstruction.lean`, `Estimates/InvariantUnitFamily.lean`, `Estimates/MomentEvaluationBounds.lean`, `Estimates/SymmetricSquarefreeMonotonicity.lean`, `Estimates/VectorApproximationPrecomposition.lean`, `Geometry/BoundedDependentCoordinates.lean`, `Geometry/NativeCoordinateEstimates.lean`, `Geometry/NativeCoordinateSplitFreezing.lean`, `Geometry/NativeProductOrbitMetric.lean`, `Geometry/SymmetricEvaluationMetric.lean`, `Linear/FurstenbergWeissProjection.lean`, `Linear/RankIntervalFactorization.lean`, `Polynomial/TotalDegreeSplitDownsets.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B012
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B017
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B023
import Definitions.Def_OAIE3v2B024

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ImageReconstructionLogBudget
namespace OAI

section

namespace Erdos3

theorem exists_generalReconstructionLogBudget_bound (C D E F Z : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      40 * generalReconstructionLogBudget C D E F Z p ≤ (p + N) ^ N := by
  let R : Polynomial ℕ := ((Polynomial.X + 2) ^ 4 + Polynomial.C C) ^ C + (Polynomial.X + 2) ^ 2
  let q : Polynomial ℕ := Polynomial.X + R + 1
  let P : Polynomial ℕ := 40 * (Polynomial.X + (Polynomial.X + 2) ^ 18 +
    (Polynomial.X + 2) ^ 48 + (Polynomial.X + 2) ^ 24 +
    ((Polynomial.X + Polynomial.C Z) ^ Z + 1) +
    (q + Polynomial.C D + Polynomial.C E) ^ E + (q + Polynomial.C F) ^ F + 1)
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  have heq : P.eval₂ (Nat.castRingHom ℝ) p = 40 * generalReconstructionLogBudget C D E F Z p := by
    simp [P, q, R, generalReconstructionLogBudget, imageRepresentativeLogBudget,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  rw [← heq]
  exact hbound p hp

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

theorem fourFirstProjection_map (f : V →ₗ[ℚ] W) (J : Submodule ℚ (Fin 4 → V)) :
    fourFirstProjection (J.map (fourLinearMap f)) = (fourFirstProjection J).map f := by
  ext y
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v 0, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨fourLinearMap f v, ⟨v, hv, rfl⟩, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_common_slice_of_equal_marginals {A B H : Type*}
    [Fintype A] [Fintype B] [Fintype H] [Nonempty A] [Nonempty B] [Nonempty H]
    (f : A → H → ℝ) (g : B → H → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmarginal : ∀ h, (𝔼 a, f a h) = 𝔼 b, g b h)
    (hmean : δ ≤ 𝔼 h, 𝔼 a, f a h) :
    ∃ (a : A) (b : B), δ ^ 2 ≤ 𝔼 h, f a h * g b h := by
  have henergy := (pow_le_pow_left₀ hδ hmean 2).trans
    (expect_square_le (fun h => 𝔼 a, f a h))
  have hproduct : (𝔼 h, (𝔼 a, f a h) ^ 2) = 𝔼 a, 𝔼 b, 𝔼 h, f a h * g b h := by
    calc
      _ = 𝔼 h, (𝔼 a, f a h) * (𝔼 b, g b h) := by
        apply Finset.expect_congr rfl
        intro h _
        rw [← hmarginal h, pow_two]
      _ = 𝔼 h, 𝔼 a, 𝔼 b, f a h * g b h := by simp_rw [Fintype.expect_mul_expect]
      _ = 𝔼 a, 𝔼 h, 𝔼 b, f a h * g b h := Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro a _
        exact Finset.expect_comm _ _ _
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty (henergy.trans_eq hproduct)
  obtain ⟨b, _, hb⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty ha
  exact ⟨a, b, hb⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SparseGeneratorBudget
namespace OAI

section

namespace Erdos3

theorem sparseGeneratorHeight_bound {p : ℝ} (hp : 0 ≤ p) (r n H : ℕ)
    (hr : (r : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (((n + 1) * (rationalKernelHeight r H * H) ^ n : ℕ) : ℝ) ≤
      Real.exp (sparseGeneratorBudget p) := by
  have hfront : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn le_rfl).trans (Real.add_one_le_exp p)
  have hbase : (rationalKernelHeight r H : ℝ) * H ≤ Real.exp ((p + 2) ^ 7 + p) := by
    rw [Real.exp_add]
    exact mul_le_mul (rationalKernelHeight_le_budget r H hp hr hH) hH
      (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ (rationalKernelHeight r H : ℝ) * H) hbase n
  rw [← Real.exp_nat_mul] at hpower
  push_cast
  calc
    ((n : ℝ) + 1) * ((rationalKernelHeight r H : ℝ) * H) ^ n ≤
        Real.exp p * Real.exp ((n : ℝ) * ((p + 2) ^ 7 + p)) :=
      mul_le_mul hfront hpower (by positivity) (Real.exp_pos _).le
    _ = Real.exp (p + (n : ℝ) * ((p + 2) ^ 7 + p)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (sparseGeneratorBudget p) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hn (by positivity))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageCosetReconstruction
namespace OAI

section

namespace Erdos3

variable {H G A : Type*} [Group H] [Group G]

def projectToCosetImage (φ : H →* G) (Λ : Subgroup G) (x : H) : CosetImage φ Λ :=
  ⟨QuotientGroup.mk (φ x), ⟨x, rfl⟩⟩

theorem projectToCosetImage_surjective (φ : H →* G) (Λ : Subgroup G) :
    Function.Surjective (projectToCosetImage φ Λ) := by
  rintro ⟨y, x, rfl⟩
  exact ⟨x, rfl⟩

theorem factorsThrough_image_cosets (φ : H →* G) (Γ : Subgroup H) (Λ : Subgroup G)
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    Function.FactorsThrough f (projectToCosetImage φ Λ) := by
  intro x y hxy
  have hmem : (φ x)⁻¹ * φ y ∈ Λ := QuotientGroup.eq.mp (congrArg Subtype.val hxy)
  have hrange : (φ x)⁻¹ * φ y ∈ φ.range := ⟨x⁻¹ * y, by simp only [map_mul, map_inv]⟩
  obtain ⟨γ, hγ, hφγ⟩ := hcover ⟨hmem, hrange⟩
  let k := y * γ⁻¹ * x⁻¹
  have hk : k ∈ φ.ker := by
    change φ k = 1
    simp only [k, map_mul, map_inv, hφγ, mul_inv_rev, inv_inv]
    group
  have hdecomp : k * (x * γ) = y := by dsimp [k]; group
  calc
    f x = f (x * γ) := (hΓ γ hγ x).symm
    _ = f (k * (x * γ)) := (hker k hk (x * γ)).symm
    _ = f y := congrArg f hdecomp

theorem exists_unique_cosetImage_reconstruction (φ : H →* G) (Γ : Subgroup H) (Λ : Subgroup G)
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    ∃! F : CosetImage φ Λ → A, ∀ x, F (projectToCosetImage φ Λ x) = f x := by
  let π := projectToCosetImage φ Λ
  have hπ := projectToCosetImage_surjective φ Λ
  have hf := factorsThrough_image_cosets φ Γ Λ hcover f hker hΓ
  let F : CosetImage φ Λ → A := fun y => f (Function.surjInv hπ y)
  have hF (x : H) : F (π x) = f x := hf (Function.surjInv_eq hπ (π x))
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  funext y
  obtain ⟨x, rfl⟩ := hπ y
  exact (hF' x).trans (hF x).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TotalDegreeSplitDownsets
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def totalDegreeSplitDownset (s : ℕ) (b : Bool) : Set (Fin 2 →₀ ℕ) :=
  {a | ∀ i, a i ≤ totalDegreeSplitBound s b i}

theorem totalDegreeSplitBound_le (s : ℕ) (b : Bool) :
    totalDegreeSplitBound s b ≤ fun _ => s := by
  intro i
  fin_cases i <;> cases b <;> simp [totalDegreeSplitBound]

theorem totalDegreeSplitDownset_lower (s : ℕ) (b : Bool) :
    IsLowerSet (totalDegreeSplitDownset s b) :=
  fun _ _ hab hb i => (hab i).trans (hb i)

theorem mem_totalDegreeSplitDownset_false (s : ℕ) (a : Fin 2 →₀ ℕ) :
    a ∈ totalDegreeSplitDownset s false ↔ a 0 = 0 ∧ a 1 ≤ s := by
  simp [totalDegreeSplitDownset, totalDegreeSplitBound, Fin.forall_fin_two]

theorem mem_totalDegreeSplitDownset_true (s : ℕ) (a : Fin 2 →₀ ℕ) :
    a ∈ totalDegreeSplitDownset s true ↔ a 0 ≤ s ∧ a 1 ≤ s - 1 := by
  simp [totalDegreeSplitDownset, totalDegreeSplitBound, Fin.forall_fin_two]

theorem totalDegreeSplitDownset_covers (s : ℕ) (a : Fin 2 →₀ ℕ)
    (ha : (∑ i, a i) ≤ s) :
    a ∈ totalDegreeSplitDownset s false ∪ totalDegreeSplitDownset s true := by
  rw [Fin.sum_univ_two] at ha
  by_cases hzero : a 0 = 0
  · exact Or.inl ((mem_totalDegreeSplitDownset_false s a).mpr ⟨hzero, by omega⟩)
  · exact Or.inr ((mem_totalDegreeSplitDownset_true s a).mpr ⟨by omega, by omega⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SquarefreeModelBudget
namespace OAI

section

namespace Erdos3

theorem squarefreeBracketHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (squarefreeBracketHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hcube : ((H * H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p := by
        push_cast
        gcongr
      _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hsq : ((n ^ 2 : ℕ) : ℝ) ≤ (p + 2) ^ 2 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (hn.trans (by linarith)) 2
  exact rational_sum_cost_le_exp (n ^ 2) (H * H * H) hp 2 2 hcube hsq

end Erdos3

end

section

namespace Erdos3

theorem le_squarefreeInputBudget (t : ℕ) {p : ℝ} (hp : 0 ≤ p) : p ≤ squarefreeInputBudget t p := by
  have hp2 : p ≤ (2 : ℝ) ^ t * p := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hp
  exact hp2.trans (le_add_of_nonneg_right (by positivity))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoundedDependentCoordinates
namespace OAI

section

namespace Erdos3

open Module

noncomputable def dependentCoordinateBudget (p : ℝ) : ℝ :=
  preimageBasisBudget (p + sparseGeneratorBudget (4 * p + 1))

theorem dependentCoordinateBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ dependentCoordinateBudget p := by
  apply preimageBasisBudget_nonneg
  exact add_nonneg hp (sparseGeneratorBudget_nonneg (by positivity))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorApproximationPrecomposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem euclidean_coefficient_norm_le_exp {I : Type*} [Fintype I] {q : ℝ}
    (hq : 0 ≤ q) (hI : (Fintype.card I : ℝ) ≤ Real.exp q)
    (c : EuclideanSpace ℂ I) (hc : ∀ i, ‖c i‖ ≤ 2) :
    ‖c‖ ≤ Real.exp (q + 2) := by
  have h := euclidean_norm_le_card_add_one_mul c (by norm_num : (0 : ℝ) ≤ 2) hc
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  nlinarith [Real.one_le_exp hq,
    mul_le_mul_of_nonneg_left hfour (Real.exp_nonneg q)]

theorem euclidean_error_le_of_coordinate_errors {I : Type*} [Fintype I]
    (v : EuclideanSpace ℂ I) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hv : ∀ i, ‖v i‖ ≤ epsilon / (Fintype.card I + 1 : ℝ)) :
    ‖v‖ ≤ epsilon := by
  have h := euclidean_norm_le_card_add_one_mul v (div_nonneg hepsilon (by positivity)) hv
  have hcard : (Fintype.card I + 1 : ℝ) ≠ 0 := by positivity
  simpa only [mul_div_cancel₀ _ hcard] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_bounded_complex_partition_approximation {I X : Type*} [Fintype I]
    [PseudoMetricSpace X] (w : I → X → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hsum : ∀ x, ∑ i, w i x = 1)
    {rho : ℝ} (hdiam : ∀ i x y, 0 < w i x → 0 < w i y → dist x y ≤ rho)
    (F : X → ℂ) (B : ℝ≥0) (hF : ∀ x, ‖F x‖ ≤ B) {K : ℝ≥0} (hLip : LipschitzWith K F) :
    ∃ c : I → ℂ, (∀ i, ‖c i‖ ≤ B) ∧
      ∀ x, ‖F x - ∑ i, (w i x : ℂ) * c i‖ ≤ (K : ℝ) * rho := by
  classical
  have hchoose (i : I) : ∃ c : ℂ, ‖c‖ ≤ B ∧
      ∀ x, 0 < w i x → ‖F x - c‖ ≤ (K : ℝ) * rho := by
    by_cases hi : ∃ y, 0 < w i y
    · obtain ⟨y, hy⟩ := hi
      refine ⟨F y, hF y, fun x hx => ?_⟩
      have h := hLip.dist_le_mul x y
      rw [dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hdiam i x y hx hy) K.coe_nonneg)
    · exact ⟨0, by simpa only [norm_zero] using B.coe_nonneg,
        fun x hx => False.elim (hi ⟨x, hx⟩)⟩
  choose c hc herr using hchoose
  exact ⟨c, hc, fun x => norm_sub_positive_sum_le (fun i => w i x) c (F x) _
    (fun i => hw i x) (hsum x) (fun i => herr i x)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MomentEvaluationBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem momentLinear_lipschitz {m : ℕ} {X : Type*} [PseudoMetricSpace X]
    (f : Fin m → X → ℂ) {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j))
    (z : Fin (m * m + 1)) :
    LipschitzWith ((momentWeightBound m : ℝ≥0) * K) (fun x => momentLinear (fun j => f j x) z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have heq : momentLinear (fun j => f j x) z - momentLinear (fun j => f j y) z =
      momentLinear (fun j => f j x - f j y) z := by
    simp only [momentLinear, Finset.sum_sub_distrib, sub_mul]
  rw [heq]
  calc
    _ ≤ (momentWeightBound m : ℝ) * ((K : ℝ) * dist x y) :=
      norm_momentLinear_le _ z (by positivity)
        (fun j => by simpa only [dist_eq_norm] using (hf j).dist_le_mul x y)
    _ = _ := by push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymmetricEvaluationMetric
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem symmetricEvaluation_metric {m : ℕ} {I X : Type*} [PseudoMetricSpace X]
    (f : Fin m → I → X → ℂ) {K : ℝ≥0}
    (hf : ∀ i j, LipschitzWith K (f i j)) (hn : ∀ i j x, ‖f i j x‖ ≤ 1)
    (k : SymmetricEvaluationIndex m I) :
    (∀ x, ‖symmetricEvaluation (fun i j => f i j x) k‖ ≤ (momentWeightBound m : ℝ) ^ m) ∧
      LipschitzWith (symmetricEvaluationLip m K)
        (fun x => symmetricEvaluation (fun i j => f i j x) k) := by
  have hB : (1 : ℝ≥0) ≤ momentWeightBound m := by exact_mod_cast momentWeightBound_pos m
  have h := bounded_lipschitz_fintype_prod
    (fun i x => momentLinear (fun j => f i (k.1 j) x) k.2) hB
    (fun i => momentLinear_lipschitz _ (fun j => hf i (k.1 j)) k.2)
    (fun i x => by simpa only [mul_one, NNReal.coe_natCast] using
      norm_momentLinear_le (fun j => f i (k.1 j) x) k.2 zero_le_one (fun j => hn i (k.1 j) x))
  simpa only [Fintype.card_fin, symmetricEvaluationLip, NNReal.coe_natCast,
    symmetricEvaluation, momentProduct, momentLinear] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InvariantUnitFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_symmetric_unit_family {m : ℕ} {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (f : Fin m → I → X → ℂ) {K : ℝ≥0}
    (hf : ∀ i j, LipschitzWith K (f i j))
    (hunit : ∀ i x, ∑ j, ‖f i j x‖ ^ 2 = 1) :
    ∃ g : SymmetricEvaluationIndex m I → X → ℂ,
      (∀ x, ∑ k, ‖g k x‖ ^ 2 = 1) ∧ (∀ k x, ‖g k x‖ ≤ 1) ∧
      (∀ k, LipschitzWith (symmetricUnitFamilyLip m (Fintype.card I) K) (g k)) ∧
      ∀ x y (c : ℂ) (e : Equiv.Perm (Fin m)), ‖c‖ = 1 →
        (∀ i j, f i j x = c * f (e i) j y) → ∀ k, g k x = c ^ m * g k y := by
  have hnorm (i j x) : ‖f i j x‖ ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => ‖f i j x‖ ^ 2) (fun j _ => sq_nonneg ‖f i j x‖) (Finset.mem_univ j)
    rw [hunit] at h
    nlinarith [norm_nonneg (f i j x)]
  let u (k : SymmetricEvaluationIndex m I) (x : X) := symmetricEvaluation (fun i j => f i j x) k
  have hlower (x) : ∃ k, (symmetricEvaluationRadius m (Fintype.card I) : ℝ) ≤ ‖u k x‖ :=
    symmetricEvaluation_lower (fun i j => f i j x) (fun i => hunit i x)
  obtain ⟨g, hgunit, hgnorm, hglip, hgphase⟩ := exists_normalized_complex_family u
    (symmetricEvaluationRadius_pos m (Fintype.card I))
    (fun k => (symmetricEvaluation_metric f hf hnorm k).2) hlower
  refine ⟨g, hgunit, hgnorm, ?_, ?_⟩
  · intro k
    simpa only [symmetricUnitFamilyLip, symmetricEvaluationIndex_card,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hglip k
  · intro x y c e hc hxy k
    apply hgphase x y (c ^ m) (by rw [norm_pow, hc, one_pow]) _ k
    intro a
    change symmetricEvaluation (fun i j => f i j x) a =
      c ^ m * symmetricEvaluation (fun i j => f i j y) a
    simp_rw [hxy]
    rw [symmetricEvaluation_const_mul]
    exact congrArg (fun z => c ^ m * z)
      (congrFun (symmetricEvaluation_permute (fun i j => f i j y) e) a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_invariant_unit_family {Γ I X : Type*} [Group Γ] [Fintype Γ]
    [Fintype I] [PseudoMetricSpace X] [MulAction Γ X]
    (f : I → X → ℂ) {K A : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j))
    (hunit : ∀ x, ∑ j, ‖f j x‖ ^ 2 = 1)
    (hact : ∀ a : Γ, LipschitzWith A (fun x : X => a • x)) :
    ∃ g : SymmetricEvaluationIndex (Fintype.card Γ) I → X → ℂ,
      (∀ x, ∑ k, ‖g k x‖ ^ 2 = 1) ∧ (∀ k x, ‖g k x‖ ≤ 1) ∧
      (∀ k, LipschitzWith
        (symmetricUnitFamilyLip (Fintype.card Γ) (Fintype.card I) (K * A)) (g k)) ∧
      (∀ a : Γ, ∀ k x, g k (a • x) = g k x) ∧
      ∀ x y (c : ℂ), ‖c‖ = 1 → (∀ a : Γ, ∀ j, f j (a • x) = c * f j (a • y)) →
        ∀ k, g k x = c ^ Fintype.card Γ * g k y := by
  classical
  let e := (Fintype.equivFin Γ).symm
  let F (i : Fin (Fintype.card Γ)) (j : I) (x : X) := f j (e i • x)
  obtain ⟨g, hgunit, hgnorm, hglip, hgphase⟩ := exists_symmetric_unit_family F
    (fun i j => (hf j).comp (hact (e i))) (fun i x => hunit (e i • x))
  refine ⟨g, hgunit, hgnorm, hglip, ?_, ?_⟩
  · intro a k x
    let ε : Equiv.Perm (Fin (Fintype.card Γ)) := e.trans ((Equiv.mulRight a).trans e.symm)
    have he (i) : e (ε i) = e i * a := by simp [ε]
    have h := hgphase (a • x) x 1 ε (by simp) (fun i j => by
      change f j (e i • (a • x)) = 1 * f j (e (ε i) • x)
      rw [he, mul_smul, one_mul]) k
    simpa only [one_pow, one_mul] using h
  · intro x y c hc hxy k
    exact hgphase x y c (Equiv.refl _) hc (fun i j => hxy (e i) j) k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def productMetricBound (d : ι → ℕ) : ℝ≥0 :=
  ∑ i, coordinateLipschitzBound (Fintype.card (Σ i, Fin (d i))) (d i) 1

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open scoped NNReal BigOperators

theorem productMetricBound_le {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) :
    (productMetricBound d : ℝ) ≤ 2 * p * (p ^ 2 + p + 1) := by
  have hdim : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p ^ 2 :=
    sigma_card_le_budget hp hι (fun i => by simpa only [Fintype.card_fin] using hd i)
  have hC (i : ι) : (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1 : ℝ) ≤
      2 * (p ^ 2 + p + 1) := by
    change ((Fintype.card (Σ j, Fin (d j)) : ℝ) + (d i : ℝ) + 1) * (1 + 1) ≤ _
    nlinarith [hd i]
  unfold productMetricBound
  rw [NNReal.coe_sum]
  calc
    _ ≤ ∑ _ : ι, 2 * (p ^ 2 + p + 1) := Finset.sum_le_sum (fun i _ => hC i)
    _ = (Fintype.card ι : ℝ) * (2 * (p ^ 2 + p + 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ p * (2 * (p ^ 2 + p + 1)) := mul_le_mul_of_nonneg_right hι (by positivity)
    _ = _ := by ring

theorem productMetricBound_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) :
    (productMetricBound d : ℝ) ≤ Real.exp ((p + 4) ^ 4) := by
  have hpoly : 2 * p * (p ^ 2 + p + 1) ≤ (p + 4) ^ 4 := by
    nlinarith [sq_nonneg (p ^ 2), mul_nonneg hp (sq_nonneg p)]
  apply (productMetricBound_le d hp hι hd).trans
  exact hpoly.trans (by linarith [Real.add_one_le_exp ((p + 4) ^ 4)])

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricSquarefreeMonotonicity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem tensorVector_unit {σ I : Type*} [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hunit : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (n : ℕ) (x : σ → ℤ) :
    ∑ a : Fin n → I, ‖tensorVector f n a x‖ ^ 2 = 1 := by
  simp only [tensorVector, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ _j : Fin n, ∑ i : I, ‖f i x‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [hunit, Finset.prod_const_one]

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

def coordinateSplitDownset (s : ℕ) (i : σ) (b : Bool) : Set (σ →₀ ℕ) :=
  {a | ∀ j, a j ≤ coordinateSplitBound s i b j}

theorem coordinateSplitBound_le (s : ℕ) (i : σ) (b : Bool) :
    coordinateSplitBound s i b ≤ fun _ => s := by
  intro j
  cases b <;> by_cases h : j = i <;> simp [coordinateSplitBound, h]

theorem coordinateSplitDownset_lower (s : ℕ) (i : σ) (b : Bool) :
    IsLowerSet (coordinateSplitDownset s i b) :=
  fun _ _ hab hb j => (hab j).trans (hb j)

theorem coordinateSplitDownset_covers [Fintype σ] (s : ℕ) (i : σ) (a : σ →₀ ℕ)
    (ha : (∑ j, a j) ≤ s) :
    a ∈ coordinateSplitDownset s i false ∪ coordinateSplitDownset s i true := by
  have hall (j : σ) : a j ≤ s :=
    (Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ j)).trans ha
  by_cases hi : a i ≤ s - 1
  · right
    intro j
    by_cases hj : j = i
    · subst j
      simpa [coordinateSplitBound] using hi
    · simpa [coordinateSplitBound, hj] using hall j
  · left
    intro j
    by_cases hj : j = i
    · subst j
      simpa [coordinateSplitBound] using hall i
    · have htwo : a i + a j ≤ ∑ k, a k := by
        calc
          a i + a j = ∑ k ∈ ({i, j} : Finset σ), a k := by simp [Ne.symm hj]
          _ ≤ ∑ k, a k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hz : a j = 0 := by omega
      simp [coordinateSplitBound, hj, hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3

def rankCoordinateTuple {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (t : ZMod N × ZMod N × ZMod N) : (Σ _ : Fin 4, ι) → ℝ :=
  fun j => β (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1)) j.2

theorem rankCoordinateTuple_first12 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (a b h : ZMod N) (i : ι) : rankCoordinateTuple β (b - h, b, a) ⟨0, i⟩ = β h i := by
  simp [rankCoordinateTuple, rankQuadrupleParameters]

theorem rankCoordinateTuple_first13 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (c d h : ZMod N) (i : ι) :
    rankCoordinateTuple β (c - d, h + (c - d), c) ⟨0, i⟩ = β h i := by
  simp [rankCoordinateTuple, rankQuadrupleParameters]

theorem rankCoordinateTuple_fixed12 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (a b h h₀ : ZMod N) (j : Σ _ : ({1, 2} : Finset (Fin 4)), ι) :
    rankCoordinateTuple β (b - h, b, a) ⟨j.1, j.2⟩ =
      rankCoordinateTuple β (b - h₀, b, a) ⟨j.1, j.2⟩ := by
  have hj := j.1.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with hj | hj <;> simp [rankCoordinateTuple, rankQuadrupleParameters, hj]

theorem rankCoordinateTuple_fixed13 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (c d h h₀ : ZMod N) (j : Σ _ : ({1, 3} : Finset (Fin 4)), ι) :
    rankCoordinateTuple β (c - d, h + (c - d), c) ⟨j.1, j.2⟩ =
      rankCoordinateTuple β (c - d, h₀ + (c - d), c) ⟨j.1, j.2⟩ := by
  have hj := j.1.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with hj | hj <;> simp [rankCoordinateTuple, rankQuadrupleParameters, hj]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateEstimates
namespace OAI

section

namespace Erdos3

def horizontalCoordinateBudget (p : ℝ) : ℝ :=
  p + p * (refiltrationCoordinateBudget p + 1 + (p + 3) ^ 7)

theorem horizontalCoordinateBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ horizontalCoordinateBudget p := by
  have h := refiltrationCoordinateBudget_nonneg hp
  unfold horizontalCoordinateBudget
  positivity

theorem horizontalCoordinateHeight_bound {p : ℝ} (hp : 0 ≤ p)
    (n H K : ℕ) (hn : (n : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (refiltrationCoordinateBudget p + 1))
    (hK : (K : ℝ) ≤ Real.exp ((p + 3) ^ 7)) :
    (((n + 1) * (H * K) ^ n : ℕ) : ℝ) ≤ Real.exp (horizontalCoordinateBudget p) := by
  have hcount : (n : ℝ) + 1 ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hsum : 0 ≤ refiltrationCoordinateBudget p + 1 + (p + 3) ^ 7 := by
    have h := refiltrationCoordinateBudget_nonneg hp
    positivity
  calc
    _ ≤ Real.exp p * (Real.exp (refiltrationCoordinateBudget p + 1) *
        Real.exp ((p + 3) ^ 7)) ^ n := by
      push_cast
      gcongr
    _ = Real.exp (p + (n : ℝ) * (refiltrationCoordinateBudget p + 1 + (p + 3) ^ 7)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_right hn hsum))

end Erdos3

end

section

namespace Erdos3

def nativeCoordinateBaseBudget (s : ℕ) (P : ℝ) : ℝ :=
  4 * P + (P + 3) ^ 7 + horizontalCoordinateBudget P +
    (s : ℝ) * P + (P + 3) ^ 2 + 4

def nativeCoordinateInputBudget (s : ℕ) (P : ℝ) : ℝ :=
  nativeCoordinateBaseBudget s P + (nativeCoordinateBaseBudget s P + 2) ^ 3 + P + 2

noncomputable def nativeDependentBudget (s : ℕ) (P : ℝ) : ℝ :=
  let Z := rankDependentInputBudget (nativeCoordinateInputBudget s P)
  Z + sparseGeneratorBudget Z

theorem nativeCoordinateBaseBudget_bounds (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ nativeCoordinateBaseBudget s P ∧ 4 * P ≤ nativeCoordinateBaseBudget s P ∧
      P ≤ nativeCoordinateBaseBudget s P ∧ (P + 3) ^ 7 + 1 ≤ nativeCoordinateBaseBudget s P ∧
      horizontalCoordinateBudget P + 1 ≤ nativeCoordinateBaseBudget s P ∧
      (P + 3) ^ 2 + (s : ℝ) * P ≤ nativeCoordinateBaseBudget s P := by
  have hH := horizontalCoordinateBudget_nonneg hP
  have h₇ : 0 ≤ (P + 3) ^ 7 := by positivity
  have h₂ : 0 ≤ (P + 3) ^ 2 := sq_nonneg _
  have hs : 0 ≤ (s : ℝ) * P := mul_nonneg (Nat.cast_nonneg s) hP
  unfold nativeCoordinateBaseBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
namespace OAI

section

namespace Erdos3

noncomputable def coefficientSpaceInputBudget (p : ℝ) : ℝ :=
  p + 4 * p + horizontalCoordinateBudget p + (p + 3) ^ 7 + 1

noncomputable def coefficientSpaceBasisBudget (p : ℝ) : ℝ :=
  let a := coefficientSpaceInputBudget p
  preimageBasisBudget (a + (a + 2) ^ 4 + dependentCoordinateBudget a)

end Erdos3

end

end OAI
end


