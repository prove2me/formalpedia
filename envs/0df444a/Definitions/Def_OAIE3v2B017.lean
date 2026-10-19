-- Prove2me | Definitions.Def_OAIE3v2B017
-- name    : OAIE3v2B017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:13.318445+00:00
-- url     : https://prove2.me/theorems/ef894d98-9f39-40fc-8290-78dd5fa0e7e4
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 18 of 311
-- statement:
--   Definitions bundle 18 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CandidateFrontSourceLossBudget.lean`, `Dynamics/ComparisonEquivalenceBudget.lean`, `Dynamics/SharedRefinementBudget.lean`, `Dynamics/SparseGeneratorBudget.lean`, `Estimates/CommonCoefficientFourAnnihilators.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/FiniteSeriesCoefficientBounds.lean`, `Estimates/FourBalancedRelations.lean`, `Estimates/GroupReductionFactors.lean`, `Estimates/ImageCosetReconstruction.lean`, `Estimates/InteriorIntervalCutoff.lean`, `Estimates/LipschitzLocalLifts.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeLocalPivotVerticalPartners.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/RationalImageIntersections.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RealFiniteZeroExtension.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/SharedFreeRoundingThreshold.lean`, `Fourier/CrossRowCharacterDifference.lean`, `Geometry/CoordinateSupNorm.lean`, `Geometry/NativeCoordinateEstimates.lean`, `Lattices/IntegerIntervalOverlap.lean`, `Linear/FiniteSpanRounding.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/RationalMatrixSeparation.lean`, `Linear/SpanKernelGenerators.lean`, `Linear/WeightedFlagBasis.lean`, `Nilpotent/BCHUniformQuotientCharts.lean`, `Probability/RoundedModelDensityBudget.lean`, `Probability/ShiftedProductCoordinateLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
namespace OAI

section

namespace Erdos3

theorem powerCover_index_allowance_le_exp (l m d : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) (hd : (d : ℝ) ≤ p) :
    (((l * m) ^ d : ℕ) : ℝ) ≤ Real.exp (2 * p ^ 2) := by
  have hprod : (l : ℝ) * m ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hl hm (by positivity) (by positivity)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
  rw [Nat.cast_pow, Nat.cast_mul]
  calc
    _ ≤ (Real.exp (2 * p)) ^ d := pow_le_pow_left₀ (by positivity) hprod d
    _ = Real.exp ((d : ℝ) * (2 * p)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2 * p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

theorem powerCover_grid_allowance_le_exp (l m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    (((l * m) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp p :=
      mul_le_mul (mul_le_mul hl hm (by positivity) (by positivity)) hl
        (by positivity) (by positivity)
    _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

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

theorem factorsThrough_target_cosets (φ : H →* G) (Γ : Subgroup H) (Λ : Subgroup G)
    (hcover : Λ ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    Function.FactorsThrough f (fun x => (QuotientGroup.mk (φ x) : G ⧸ Λ)) := by
  intro x y hxy
  have hmem : (φ x)⁻¹ * φ y ∈ Λ := QuotientGroup.eq.mp hxy
  obtain ⟨γ, hγ, hφγ⟩ := hcover hmem
  let k := y * γ⁻¹ * x⁻¹
  have hk : k ∈ φ.ker := by
    change φ k = 1
    simp only [k, map_mul, map_inv, hφγ, mul_inv_rev, inv_inv]
    group
  have hdecomp : k * (x * γ) = y := by
    dsimp [k]
    group
  calc
    f x = f (x * γ) := (hΓ γ hγ x).symm
    _ = f (k * (x * γ)) := (hker k hk (x * γ)).symm
    _ = f y := congrArg f hdecomp

theorem exists_unique_quotient_reconstruction (φ : H →* G) (hφ : Function.Surjective φ)
    (Γ : Subgroup H) (Λ : Subgroup G) (hcover : Λ ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    ∃! F : G ⧸ Λ → A, ∀ x, F (QuotientGroup.mk (φ x)) = f x := by
  let π : H → G ⧸ Λ := fun x => QuotientGroup.mk (φ x)
  have hπ : Function.Surjective π := QuotientGroup.mk_surjective.comp hφ
  have hf := factorsThrough_target_cosets φ Γ Λ hcover f hker hΓ
  let F : G ⧸ Λ → A := fun y => f (Function.surjInv hπ y)
  have hF (x : H) : F (π x) = f x := hf (Function.surjInv_eq hπ (π x))
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  funext y
  obtain ⟨x, rfl⟩ := hπ y
  exact (hF' x).trans (hF x).symm

theorem exists_unique_observable_reconstruction (φ : H →* G) (hφ : Function.Surjective φ)
    (Γ : Subgroup H) (Λ : Subgroup G) (hcover : Λ ≤ Γ.map φ) (f : H ⧸ Γ → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (QuotientGroup.mk (k * x)) = f (QuotientGroup.mk x)) :
    ∃! F : G ⧸ Λ → A, ∀ x, F (QuotientGroup.mk (φ x)) = f (QuotientGroup.mk x) := by
  apply exists_unique_quotient_reconstruction φ hφ Γ Λ hcover (fun x => f (QuotientGroup.mk x)) hker
  intro γ hγ x
  apply congrArg f
  apply QuotientGroup.eq.mpr
  simpa only [mul_inv_rev, inv_mul_cancel_left, inv_mul_cancel_right] using Γ.inv_mem hγ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LipschitzLocalLifts
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y E : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [NormedAddCommGroup E]

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] in
theorem reconstruction_norm_le (π : X → Y) (hπ : Function.Surjective π)
    (f : X → E) (F : Y → E) (hF : ∀ x, F (π x) = f x) {B : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ B) : ∀ y, ‖F y‖ ≤ B := by
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  rw [hF]
  exact hbound x

theorem lipschitz_reconstruction_of_local_lifts (π : X → Y) (hπ : Function.Surjective π)
    (f : X → E) (F : Y → E) (hF : ∀ x, F (π x) = f x)
    (L K B δ : ℝ≥0) (hδ : 0 < δ) (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlift : ∀ y z : Y, dist y z < δ →
      ∃ x x' : X, π x = y ∧ π x' = z ∧ dist x x' ≤ K * dist y z) :
    LipschitzWith (max (L * K) (2 * B / δ)) F := by
  have hFbound := reconstruction_norm_le π hπ f F hF hbound
  have hδr : (0 : ℝ) < δ := hδ
  apply LipschitzWith.of_dist_le_mul
  intro y z
  by_cases hyz : dist y z < δ
  · obtain ⟨x, x', hx, hx', hdist⟩ := hlift y z hyz
    rw [← hx, ← hx', hF, hF]
    calc
      dist (f x) (f x') ≤ L * dist x x' := hf.dist_le_mul x x'
      _ ≤ (L : ℝ) * (K * dist (π x) (π x')) := by
        rw [hx, hx']
        exact mul_le_mul_of_nonneg_left hdist L.coe_nonneg
      _ = ((L * K : ℝ≥0) : ℝ) * dist (π x) (π x') := by simp only [NNReal.coe_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left (L * K) (2 * B / δ)) dist_nonneg
  · have hdist : (δ : ℝ) ≤ dist y z := le_of_not_gt hyz
    calc
      dist (F y) (F z) ≤ ‖F y‖ + ‖F z‖ := dist_le_norm_add_norm _ _
      _ ≤ (2 : ℝ) * B := by linarith [hFbound y, hFbound z]
      _ = (2 * (B : ℝ) / δ) * δ := (div_mul_cancel₀ _ hδr.ne').symm
      _ ≤ (2 * (B : ℝ) / δ) * dist y z := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = ((2 * B / δ : ℝ≥0) : ℝ) * dist y z := by simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right (L * K) (2 * B / δ)) dist_nonneg

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupReductionFactors
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G]

theorem exists_representative_factors_of_reductions (Γ : Subgroup G)
    (H : ℕ → Subgroup G) (s : ℕ) (P : G → Prop)
    (hzero : H 0 = ⊤) (hterminal : H s = ⊥)
    (hstep : ∀ i < s, ∀ g ∈ H i,
      ∃ r, P r ∧ ∃ w ∈ Γ, r⁻¹ * g * w⁻¹ ∈ H (i + 1)) :
    ∀ g : G, ∃ rs : List G, rs.length = s ∧ (∀ r ∈ rs, P r) ∧
      ∃ γ ∈ Γ, g = rs.prod * γ := by
  have haux (n : ℕ) : ∀ i, i + n = s → ∀ g ∈ H i,
      ∃ rs : List G, rs.length = n ∧ (∀ r ∈ rs, P r) ∧
        ∃ γ ∈ Γ, g = rs.prod * γ := by
    induction n with
    | zero =>
      intro i hi g hg
      have his : i = s := by omega
      subst i
      have hg1 : g = 1 := by simpa only [hterminal, Subgroup.mem_bot] using hg
      exact ⟨[], rfl, by simp, 1, Γ.one_mem, by simpa using hg1⟩
    | succ n ih =>
      intro i hi g hg
      obtain ⟨r, hr, w, hw, hrem⟩ := hstep i (by omega) g hg
      obtain ⟨rs, hlen, hP, γ, hγ, heq⟩ := ih (i + 1) (by omega) _ hrem
      refine ⟨r :: rs, by simp [hlen], ?_, γ * w, Γ.mul_mem hγ hw, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hr
        · exact hP a ha
      · calc
          g = r * (r⁻¹ * g * w⁻¹) * w := by group
          _ = (r :: rs).prod * (γ * w) := by rw [heq, List.prod_cons]; group
  intro g
  exact haux s 0 (by omega) g (by simp [hzero])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateSupNorm
namespace OAI

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [Fintype κ] in
theorem coordinateLinearMap_apply_sum (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (v : ι → ℝ) (k : κ) :
    A v k = ∑ i, A (Pi.single i 1) k * v i := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one, LinearMap.sum_single_apply]
  calc
    A v k = A (∑ i, v i • Pi.single i (1 : ℝ)) k := congrArg (fun w => A w k) hv
    _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteSpanRounding
namespace OAI

section

namespace Erdos3

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

def boundedSpanCell (v : ι → V) (c : ℝ) : Set V :=
  (fun t : ι → ℝ => ∑ i, t i • v i) '' Set.univ.pi (fun _ => Set.Icc 0 c)

theorem boundedSpanCell_subset_span (v : ι → V) (c : ℝ) :
    boundedSpanCell v c ⊆ Submodule.span ℝ (Set.range v) := by
  rintro _ ⟨t, _, rfl⟩
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem exists_bounded_span_remainder (v : ι → V) (c : ℝ) (hc : 0 < c)
    (x : V) (hx : x ∈ Submodule.span ℝ (Set.range v)) :
    ∃ r ∈ boundedSpanCell v c, ∃ z : ι → ℤ, x = r + ∑ i, ((z i : ℝ) * c) • v i := by
  classical
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  let z : ι → ℤ := fun i => ⌊t i / c⌋
  let u : ι → ℝ := fun i => t i - (z i : ℝ) * c
  refine ⟨∑ i, u i • v i, ⟨u, ?_, rfl⟩, z, ?_⟩
  · intro i _
    exact ⟨Int.sub_floor_div_mul_nonneg (t i) hc, (Int.sub_floor_div_mul_lt (t i) hc).le⟩
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_smul]
    congr 1
    dsimp [u]
    ring

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem isCompact_boundedSpanCell (v : ι → V) (c : ℝ) : IsCompact (boundedSpanCell v c) := by
  apply (isCompact_univ_pi (fun _ : ι => isCompact_Icc)).image
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanKernelGenerators
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem range_kernel_projection (A : Matrix ι κ ℚ) (S : Matrix κ ι ℚ)
    (hS : A * S = 1) :
    LinearMap.range (1 - S * A).mulVecLin = LinearMap.ker A.mulVecLin := by
  have hzero : A * (1 - S * A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hS, Matrix.one_mul, sub_self]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change A *ᵥ ((1 - S * A) *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
  · intro hy
    change A *ᵥ y = 0 at hy
    refine ⟨y, ?_⟩
    change (1 - S * A) *ᵥ y = y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hy, Matrix.mulVec_zero, sub_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalImageIntersections
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

section Coordinates

variable [DecidableEq κ]

noncomputable def rationalQuotientEquiv (D : Matrix ι κ ℚ)
    (K : Submodule ℚ (κ → ℚ)) (hker : LinearMap.ker D.mulVecLin = K)
    (hsurj : Function.Surjective D.mulVec) :
    ((κ → ℚ) ⧸ K) ≃ₗ[ℚ] (ι → ℚ) :=
  (Submodule.quotEquivOfEq K (LinearMap.ker D.mulVecLin) hker.symm).trans
    (D.mulVecLin.quotKerEquivOfSurjective hsurj)

end Coordinates

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalMatrixSeparation
namespace OAI

section

namespace Erdos3

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

theorem boundedSpanCell_linear_bound (v : ι → V) (f : V →ₗ[ℝ] ℝ) {c H : ℝ}
    (hc : 0 ≤ c) (hv : ∀ i, |f (v i)| ≤ H) {x : V} (hx : x ∈ boundedSpanCell v c) :
    |f x| ≤ Fintype.card ι * c * H := by
  classical
  obtain ⟨t, ht, rfl⟩ := hx
  simp only [map_sum, map_smul, smul_eq_mul]
  calc
    _ ≤ ∑ i, |t i * f (v i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, c * H := by
      apply Finset.sum_le_sum
      intro i _
      have hi := ht i (Set.mem_univ i)
      rw [abs_mul, abs_of_nonneg hi.1]
      exact mul_le_mul hi.2 (hv i) (abs_nonneg _) hc
    _ = _ := by simp [mul_assoc]

theorem boundedSpanCell_coordinate_bound (e : Module.Basis κ ℝ V) (v : ι → V) {c H : ℝ}
    (hc : 0 ≤ c) (hv : ∀ i j, |e.repr (v i) j| ≤ H) {x : V}
    (hx : x ∈ boundedSpanCell v c) (j : κ) :
    |e.repr x j| ≤ Fintype.card ι * c * H :=
  boundedSpanCell_linear_bound v (e.coord j) hc (fun i => hv i j) hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L]

omit [DecidableEq ι] in
theorem coordinate_span_matrix_range {η : Type*} [Fintype η]
    (e : Basis ι ℚ L) (v : η → L) (I : Submodule ℚ L)
    (hspan : Submodule.span ℚ (Set.range v) = I) :
    LinearMap.range (Matrix.mulVecLin (show Matrix ι η ℚ from fun i j => e.repr (v j) i)) =
      I.map e.equivFun.toLinearMap := by
  rw [Matrix.range_mulVecLin, ← hspan, Submodule.map_span, ← Set.range_comp]
  rfl

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem lie_subalgebra_finrank_le (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L) :
    Module.finrank ℚ K ≤ Fintype.card ι := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  have h := LinearMap.finrank_le_finrank_of_injective (f := K.incl.toLinearMap)
    (fun _ _ h => Subtype.ext h)
  simpa only [Module.finrank_eq_card_basis e] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

namespace Erdos3

noncomputable def cyclicCutNeighborhood (N : ℕ) [NeZero N] (a : ℤ) (δ : ℝ) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter (fun x => |(x.val : ℝ) - a| ≤ δ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open scoped Matrix

noncomputable def coefficientWeight {J : Type*} (f : (J → ℝ) → ℝ)
    (S : J → ℝ) (z : J → ℤ) : ℝ := f (fun j => (z j : ℝ) / S j)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

omit [Fintype ι] [Fintype κ] in

theorem linearMap_baseChange_basis (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (i : κ) (j : ι) :
    (f.baseChange ℝ).repr (φ.baseChange ℝ ((e.baseChange ℝ) j)) i =
      (f.repr (φ (e j)) i : ℝ) := by
  simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

theorem linearMap_baseChange_rightInverse (φ : L →ₗ[ℚ] M) (σ : M →ₗ[ℚ] L)
    (hσ : Function.RightInverse σ φ) :
    Function.RightInverse (σ.baseChange ℝ) (φ.baseChange ℝ) := by
  have heq : φ.comp σ = LinearMap.id := LinearMap.ext hσ
  have heqR := congrArg (fun T : M →ₗ[ℚ] M => T.baseChange ℝ) heq
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at heqR
  intro x
  exact DFunLike.congr_fun heqR x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedFlagBasis
namespace OAI

section

namespace Erdos3

open Module

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem span_image_inl_of_basis_extension
    {P R : Submodule K V} (hRP : R ≤ P) {κ μ : Type*}
    (bP : Basis κ K P) (bV : Basis (κ ⊕ μ) K V)
    (hext : ∀ i, bV (Sum.inl i) = (bP i : V)) (s : Set κ)
    (hspan : R.comap P.subtype = Submodule.span K (bP '' s)) :
    R = Submodule.span K (bV '' (Sum.inl '' s)) := by
  have himage : P.subtype '' (bP '' s) = bV '' (Sum.inl '' s) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, ⟨i, hi, rfl⟩, hext i⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨bP i, ⟨i, hi, rfl⟩, (hext i).symm⟩
  calc
    R = (R.comap P.subtype).map P.subtype :=
      (Submodule.map_comap_eq_self (by
        simpa [Submodule.range_subtype] using hRP)).symm
    _ = (Submodule.span K (bP '' s)).map P.subtype := by rw [hspan]
    _ = Submodule.span K (P.subtype '' (bP '' s)) := by rw [Submodule.map_span]
    _ = Submodule.span K (bV '' (Sum.inl '' s)) := by rw [himage]

theorem span_range_inl_complement_basis {P Q : Submodule K V} (hPQ : IsCompl P Q)
    {κ μ : Type*} (bP : Basis κ K P) (bQ : Basis μ K Q) :
    let bV := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
    P = Submodule.span K (bV '' Set.range Sum.inl) := by
  classical
  let bV := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
  apply le_antisymm
  · intro x hx
    have hxp : (⟨x, hx⟩ : P) ∈ Submodule.span K (Set.range bP) := by
      rw [bP.span_eq]
      exact Submodule.mem_top
    exact Submodule.span_induction (R := K) (s := Set.range bP)
      (p := fun y _ => (y : V) ∈ Submodule.span K (bV '' Set.range Sum.inl))
      (fun y hy => by
        obtain ⟨i, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨Sum.inl i, ⟨i, rfl⟩, ?_⟩
        simp [bV])
      (Submodule.zero_mem _)
      (fun _ _ _ _ hy hz => Submodule.add_mem _ hy hz)
      (fun a _ _ hy => Submodule.smul_mem _ a hy) hxp
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp

theorem exists_basis_with_nested_supports (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (P : Fin n → Submodule K V), Antitone P →
      ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ K V) (s : Fin n → Set κ),
        Antitone s ∧ ∀ i, P i = Submodule.span K (b '' s i) := by
  induction n with
  | zero =>
      intro V _ _ _ P _
      refine ⟨Fin (finrank K V), inferInstance, finBasis K V, Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro V _ _ _ P hanti
      classical
      let P₀ : Submodule K V := P 0
      let tail : Fin n → Submodule K P₀ := fun i => (P i.succ).comap P₀.subtype
      have htail : Antitone tail := by
        intro i j hij
        apply Submodule.comap_mono
        exact hanti (by simpa using hij)
      obtain ⟨κ, instκ, bP, sP, hsP, hbP⟩ := ih tail htail
      let : Fintype κ := instκ
      obtain ⟨Q, hPQ⟩ := Submodule.exists_isCompl P₀
      let bQ := finBasis K Q
      let e : (P₀ × Q) ≃ₗ[K] V := P₀.prodEquivOfIsCompl Q hPQ
      let b : Basis (κ ⊕ Fin (finrank K Q)) K V := (bP.prod bQ).map e
      let s : Fin (n + 1) → Set (κ ⊕ Fin (finrank K Q)) :=
        Fin.cases (Set.range Sum.inl) (fun j => Sum.inl '' sP j)
      refine ⟨κ ⊕ Fin (finrank K Q), inferInstance, b, s, ?_, ?_⟩
      · intro i j hij
        obtain rfl | ⟨i', rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact fun _ hx => hx
          · rintro x ⟨k, _, rfl⟩
            exact Set.mem_range.mpr ⟨k, rfl⟩
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim ((not_le_of_gt (Fin.succ_pos i')) hij)
          · exact Set.image_mono (hsP (by simpa using hij))
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact span_range_inl_complement_basis hPQ bP bQ
        · apply span_image_inl_of_basis_extension
            (P := P₀) (R := P j.succ) (hanti (Fin.zero_le j.succ))
            bP b (fun k => by simp [b, e]) (sP j)
          simpa [tail, P₀] using hbP j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSeriesCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

def finiteSeriesWeight (s : ℕ) (i : Fin 2 × Fin (s + 1)) : ℚ :=
  if i.1 = 0 then (i.2.val.factorial : ℚ)⁻¹ else (-1 : ℚ) ^ (i.2.val + 1) / i.2.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3

open Module

theorem bch_box_expression_le_exp (s a C n d : ℕ) (hC : 2 ≤ C) {p : ℝ}
    (hp : 0 ≤ p) (hn : n ≤ s) (hd : (d : ℝ) ≤ p) :
    (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) *
      Real.exp ((p + s + C) ^ C) * (Real.exp ((p + 2) ^ a)) ^ s ≤
        Real.exp ((p + (C + 3 * s + a + 10)) ^ (C + 3 * s + a + 10)) := by
  let D := C + 3 * s + a + 10
  let t := p + D
  have hD : 3 ≤ D := by dsimp [D]; omega
  have hD' : (3 : ℝ) ≤ D := by exact_mod_cast hD
  have ht : 3 ≤ t := by dsimp [t]; linarith
  have hs : (s : ℝ) + 1 ≤ t := by
    have h : s + 1 ≤ D := by dsimp [D]; omega
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    dsimp [t]
    push_cast at h'
    linarith
  have hp2 : p + 2 ≤ t := by dsimp [t]; linarith
  have hn' : (n : ℝ) ≤ t := (Nat.cast_le.mpr hn).trans (by linarith)
  have hd' : (d : ℝ) ≤ t := hd.trans (by linarith)
  have hbase : ((n * d + 1 : ℕ) : ℝ) ≤ t ^ 3 := by
    have hnd := mul_le_mul hn' hd' (Nat.cast_nonneg d) (by linarith : 0 ≤ t)
    push_cast
    nlinarith [sq_nonneg (t - 1)]
  have hcount : (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) ≤ t ^ (3 * s + 1) := by
    push_cast at hbase
    push_cast
    calc
      _ ≤ t * (t ^ 3) ^ s :=
        mul_le_mul hs (pow_le_pow_left₀ (by positivity) hbase s) (by positivity) (by linarith)
      _ = t ^ (3 * s + 1) := by rw [← pow_mul, pow_succ']
  have hcount' : (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) ≤ Real.exp (t ^ (D - 1)) := by
    have he : 3 * s + 1 ≤ D - 1 := by dsimp [D]; omega
    apply hcount.trans
    apply (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) he).trans
    linarith [Real.add_one_le_exp (t ^ (D - 1))]
  have hshift : p + s + C ≤ t := by
    have h : s + C ≤ D := by dsimp [D]; omega
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    dsimp [t]
    push_cast at h'
    linarith
  have hcoef : Real.exp ((p + s + C) ^ C) ≤ Real.exp (t ^ (D - 1)) := by
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_left₀ (by positivity) hshift C).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega)
  have hinput : (Real.exp ((p + 2) ^ a)) ^ s ≤ Real.exp (t ^ (D - 1)) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ t * t ^ a :=
        mul_le_mul (by linarith : (s : ℝ) ≤ t)
          (pow_le_pow_left₀ (by linarith) hp2 a) (by positivity) (by linarith)
      _ = t ^ (a + 1) := (pow_succ' _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega)
  calc
    _ ≤ Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) :=
      mul_le_mul (mul_le_mul hcount' hcoef (by positivity) (by positivity)) hinput
        (by positivity) (by positivity)
    _ = Real.exp (3 * t ^ (D - 1)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t ^ D) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ t * t ^ (D - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = t ^ D := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ D)]
    _ = _ := by simp [t, D]

end Erdos3

end

section

namespace Erdos3

open Module

theorem bch_triple_box_expression_le_exp (s a C d : ℕ) (hC : 2 ≤ C) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (((s + 1) * (3 * d + 1) ^ s : ℕ) : ℝ) * Real.exp ((p + 3 + C) ^ C) *
      (Real.exp ((p + 2) ^ a)) ^ s ≤
      Real.exp ((p + (C + 3 * (s + 3) + a + 10)) ^ (C + 3 * (s + 3) + a + 10)) := by
  have hcount : (s + 1) * (3 * d + 1) ^ s ≤ (s + 3 + 1) * (3 * d + 1) ^ (s + 3) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hcoef : Real.exp ((p + 3 + C) ^ C) ≤ Real.exp ((p + (s + 3) + C) ^ C) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hinput : (Real.exp ((p + 2) ^ a)) ^ s ≤ (Real.exp ((p + 2) ^ a)) ^ (s + 3) :=
    pow_le_pow_right₀ (Real.one_le_exp (by positivity)) (by omega)
  apply le_trans (mul_le_mul (mul_le_mul (Nat.cast_le.mpr hcount) hcoef
    (by positivity) (by positivity)) hinput (by positivity) (by positivity))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    bch_box_expression_le_exp (s + 3) a C 3 d hC hp (by omega) hd

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

def fourAlternatingMap : (Fin 4 → V) →ₗ[R] V :=
  (LinearMap.proj 0 : (Fin 4 → V) →ₗ[R] V) + LinearMap.proj 1 - LinearMap.proj 2 - LinearMap.proj 3

def fourCommonModulo (C D : Submodule R V) : Submodule R (Fin 4 → V) :=
  Submodule.pi Set.univ (fun _ => C) ⊓
    ⨅ k : Fin 4, D.comap ((LinearMap.proj k : (Fin 4 → V) →ₗ[R] V) - LinearMap.proj 0)

def fourBalancedDependent (D : Submodule R V) : Submodule R (Fin 4 → V) :=
  Submodule.pi Set.univ (fun _ => D) ⊓ LinearMap.ker (fourAlternatingMap (R := R))

def fourRefinedRelation (C D : Submodule R V) (K : Submodule R (Fin 4 → V)) :
    Submodule R (Fin 4 → V) :=
  (K ⊓ fourCommonModulo C D) ⊔ fourBalancedDependent D

def fourPetalSpace (D : Submodule R V) (K : Submodule R (Fin 4 → V)) : Submodule R V :=
  D ⊓ K.comap (LinearMap.single R (fun _ : Fin 4 => V) 0)

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

def petalComparisonSpace (C P K : Submodule R V) : Submodule R (Fin 2 → V) :=
  (C ⊔ K).comap (LinearMap.proj (1 : Fin 2) : (Fin 2 → V) →ₗ[R] V) ⊓
    (P ⊔ K).comap ((LinearMap.proj (0 : Fin 2) : (Fin 2 → V) →ₗ[R] V) -
      (LinearMap.proj (1 : Fin 2) : (Fin 2 → V) →ₗ[R] V))

end Algebra

open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

section Functional

variable {R L M : Type*} [CommRing R] [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M]

def pairDifferenceFunctional (η : L →ₗ[R] M) : (Fin 2 → L) →ₗ[R] M :=
  η.comp (LinearMap.proj (0 : Fin 2)) - η.comp (LinearMap.proj (1 : Fin 2))

theorem pairDifferenceFunctional_apply (η : L →ₗ[R] M) (z : Fin 2 → L) :
    pairDifferenceFunctional η z = η (z 0) - η (z 1) := rfl

end Functional

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def frozenRealSection {Z Ξ : Type*} (F : Z → Ξ → ℝ) (a : Option Ξ) (z : Z) : ℝ :=
  a.elim 0 (F z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SparseGeneratorBudget
namespace OAI

section

namespace Erdos3

noncomputable def sparseGeneratorBudget (p : ℝ) : ℝ := p + p * ((p + 2) ^ 7 + p)

theorem sparseGeneratorBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ sparseGeneratorBudget p := by
  unfold sparseGeneratorBudget
  positivity

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

noncomputable def preimageBasisBudget (p : ℝ) : ℝ :=
  sparseGeneratorBudget (p + (p + (p + 3) ^ 7 + 2) ^ 4 + 1)

theorem preimageBasisBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ preimageBasisBudget p := by
  apply sparseGeneratorBudget_nonneg
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def zeroExtendFinset {X : Type*} (S : Finset X) (f : X → ℂ) (x : X) : ℂ := by
  classical
  exact if x ∈ S then f x else 0

theorem expect_zeroExtendFinset {X : Type*} (A S : Finset X) (hSA : S ⊆ A) (f : X → ℂ) :
    (𝔼 x ∈ A, zeroExtendFinset S f x) =
      ((S.card : ℂ) / (A.card : ℂ)) * (𝔼 x ∈ S, f x) := by
  classical
  rw [Finset.expect_eq_sum_div_card]
  simp only [zeroExtendFinset, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSA]
  rw [← Finset.card_mul_expect S f]
  ring

theorem norm_expect_zeroExtendFinset {X : Type*} (A S : Finset X) (hSA : S ⊆ A) (f : X → ℂ) :
    ‖𝔼 x ∈ A, zeroExtendFinset S f x‖ =
      ((S.card : ℝ) / (A.card : ℝ)) * ‖𝔼 x ∈ S, f x‖ := by
  rw [expect_zeroExtendFinset A S hSA f, norm_mul, norm_div,
    Complex.norm_natCast, Complex.norm_natCast]

theorem zeroExtendFinset_mul_left {X : Type*} (S : Finset X) (f g : X → ℂ) (x : X) :
    f x * zeroExtendFinset S g x = zeroExtendFinset S (fun x => f x * g x) x := by
  classical
  by_cases hx : x ∈ S <;> simp [zeroExtendFinset, hx]

theorem zeroExtendFinset_mul_star {X : Type*} [DecidableEq X] (S T : Finset X) (f g : X → ℂ) (x : X) :
    zeroExtendFinset S f x * star (zeroExtendFinset T g x) =
      zeroExtendFinset (S ∩ T) (fun x => f x * star (g x)) x := by
  classical
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp [zeroExtendFinset, hs, ht]

theorem zeroExtendFinset_norm_le_one {X : Type*} (S : Finset X) (f : X → ℂ)
    (hf : ∀ x ∈ S, ‖f x‖ ≤ 1) (x : X) : ‖zeroExtendFinset S f x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ S
  · simpa [zeroExtendFinset, hx] using hf x hx
  · simp [zeroExtendFinset, hx]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def normalizedSquareLeftBudget (a b : ℕ) (p : ℝ) : ℝ :=
  (p + a + 2 + b) ^ b

theorem normalizedSquareLeftBudget_nonneg (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ normalizedSquareLeftBudget a b p := by
  unfold normalizedSquareLeftBudget
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerIntervalOverlap
namespace OAI

section

namespace Erdos3

theorem integerIco_intersection (c₁ l₁ c₂ l₂ N : ℕ)
    (hN₁ : c₁ + l₁ ≤ N) (hN₂ : c₂ + l₂ ≤ N)
    (hne : (Finset.Ico (c₁ : ℤ) (c₁ + l₁) ∩ Finset.Ico (c₂ : ℤ) (c₂ + l₂)).Nonempty) :
    ∃ c len : ℕ, 0 < len ∧ c + len ≤ N ∧ len ≤ l₁ ∧ len ≤ l₂ ∧
      Finset.Ico (c₁ : ℤ) (c₁ + l₁) ∩ Finset.Ico (c₂ : ℤ) (c₂ + l₂) =
        Finset.Ico (c : ℤ) (c + len) := by
  let c := max c₁ c₂
  let e := min (c₁ + l₁) (c₂ + l₂)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
  obtain ⟨hx₁₀, hx₁₁⟩ := Finset.mem_Ico.mp hx₁
  obtain ⟨hx₂₀, hx₂₁⟩ := Finset.mem_Ico.mp hx₂
  have hce : c < e := by dsimp [c, e]; omega
  have heq : c + (e - c) = e := by omega
  refine ⟨c, e - c, by omega, ?_, ?_, ?_, ?_⟩
  · dsimp [e] at heq
    omega
  · dsimp [c, e]
    omega
  · dsimp [c, e]
    omega
  · ext y
    simp only [Finset.mem_inter, Finset.mem_Ico]
    dsimp [c, e] at *
    omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeLocalPivotVerticalPartners
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_remove_normalization {X : Type*} (S : Finset X) (f g : X → ℂ)
    {b rho : ℝ} (hb : 0 ≤ b)
    (hcorr : rho ≤ ‖𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * g x‖) :
    rho ≤ ‖𝔼 x ∈ S, f x * g x‖ := by
  have hmean : (𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * g x) =
      (Real.exp (-b) : ℂ) * (𝔼 x ∈ S, f x * g x) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hcorr
  exact hcorr.trans (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateEstimates
namespace OAI

section

namespace Erdos3

def refiltrationCoordinateBudget (p : ℝ) : ℝ :=
  ((p + 1 + (p + 3) ^ 7 + 2) ^ 9 + p + 4) ^ 4

theorem refiltrationCoordinateBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ refiltrationCoordinateBudget p := by
  unfold refiltrationCoordinateBudget
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3.SubspaceFreeLift

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (S : Fin s → Submodule ℚ L)

abbrev Alphabet := Σ d : Fin s, Fin (finrank ℚ (S d))

def weight (x : Alphabet S) : ℕ := x.1.val + 1

theorem weight_pos (x : Alphabet S) : 0 < weight S x := Nat.succ_pos _

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.SubspaceFreeLift

open Module
open scoped TensorProduct

theorem alphabet_card_le {L : Type*} [LieRing L] [LieAlgebra ℚ L] [Module.Finite ℚ L]
    {s : ℕ} (S : Fin s → Submodule ℚ L) :
    Fintype.card (Alphabet S) ≤ s * finrank ℚ L := by
  change Fintype.card (Σ d : Fin s, Fin (finrank ℚ (S d))) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _d : Fin s, finrank ℚ L := Finset.sum_le_sum
      (fun d _ => by simpa only [Fintype.card_fin] using Submodule.finrank_le (S d))
    _ = _ := by simp

end Erdos3.SubspaceFreeLift

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

open Module

noncomputable def fourRefinementBasisBudget (p : ℝ) : ℝ :=
  p + preimageBasisBudget (4 * p)

noncomputable def fourRefinementAnnihilatorBudget (p : ℝ) : ℝ :=
  (4 * p + fourRefinementBasisBudget p + 3) ^ 7

theorem fourRefinementBasisBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ fourRefinementBasisBudget p :=
  add_nonneg hp (preimageBasisBudget_nonneg (by positivity))

theorem fourRefinementAnnihilatorBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ fourRefinementAnnihilatorBudget p := by
  have h := fourRefinementBasisBudget_nonneg hp
  unfold fourRefinementAnnihilatorBudget
  positivity

end Erdos3

end

section

namespace Erdos3

def coefficientFourHeightBudget (p : ℝ) : ℝ := p + refiltrationCoordinateBudget p + 2

theorem coefficientFourHeightBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ coefficientFourHeightBudget p := by
  have h := refiltrationCoordinateBudget_nonneg hp
  unfold coefficientFourHeightBudget
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedRefinementBudget
namespace OAI

section

namespace Erdos3

def sharedRefinementInputBudget (s : ℕ) (p : ℝ) : ℝ :=
  let B := (p + 2) ^ 3 + 2 * p
  p + coefficientFourHeightBudget B + ((B + 3) ^ 2 + (s : ℝ) * p) + ((p + 2) ^ 3 + p)

theorem sharedRefinementInputBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let B := (p + 2) ^ 3 + 2 * p
    let A := sharedRefinementInputBudget s p
    0 ≤ B ∧ p ≤ B ∧ 0 ≤ A ∧ p ≤ A ∧ coefficientFourHeightBudget B ≤ A ∧
      (B + 3) ^ 2 + (s : ℝ) * p ≤ A ∧ (p + 2) ^ 3 + p ≤ A := by
  intro B A
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpB : p ≤ B := by dsimp only [B]; nlinarith [sq_nonneg (p + 2)]
  have hH := coefficientFourHeightBudget_nonneg hB
  have hE : 0 ≤ (B + 3) ^ 2 + (s : ℝ) * p := by positivity
  have hL : 0 ≤ (p + 2) ^ 3 + p := by positivity
  have hA : A = p + coefficientFourHeightBudget B + ((B + 3) ^ 2 + (s : ℝ) * p) +
      ((p + 2) ^ 3 + p) := rfl
  refine ⟨hB, hpB, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold
namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeEquationInputBudget (s : ℕ) (q p : ℝ) : ℝ :=
  let z := 8 * sharedRefinementInputBudget s p + 1
  4 * p + (fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) + 1) +
    (z + ((z + 2) ^ 3 + (z + 2) ^ 36))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RoundedModelDensityBudget
namespace OAI

section

namespace Erdos3

noncomputable def roundedModelLogBudget (P : ℝ) (d : ℕ) : ℝ :=
  736 + 96 * max P 0 + 1504 * d

theorem roundedModelLogBudget_nonneg (P : ℝ) (d : ℕ) : 0 ≤ roundedModelLogBudget P d := by
  unfold roundedModelLogBudget
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

def mixedCornerCount (s : ℕ) : ℕ := 2 ^ (s + 3) - 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CrossRowCharacterDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def characterCrossRow (f g : G → ℂ) (χ : G → AddChar G ℂ) (h n : G) : ℂ :=
  (f n * star (g (n + h))) * star (χ h n)

end Erdos3

end

end OAI
end


