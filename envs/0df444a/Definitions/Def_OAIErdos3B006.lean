-- Prove2me | Definitions.Def_OAIErdos3B006
-- name    : OAIErdos3B006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T10:08:15.496497+00:00
-- url     : https://prove2.me/theorems/5e860b56-cb41-421c-91ec-84c92169b1fd
-- title:
--   OpenAI Erdős-3 split, definitions bundle 7 of 88
-- statement:
--   Definitions bundle 7 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B005`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 7 available.
--
--   Modules: `OAI.Erdos3.DualLieAlgebra`, `OAI.Erdos3.FiniteProbabilityWeights.complexMean_finitePushforward`, `OAI.Erdos3.FiniteProbabilityWeights.finitePushforward`, `OAI.Erdos3.FiniteProbabilityWeights.mean_finitePushforward`, `OAI.Erdos3.FiniteProbabilityWeights.uniform_finitePushforward_mean`, `OAI.Erdos3.FiniteProgressionPartition.comparableResidueProgressions`, `OAI.Erdos3.FiniteProgressionPartition.comparableResidueProgressions_length_bounds`, `OAI.Erdos3.FiniteProgressionPartition.comparableResidueProgressions_step`, `OAI.Erdos3.FiniteProgressionPartition.residues`, `OAI.Erdos3.FiniteProgressionPartition.residues_length_lower`, `OAI.Erdos3.FiniteProgressionPartition.residues_start`, `OAI.Erdos3.FiniteProgressionPartition.residues_step`, `OAI.Erdos3.NilpotentLieBCHGroup.quotient_mem_map_subgroup_iff`, `OAI.Erdos3.NilpotentLieFiltration.bch_triple_sub_sum_mem_next_layer`, `OAI.Erdos3.NilpotentLieFiltration.inv_mul_coord_mem_layer_of_quotient_eq`, `OAI.Erdos3.NilpotentLieFiltration.mul_inv_coord_mem_layer_of_quotient_eq`, `OAI.Erdos3.NilpotentLieFiltration.normalized_splitting_sub_sum_mem_next_layer`, `OAI.Erdos3.PatchKernel.kernel_le_periodicValue`, `OAI.Erdos3.PatchKernel.periodicValue`, `OAI.Erdos3.PatchKernel.periodicValue_lipschitz`, `OAI.Erdos3.PatchKernel.periodicValue_mem_Icc`, `OAI.Erdos3.PatchKernel.periodicValue_sub_le`, `OAI.Erdos3.RelativeChangSanders.exp_weightedAverage_le_weightedAverage_exp`, `OAI.Erdos3.RelativeChangSanders.weighted_rudin_exp_ineq`, `OAI.Erdos3.TriangularSlots.tsum_approx_finite_family`, `OAI.Erdos3.TriangularSlots.tsum_eq_at_of_residual_bound`, `OAI.Erdos3.basis_coordinate_linearEquiv_matrix`, `OAI.Erdos3.basis_reindex_equivFun`, `OAI.Erdos3.basis_reindex_grid`, `OAI.Erdos3.basis_reindex_toMatrix`, `OAI.Erdos3.constantSlots`, `OAI.Erdos3.crtConfigurationCharacter`, `OAI.Erdos3.crtConfigurationEquiv`, `OAI.Erdos3.crtConfigurationTorus`, `OAI.Erdos3.derivativeGridPoint_reindex`, `OAI.Erdos3.derivativeGridPoint_reindex_norm`, `OAI.Erdos3.dualBaseLie`, `OAI.Erdos3.dualBaseLinear`, `OAI.Erdos3.dualBaseLinear_constant`, `OAI.Erdos3.dualBaseLinear_infinitesimal`, `OAI.Erdos3.dualBaseLinear_lie`, `OAI.Erdos3.dualBaseLinear_tmul`, `OAI.Erdos3.dualConstantLie`, `OAI.Erdos3.dualInfinitesimal`, `OAI.Erdos3.dualInfinitesimal_injective`, `OAI.Erdos3.dualInfinitesimal_lie`, `OAI.Erdos3.dualLie_decomposition`, `OAI.Erdos3.dualLie_lowerCentralSeries_eq_bot`, `OAI.Erdos3.dualTangentLinear`, `OAI.Erdos3.dualTangentLinear_constant`, `OAI.Erdos3.dualTangentLinear_infinitesimal`, `OAI.Erdos3.dualTangentLinear_tmul`, `OAI.Erdos3.dynkinWord_mem_submodule_of_nonlinear`, `OAI.Erdos3.emptyCubeCoordinateEquiv`, `OAI.Erdos3.eq_zero_of_integer_mul_of_abs_lt`, `OAI.Erdos3.exists_biased_finite_slice`, `OAI.Erdos3.finiteProbabilityTest`, `OAI.Erdos3.lieBCH_sub_add_mem_submodule`, `OAI.Erdos3.lieBCH_triple_sub_sum_mem_submodule`, `OAI.Erdos3.linearCutoff`, `OAI.Erdos3.linearCutoff_eq_one`, `OAI.Erdos3.linearCutoff_eq_zero`, `OAI.Erdos3.linearCutoff_lipschitz`, `OAI.Erdos3.linearCutoff_range`, `OAI.Erdos3.matrixDenominator_mul_entry_real`, `OAI.Erdos3.matrixDenominator_mul_entry_real_integral`, `OAI.Erdos3.nsmulKernelCongr`, `OAI.Erdos3.nsmulKernelPiEquiv`, `OAI.Erdos3.pi_norm_comp_equiv`, `OAI.Erdos3.pivots_lt_of_weighted_bound`, `OAI.Erdos3.rankDependentInputBudget`, `OAI.Erdos3.rankDependentInputBudget_bounds`, `OAI.Erdos3.rational_power_clear_denominator`, `OAI.Erdos3.realDenominatorGrid_comp`, `OAI.Erdos3.realDenominatorGrid_rational_power_scale`, `OAI.Erdos3.residueBlock_long_side_budget`, `OAI.Erdos3.rightBracketList_mem_submodule`, `OAI.Erdos3.separate_kernel`, `OAI.Erdos3.smallBoxCutoff`, `OAI.Erdos3.smallBoxCutoff_lipschitz`, `OAI.Erdos3.smallBoxCutoff_mul_lipschitz`, `OAI.Erdos3.smallBoxCutoff_one`, `OAI.Erdos3.smallBoxCutoff_range`, `OAI.Erdos3.smallBoxCutoff_support`, `OAI.Erdos3.smallBoxCutoff_zero`, `OAI.Erdos3.sorted_basis_diagonal_one`, `OAI.Erdos3.sorted_basis_initial_identity`, `OAI.Erdos3.sorted_basis_upper_zero`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B004

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FlatPatchReset
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

def constantSlots {d : ℕ} (x : Fin d → ℝ) : TriangularSlots d where
  center _ := x
  lower _ _ _ _ := rfl

namespace PatchKernel

variable {d : ℕ} (Φ : PatchKernel d)

noncomputable def periodicValue (x : Fin d → ℝ) : ℝ := (constantSlots x).patchValue Φ

theorem periodicValue_mem_Icc (x : Fin d → ℝ) : Φ.periodicValue x ∈ Set.Icc (0 : ℝ) 1 :=
  (constantSlots x).patchValue_mem_Icc Φ

theorem kernel_le_periodicValue (x : Fin d → ℝ) (b : Fin d → ℤ) :
    Φ.value (fun i => (b i : ℝ) - x i) ≤ Φ.periodicValue x := by
  by_cases hb : Φ.value (fun i => (b i : ℝ) - x i) = 0
  · rw [hb]
    exact (Φ.periodicValue_mem_Icc x).1
  · exact le_of_eq ((constantSlots x).patchValue_eq_of_nonzero Φ hb).symm

theorem periodicValue_sub_le (x y : Fin d → ℝ) :
    Φ.periodicValue x - Φ.periodicValue y ≤ Φ.lip * dist x y := by
  by_cases hx : ∃ b : Fin d → ℤ, Φ.value (fun i => (b i : ℝ) - x i) ≠ 0
  · obtain ⟨b, hb⟩ := hx
    have heq := (constantSlots x).patchValue_eq_of_nonzero Φ hb
    have hle := Φ.kernel_le_periodicValue y b
    have hdist := Φ.lipschitz.dist_le_mul
      ((fun i => (b i : ℝ)) - x) ((fun i => (b i : ℝ)) - y)
    rw [dist_sub_left, Real.dist_eq] at hdist
    have habs := (le_abs_self
      (Φ.value (fun i => (b i : ℝ) - x i) - Φ.value (fun i => (b i : ℝ) - y i))).trans hdist
    change Φ.periodicValue x = Φ.value (fun i => (b i : ℝ) - x i) at heq
    linarith
  · have hz : Φ.periodicValue x = 0 := by
      apply (constantSlots x).patchValue_eq_zero Φ
      intro b
      exact not_ne_iff.mp (fun hb => hx ⟨b, hb⟩)
    have hy := (Φ.periodicValue_mem_Icc y).1
    have hnonneg : 0 ≤ (Φ.lip : ℝ) * dist x y := mul_nonneg Φ.lip.coe_nonneg dist_nonneg
    linarith

theorem periodicValue_lipschitz : LipschitzWith Φ.lip Φ.periodicValue := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  have hxy := Φ.periodicValue_sub_le x y
  have hyx := Φ.periodicValue_sub_le y x
  rw [dist_comm y x] at hyx
  constructor <;> linarith

end PatchKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CurrentLayerSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem bch_triple_sub_sum_mem_next_layer (k : ℕ) (a p d : L)
    (ha : a ∈ F.layer k) (hd : d ∈ F.layer k) :
    lieBCH s (lieBCH s a p) d - (a + p + d) ∈ F.layer (k + 1) := by
  have hp : p ∈ F.layer 1 := by simp only [F.one_eq_top, Submodule.mem_top]
  have hap : lieBCH s a p ∈ F.layer 1 := by
    simp only [F.one_eq_top, Submodule.mem_top]
  have h₁ := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot
    (F.layerIdeal (k + 1)) a p (F.lie_mem ha hp)
  have h₂ := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot
    (F.layerIdeal (k + 1)) (lieBCH s a p) d
    (by
      change ⁅lieBCH s a p, d⁆ ∈ F.layer (k + 1)
      simpa only [Nat.add_comm 1 k] using F.lie_mem hap hd)
  have h := (F.layer (k + 1)).add_mem h₂ h₁
  convert h using 1
  abel

theorem inv_mul_coord_mem_layer_of_quotient_eq (k : ℕ) (a b : F.Group)
    (h : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) a =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) b) :
    (a⁻¹ * b).coord ∈ F.layer k := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal k) _).mp
  have hq : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  exact congrArg NilpotentLieBCHGroup.coord hq

theorem mul_inv_coord_mem_layer_of_quotient_eq (k : ℕ) (a b : F.Group)
    (h : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) a =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) b) :
    (a * b⁻¹).coord ∈ F.layer k := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal k) _).mp
  have hq : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  exact congrArg NilpotentLieBCHGroup.coord hq

theorem normalized_splitting_sub_sum_mem_next_layer (k : ℕ)
    (E P R E₀ R₀ : F.Group)
    (hE : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) E₀ =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) E)
    (hR : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) R =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) R₀) :
    (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord -
      ((E₀⁻¹ * E).coord + P.coord + (R * R₀⁻¹).coord) ∈ F.layer (k + 1) := by
  have heq : E₀⁻¹ * (E * P * R) * R₀⁻¹ = (E₀⁻¹ * E) * P * (R * R₀⁻¹) := by
    simp only [mul_assoc]
  rw [heq]
  exact F.bch_triple_sub_sum_mem_next_layer k _ _ _
    (F.inv_mul_coord_mem_layer_of_quotient_eq k E₀ E hE)
    (F.mul_inv_coord_mem_layer_of_quotient_eq k R R₀ hR)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteBiasedSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_biased_finite_slice {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (F : A → B → ℂ) {δ : ℝ} (hδ : δ ≤ ‖𝔼 a, 𝔼 b, F a b‖) :
    ∃ a, δ ≤ ‖𝔼 b, F a b‖ := by
  have hmean : δ ≤ 𝔼 a, ‖𝔼 b, F a b‖ := hδ.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  exact ⟨a, ha⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FinitePushforwardComplexWeights
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {U T : Type*} [Fintype U] [Fintype T]

noncomputable def finitePushforward (p : FiniteProbabilityWeights U) (f : U → T) :
    FiniteProbabilityWeights T := by
  classical
  refine ⟨fun t => ∑ u, if f u = t then p.weight u else 0, ?_, ?_⟩
  · intro t
    exact Finset.sum_nonneg (fun u _ => by split <;> simp_all only [p.nonneg, le_refl])
  · rw [Finset.sum_comm]
    simpa using p.total

theorem mean_finitePushforward (p : FiniteProbabilityWeights U) (f : U → T) (g : T → ℝ) :
    (p.finitePushforward f).mean g = p.mean (fun u => g (f u)) := by
  classical
  simp only [mean, finitePushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [ite_mul, zero_mul]
  simp

theorem uniform_finitePushforward_mean [Nonempty U] (f : U → T) (g : T → ℝ) :
    ((uniform U).finitePushforward f).mean g = 𝔼 u, g (f u) := by
  rw [mean_finitePushforward, uniform_mean]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {U T : Type*} [Fintype U] [Fintype T]

theorem complexMean_finitePushforward (p : FiniteProbabilityWeights U)
    (f : U → T) (g : T → ℂ) :
    (p.finitePushforward f).complexMean g = p.complexMean (fun u => g (f u)) := by
  classical
  simp only [complexMean, finitePushforward, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul]
  simp

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HorizontalPivotExclusion
namespace OAI

section

namespace Erdos3

theorem pivots_lt_of_weighted_bound {m k : ℕ}
    (p : Fin k → Fin m) (hp : Function.Injective p)
    (w : Fin m → ℝ) (hw : ∀ i, 1 ≤ w i)
    (l : ℕ) (hl : 0 < l) (a : ℕ) (T C v : ℝ)
    (hfar : ∀ i, a ≤ i.val → T ≤ w i)
    (hlower : 1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ v)
    (hupper : v ≤ C) (hlarge : C * (l : ℝ) ^ m < T) :
    ∀ i, (p i).val < a := by
  have hkm : k ≤ m := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective p hp
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hpow : 0 < (l : ℝ) ^ k := pow_pos hlr _
  have hprod : (∏ i, w (p i)) / (l : ℝ) ^ k ≤ C := by
    simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using hlower.trans hupper
  have hC : 0 ≤ C := (div_nonneg
    (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hw (p i)))) hpow.le).trans hprod
  have hprodm : (∏ i, w (p i)) ≤ C * (l : ℝ) ^ m := by
    apply ((div_le_iff₀ hpow).mp hprod).trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact pow_le_pow_right₀ (by exact_mod_cast Nat.succ_le_iff.mpr hl) hkm
  intro j
  by_contra hj
  have hsingle : w (p j) ≤ ∏ i, w (p i) := by
    have h := Finset.prod_le_prod_of_subset_of_one_le
      (f := fun i => w (p i)) (Finset.subset_univ ({j} : Finset (Fin k)))
      (fun i _ => zero_le_one.trans (hw (p i))) (fun i _ _ => hw (p i))
    simpa only [Finset.prod_singleton] using h
  exact (not_le_of_gt hlarge) ((hfar (p j) (Nat.le_of_not_gt hj)).trans (hsingle.trans hprodm))

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

noncomputable def linearCutoff (a : ℝ) (h : ℝ≥0) (t : ℝ) : ℝ :=
  max 0 (min 1 ((a + (h : ℝ) - t) / h))

theorem linearCutoff_range (a : ℝ) (h : ℝ≥0) (t : ℝ) :
    0 ≤ linearCutoff a h t ∧ linearCutoff a h t ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem linearCutoff_eq_one (a : ℝ) (h : ℝ≥0) (hh : 0 < h) {t : ℝ} (ht : t ≤ a) :
    linearCutoff a h t = 1 := by
  have hhR : (0 : ℝ) < h := hh
  have hfrac : (1 : ℝ) ≤ (a + (h : ℝ) - t) / h := (le_div_iff₀ hhR).mpr (by linarith)
  simp only [linearCutoff, min_eq_left hfrac, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem linearCutoff_eq_zero (a : ℝ) (h : ℝ≥0) {t : ℝ} (ht : a + (h : ℝ) ≤ t) :
    linearCutoff a h t = 0 := by
  have hfrac : (a + (h : ℝ) - t) / h ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) h.coe_nonneg
  exact max_eq_left ((min_le_right _ _).trans hfrac)

theorem linearCutoff_lipschitz (a : ℝ) (h : ℝ≥0) (hh : 0 < h) :
    LipschitzWith h⁻¹ (linearCutoff a h) := by
  have hhR : (0 : ℝ) < h := hh
  have haff : LipschitzWith h⁻¹ (fun t : ℝ => (a + (h : ℝ) - t) / h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, ← sub_div]
    have heq : (a + (h : ℝ) - x) - (a + (h : ℝ) - y) = -(x - y) := by ring
    rw [heq, abs_div, abs_neg, abs_of_pos hhR]
    simp only [NNReal.coe_inv]
    exact le_of_eq (by ring)
  exact (haff.const_min 1).const_max 0

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SortedBasisTriangular
namespace OAI

section

namespace Erdos3

open Module

theorem basis_reindex_equivFun {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι]
    (b : Basis ι K E) (e : Equiv.Perm ι) (x : E) :
    (b.reindex e.symm).equivFun x = fun i => b.equivFun x (e i) := by
  funext i
  simp only [Basis.equivFun_apply, Basis.repr_reindex_apply, Equiv.symm_symm]

theorem basis_reindex_toMatrix {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K E) (e : Equiv.Perm ι) (f : E →ₗ[K] E) (i j : ι) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i j =
      LinearMap.toMatrix b b f (e i) (e j) := by
  simp only [LinearMap.toMatrix_apply, Basis.repr_reindex_apply, Basis.reindex_apply,
    Equiv.symm_symm]

theorem basis_coordinate_linearEquiv_matrix {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K E) (f : E ≃ₗ[K] E) :
    LinearMap.toMatrix' (b.equivFun.symm.trans (f.trans b.equivFun)).toLinearMap =
      LinearMap.toMatrix b b f.toLinearMap := by
  ext i j
  rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix_apply]
  change b.equivFun (f (b.equivFun.symm (Pi.single j 1))) i = b.repr (f (b j)) i
  have he : b.equivFun.symm (Pi.single j 1) = b j := by
    apply b.equivFun.injective
    simp only [b.equivFun.apply_symm_apply]
    funext i
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [he, Basis.equivFun_apply]

theorem realDenominatorGrid_comp {ι κ : Type*} (l : ℕ) (x : ι → ℝ)
    (hx : x ∈ realDenominatorGrid l) (e : κ → ι) :
    (x ∘ e) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨z ∘ e, ?_⟩
  funext i
  exact congrFun hz (e i)

theorem basis_reindex_grid {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (b : Basis ι ℝ E) (e : Equiv.Perm ι) (l : ℕ) (x : E)
    (hx : b.equivFun x ∈ realDenominatorGrid l) :
    (b.reindex e.symm).equivFun x ∈ realDenominatorGrid l := by
  rw [basis_reindex_equivFun]
  exact realDenominatorGrid_comp l (b.equivFun x) hx e

end Erdos3

end

section

namespace Erdos3

open Module

theorem sorted_basis_upper_zero {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {d : ℕ}
    (b : Basis (Fin d) K E) (w : Fin d → ℕ) (f : E →ₗ[K] E)
    (hf : ∀ i j, w i ≤ w j → LinearMap.toMatrix b b f i j = (1 : Matrix (Fin d) (Fin d) K) i j)
    (e : Equiv.Perm (Fin d)) (hm : Monotone (w ∘ e)) (i j : Fin d) (hij : i < j) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i j = 0 := by
  rw [basis_reindex_toMatrix, hf _ _ (hm hij.le)]
  simp only [Matrix.one_apply, e.injective.eq_iff, if_neg (ne_of_lt hij)]

theorem sorted_basis_diagonal_one {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {d : ℕ}
    (b : Basis (Fin d) K E) (w : Fin d → ℕ) (f : E →ₗ[K] E)
    (hf : ∀ i j, w i ≤ w j → LinearMap.toMatrix b b f i j = (1 : Matrix (Fin d) (Fin d) K) i j)
    (e : Equiv.Perm (Fin d)) (i : Fin d) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i i = 1 := by
  rw [basis_reindex_toMatrix, hf _ _ le_rfl, Matrix.one_apply_eq]

theorem sorted_basis_initial_identity {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {d a : ℕ}
    (b : Basis (Fin d) K E) (w : Fin d → ℕ) (f : E →ₗ[K] E)
    (hf : ∀ i j, w i ≤ w j → LinearMap.toMatrix b b f i j = (1 : Matrix (Fin d) (Fin d) K) i j)
    (e : Equiv.Perm (Fin d)) (hfirst : ∀ i, i.val < a → w (e i) = 1)
    (i j : Fin d) (hi : i.val < a) (hj : j.val < a) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i j =
      (1 : Matrix (Fin d) (Fin d) K) i j := by
  rw [basis_reindex_toMatrix, hf _ _ (by rw [hfirst i hi, hfirst j hj])]
  simp only [Matrix.one_apply, e.injective.eq_iff]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedDerivativePoints
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem pi_norm_comp_equiv {ι : Type*} [Fintype ι] (x : ι → ℝ) (e : Equiv.Perm ι) :
    ‖x ∘ e‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact norm_le_pi_norm x (e i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h := norm_le_pi_norm (x ∘ e) (e.symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h

theorem derivativeGridPoint_reindex {σ κ : Type*} [Fintype κ]
    (T : σ → ℝ) (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ))
    (A : Matrix κ κ ℝ) (e : Equiv.Perm κ) (h : σ → ℤ) (r : κ → ℝ) :
    derivativeGridPoint T (scale ∘ e) ((LinearMap.funLeft ℝ ℝ e).comp Y)
      (A.submatrix e e) h (r ∘ e) =
        ((derivativeGridPoint T scale Y A h r).1, (derivativeGridPoint T scale Y A h r).2 ∘ e) := by
  have hm : (A.submatrix e e) *ᵥ (r ∘ e) = (A *ᵥ r) ∘ e := by
    simp only [Matrix.submatrix_mulVec_equiv, Function.comp_def, Equiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · funext i
    change scale (e i) * (Y (fun j => (h j : ℝ)) (e i) - ((A.submatrix e e) *ᵥ (r ∘ e)) i) =
      scale (e i) * (Y (fun j => (h j : ℝ)) (e i) - (A *ᵥ r) (e i))
    rw [hm]
    rfl

theorem derivativeGridPoint_reindex_norm {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ))
    (A : Matrix κ κ ℝ) (e : Equiv.Perm κ) (h : σ → ℤ) (r : κ → ℝ) :
    ‖derivativeGridPoint T (scale ∘ e) ((LinearMap.funLeft ℝ ℝ e).comp Y)
      (A.submatrix e e) h (r ∘ e)‖ = ‖derivativeGridPoint T scale Y A h r‖ := by
  rw [derivativeGridPoint_reindex, Prod.norm_def, Prod.norm_def, pi_norm_comp_equiv]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.Separation
namespace OAI

section

namespace Erdos3

theorem eq_zero_of_integer_mul_of_abs_lt {x D : ℝ} (hD : 0 < D)
    (hgrid : ∃ z : ℤ, D * x = z) (hsmall : |x| < 1 / D) : x = 0 := by
  obtain ⟨z, hz⟩ := hgrid
  have hzsmall : |(z : ℝ)| < 1 := by
    rw [← hz, abs_mul, abs_of_pos hD]
    have h := (lt_div_iff₀ hD).mp hsmall
    nlinarith
  have hz0 : z = 0 := by
    have h : |z| < (1 : ℤ) := by exact_mod_cast hzsmall
    have hnonneg := abs_nonneg z
    have habs : |z| = 0 := by omega
    exact abs_eq_zero.mp habs
  rw [hz0, Int.cast_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left hD.ne'

theorem separate_kernel {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : V →ₗ[ℝ] (ι → ℝ)) (a b : V) {D : ℝ} (hD : 0 < D)
    (hsum : Q (a + b) = 0)
    (hgrid : ∀ i, ∃ z : ℤ, D * Q b i = z)
    (hsmall : ∀ i, |Q a i| < 1 / D) : Q a = 0 ∧ Q b = 0 := by
  have hcoords : ∀ i, Q a i + Q b i = 0 := by
    intro i
    have h := congrFun hsum i
    simpa only [map_add, Pi.add_apply, Pi.zero_apply] using h
  have hb : Q b = 0 := by
    funext i
    apply eq_zero_of_integer_mul_of_abs_lt hD (hgrid i)
    have hneg : Q b i = -(Q a i) := by linarith [hcoords i]
    simpa only [hneg, abs_neg] using hsmall i
  refine ⟨?_, hb⟩
  funext i
  change Q a i = 0
  have hbi : Q b i = 0 := congrFun hb i
  linarith [hcoords i]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedRudin
namespace OAI

section

noncomputable section

open _root_.Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

omit [AddCommGroup G] in

theorem exp_weightedAverage_le_weightedAverage_exp
    (w : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hw_sum : ∑ x : G, w x = 1)
    (f : G → ℝ) :
    exp (∑ x : G, w x * f x) ≤ ∑ x : G, w x * exp (f x) := by
  have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset G))
    (p := f) (fun x _ ↦ hw x) (by simpa using hw_sum)
    (fun x _ ↦ Set.mem_univ (f x))
  simpa using h

theorem weighted_rudin_exp_ineq
    (mu : G → ℝ) (K : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x)
    (hDelta : IsWeightedDissociated mu K Delta)
    (c : AddChar G ℂ → ℂ) :
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
      exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
  have hexp (z : ℂ) :
      exp z.re ≤ cosh ‖z‖ + (z / ‖z‖).re * sinh ‖z‖ := by
    calc
      _ = exp ((z / ‖z‖).re * ‖z‖) := by
        obtain rfl | hz := eq_or_ne z 0 <;> simp [*]
      _ ≤ _ := exp_mul_le_cosh_add_mul_sinh
        (by simpa using z.abs_re_div_norm_le_one) _
  choose u hu huc using fun psi ↦ Complex.exists_norm_mul_eq_self (c psi)
  have hu0 (psi : AddChar G ℂ) : u psi ≠ 0 := fun h ↦ by
    simpa [h] using hu psi
  have hpoint (x : G) :
      exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
    calc
      exp ((∑ psi ∈ Delta, c psi * psi x).re) =
          ∏ psi ∈ Delta, exp ((c psi * psi x).re) := by
            simp_rw [← exp_sum, ← Complex.re_sum]
      _ ≤ ∏ psi ∈ Delta,
          (cosh ‖c psi * psi x‖ +
            ((c psi * psi x) / ‖c psi * psi x‖).re *
              sinh ‖c psi * psi x‖) := by
        gcongr with psi hpsi
        exact hexp _
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ +
            (u psi * (c psi * psi x) / (u psi * ↑‖c psi‖)).re *
              sinh ‖c psi‖) := by
        apply prod_congr rfl
        intro psi hpsi
        rw [norm_mul, AddChar.norm_apply, mul_one,
          mul_div_mul_left _ _ (hu0 psi)]
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
        apply prod_congr rfl
        intro psi hpsi
        obtain hc | hc := eq_or_ne (c psi) 0
        · simp [hc]
        simp only [huc, mul_left_comm (u psi), mul_div_cancel_left₀ _ hc,
          ← Complex.re_mul_ofReal, mul_right_comm]
  let q : AddChar G ℂ → ℝ := fun psi ↦ sinh ‖c psi‖ / cosh ‖c psi‖
  let v : AddChar G ℂ → ℂ := fun psi ↦ (q psi : ℂ) * u psi
  have hfactor (x : G) :
      (∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re)) =
        (∏ psi ∈ Delta, cosh ‖c psi‖) *
          (∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
    rw [← Finset.prod_mul_distrib]
    apply prod_congr rfl
    intro psi hpsi
    have hcosh : cosh ‖c psi‖ ≠ 0 := ne_of_gt (cosh_pos _)
    have hsinh_re :
        (u psi * (sinh ‖c psi‖ : ℂ) * psi x).re =
          sinh ‖c psi‖ * (u psi * psi x).re := by
      rw [show u psi * (sinh ‖c psi‖ : ℂ) * psi x =
          (sinh ‖c psi‖ : ℂ) * (u psi * psi x) by ring]
      exact Complex.re_ofReal_mul _ _
    have hv_re : (v psi * psi x).re = q psi * (u psi * psi x).re := by
      rw [show v psi * psi x = (q psi : ℂ) * (u psi * psi x) by
        simp [v]; ring]
      exact Complex.re_ofReal_mul _ _
    rw [hsinh_re, hv_re]
    dsimp [q]
    field_simp
  calc
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∑ x : G, mu x * ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hpoint x) (hmu x)
    _ = (∏ psi ∈ Delta, cosh ‖c psi‖) *
        (∑ x : G, mu x *
          ∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [hfactor]
      ring
    _ ≤ (∏ psi ∈ Delta, cosh ‖c psi‖) * exp K := by
      gcongr
      apply hDelta v
      intro psi hpsi
      have hq : |q psi| ≤ 1 := by
        simpa [q, Real.tanh_eq_sinh_div_cosh] using (Real.abs_tanh_lt_one ‖c psi‖).le
      simpa [v, norm_mul, hu psi, Complex.norm_real, Real.norm_eq_abs] using hq
    _ ≤ exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) * exp K := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      calc
        ∏ psi ∈ Delta, cosh ‖c psi‖ ≤
            ∏ psi ∈ Delta, exp (‖c psi‖ ^ 2 / 2) := by
          gcongr with psi hpsi
          exact cosh_le_exp_half_sq _
        _ = exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
          simp_rw [← exp_sum, ← sum_div]
    _ = exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
      rw [← exp_add]
      congr 1
      ring

end Erdos3.RelativeChangSanders

end

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CRTConfigurationTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def crtConfigurationEquiv {J : Type*} [Fintype J] (N : J → ℕ)
    (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) :
    (ZMod (∏ j, N j) × ZMod (∏ j, N j)) ≃+ ((t : J × Bool) → ZMod (N t.1)) where
  toFun z t := if t.2 then ZMod.prodEquivPi N hN z.2 t.1 else ZMod.prodEquivPi N hN z.1 t.1
  invFun w := ((ZMod.prodEquivPi N hN).symm (fun j => w (j, false)),
    (ZMod.prodEquivPi N hN).symm (fun j => w (j, true)))
  left_inv z := by
    apply Prod.ext
    · change (ZMod.prodEquivPi N hN).symm (ZMod.prodEquivPi N hN z.1) = z.1
      exact (ZMod.prodEquivPi N hN).symm_apply_apply z.1
    · change (ZMod.prodEquivPi N hN).symm (ZMod.prodEquivPi N hN z.2) = z.2
      exact (ZMod.prodEquivPi N hN).symm_apply_apply z.2
  right_inv w := by
    funext ⟨j, b⟩
    cases b
    · change ZMod.prodEquivPi N hN ((ZMod.prodEquivPi N hN).symm (fun j => w (j, false))) j = _
      exact congrFun ((ZMod.prodEquivPi N hN).apply_symm_apply _) j
    · change ZMod.prodEquivPi N hN ((ZMod.prodEquivPi N hN).symm (fun j => w (j, true))) j = _
      exact congrFun ((ZMod.prodEquivPi N hN).apply_symm_apply _) j
  map_add' z v := by
    funext ⟨j, b⟩
    cases b
    · change ZMod.prodEquivPi N hN (z.1 + v.1) j = _
      exact congrFun (map_add (ZMod.prodEquivPi N hN) z.1 v.1) j
    · change ZMod.prodEquivPi N hN (z.2 + v.2) j = _
      exact congrFun (map_add (ZMod.prodEquivPi N hN) z.2 v.2) j

noncomputable def crtConfigurationTorus {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) :
    (ZMod (∏ j, N j) × ZMod (∏ j, N j)) →+ ((J × Bool) → UnitAddCircle) where
  toFun z t := ZMod.toAddCircle (crtConfigurationEquiv N hN z t)
  map_zero' := by ext t; simp
  map_add' z v := by ext t; simp

noncomputable def crtConfigurationCharacter {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (frequency : J × Bool → ℤ) :
    AddChar (ZMod (∏ j, N j) × ZMod (∏ j, N j)) ℂ where
  toFun z := ∏ t, CircleFourier.character (frequency t • crtConfigurationTorus N hN z t)
  map_zero_eq_one' := by simp
  map_add_eq_mul' z v := by
    simp only [map_add, Pi.add_apply, smul_add, CircleFourier.character_add, Finset.prod_mul_distrib]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmptyCubeCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def emptyCubeCoordinateEquiv (X : Type*) : (Option Empty → X) ≃ X where
  toFun x := x none
  invFun x := fun _ => x
  left_inv x := by
    funext i
    cases i with
    | none => rfl
    | some a => exact a.elim
  right_inv _ := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuotientSubgroupCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_mem_map_subgroup_iff (I : LieIdeal ℚ L) (U : LieSubalgebra ℚ L)
    (g : NilpotentLieBCHGroup L s hnil) :
    quotientHom I g ∈ (subgroup (hnil := hnil) U).map (quotientHom (hnil := hnil) I) ↔
      g.coord ∈ U.toSubmodule ⊔ I.toSubmodule := by
  constructor
  · intro hg
    obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp hg
    have hdiff : g.coord - u.coord ∈ I := by
      apply (lieQuotientMap_eq_zero I _).mp
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg coord heq).symm
    apply Submodule.mem_sup.mpr
    exact ⟨u.coord, hu, g.coord - u.coord, hdiff, by abel⟩
  · intro hg
    obtain ⟨u, hu, v, hv, heq⟩ := Submodule.mem_sup.mp hg
    apply Subgroup.mem_map.mpr
    refine ⟨⟨u⟩, hu, ?_⟩
    apply ext
    change lieQuotientMap I u = lieQuotientMap I g.coord
    rw [← heq, map_add, (lieQuotientMap_eq_zero I v).mpr hv, add_zero]

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmallBoxCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

noncomputable def smallBoxCutoff (x : D → ℝ) : ℝ :=
  max 0 (min 1 (3 - 8 * ‖x‖))

theorem smallBoxCutoff_range (x : D → ℝ) :
    0 ≤ smallBoxCutoff x ∧ smallBoxCutoff x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem smallBoxCutoff_one (x : D → ℝ) (hx : ∀ i, |x i| ≤ 1/4) :
    smallBoxCutoff x = 1 := by
  have hn : ‖x‖ ≤ 1/4 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    (by simpa only [Real.norm_eq_abs] using hx)
  rw [smallBoxCutoff, min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem smallBoxCutoff_zero (x : D → ℝ) (hx : 3/8 ≤ ‖x‖) :
    smallBoxCutoff x = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem smallBoxCutoff_support (x : D → ℝ) (hx : smallBoxCutoff x ≠ 0) :
    ∀ i, |x i| < 1/2 := by
  have hn : ‖x‖ < 3/8 := lt_of_not_ge (fun h => hx (smallBoxCutoff_zero x h))
  intro i
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  linarith

theorem smallBoxCutoff_lipschitz : LipschitzWith 8 (smallBoxCutoff (D := D)) := by
  have h : LipschitzWith 8 (fun x : D → ℝ => 3 - 8 * ‖x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have he : (3 - 8 * ‖x‖) - (3 - 8 * ‖y‖) = -8 * (‖x‖ - ‖y‖) := by ring
    rw [he, abs_mul]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8), NNReal.coe_ofNat]
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y)
      (by norm_num)
  exact (h.const_min 1).const_max 0

theorem smallBoxCutoff_mul_lipschitz (f : (D → ℝ) → ℝ) {L B : ℝ≥0}
    (hf : LipschitzWith L f) (hb : ∀ x, |f x| ≤ B) :
    LipschitzWith (L + B * 8) (fun x => smallBoxCutoff x * f x) := by
  simpa only [one_mul] using lipschitz_real_mul_of_bounds (Bf := 1) (Bg := B) smallBoxCutoff f
    smallBoxCutoff_lipschitz hf
    (fun x => by rw [abs_of_nonneg (smallBoxCutoff_range x).1]; exact (smallBoxCutoff_range x).2) hb

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedTriangularSum
namespace OAI

section

namespace Erdos3.TriangularSlots

open scoped BigOperators

variable {d : ℕ} (A : TriangularSlots d)

theorem tsum_eq_at_of_residual_bound (f : (Fin d → ℝ) → ℝ) {R : ℝ}
    (hgap : R + R < 1) (hsupport : ∀ x, f x ≠ 0 → ∀ i, |x i| ≤ R)
    (b : Fin d → ℤ) (hb : ∀ i, |A.residual b i| ≤ R) :
    (∑' z, f (A.residual z)) = f (A.residual b) := by
  apply tsum_eq_single b
  intro z hzb
  by_contra hz
  exact hzb (A.integer_unique hgap (hsupport _ hz) hb)

theorem tsum_approx_finite_family {I : Type*} [Fintype I]
    (f : (Fin d → ℝ) → ℝ) (g : I → (Fin d → ℝ) → ℝ) (c : I → ℝ)
    {R ε : ℝ} (hgap : R + R < 1) (hε : 0 ≤ ε)
    (hf : ∀ x, f x ≠ 0 → ∀ j, |x j| ≤ R)
    (hg : ∀ i x, g i x ≠ 0 → ∀ j, |x j| ≤ R)
    (happrox : ∀ x, |f x - ∑ i, c i * g i x| ≤ ε) :
    |(∑' z, f (A.residual z)) - ∑ i, c i * ∑' z, g i (A.residual z)| ≤ ε := by
  classical
  by_cases h : ∃ z : Fin d → ℤ, f (A.residual z) ≠ 0 ∨ ∃ i, g i (A.residual z) ≠ 0
  · obtain ⟨z, hz⟩ := h
    have hb : ∀ j, |A.residual z j| ≤ R := by
      rcases hz with hz | ⟨i, hi⟩
      · exact hf _ hz
      · exact hg i _ hi
    rw [A.tsum_eq_at_of_residual_bound f hgap hf z hb]
    simp_rw [A.tsum_eq_at_of_residual_bound _ hgap (hg _) z hb]
    exact happrox _
  · have hfzero (z : Fin d → ℤ) : f (A.residual z) = 0 := by
      by_contra hz
      exact h ⟨z, Or.inl hz⟩
    have hgzero (i : I) (z : Fin d → ℤ) : g i (A.residual z) = 0 := by
      by_contra hz
      exact h ⟨z, Or.inr ⟨i, hz⟩⟩
    simp only [hfzero, hgzero, tsum_zero, mul_zero, Finset.sum_const_zero, sub_self, abs_zero]
    exact hε

end Erdos3.TriangularSlots

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ComparableResidueProgressionPartition
namespace OAI

section

namespace Erdos3.FiniteProgressionPartition

noncomputable def residues (N q : ℕ) (hq : 0 < q) :
    FiniteProgressionPartition N := by
  let len : Fin q → ℕ := fun r => truncatedProgressionLength N r.val q N
  let f : (Σ r : Fin q, Fin (len r)) → Fin N := fun x =>
    ⟨x.1.val + q * x.2.val, ((lt_truncatedProgressionLength_iff hq).mp x.2.isLt).2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, j⟩ ⟨s, k⟩ heq
      have he : r.val + q * j.val = s.val + q * k.val := congrArg Fin.val heq
      have hrs : r = s := by
        apply Fin.ext
        have hm := congrArg (fun n => n % q) he
        simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt,
          Nat.mod_eq_of_lt s.isLt] using hm
      cases hrs
      have hjk : j = k := Fin.ext (mul_left_cancel₀ hq.ne' (Nat.add_left_cancel he))
      cases hjk
      rfl
    · intro n
      let r : Fin q := ⟨n.val % q, Nat.mod_lt _ hq⟩
      have hj : n.val / q < len r := by
        apply (lt_truncatedProgressionLength_iff hq).mpr
        exact ⟨lt_of_le_of_lt (Nat.div_le_self _ _) n.isLt,
          by simpa only [r, Nat.mod_add_div] using n.isLt⟩
      exact ⟨⟨r, ⟨n.val / q, hj⟩⟩, Fin.ext (Nat.mod_add_div _ _)⟩
  exact {
    Label := Fin q
    labelFintype := inferInstance
    start := fun r => r.val
    step := fun _ => q
    length := len
    step_pos := fun _ => hq
    equiv := Equiv.ofBijective f hf
    equiv_val := fun _ _ => rfl }

@[simp] theorem residues_start (N q : ℕ) (hq : 0 < q)
    (r : (residues N q hq).Label) : (residues N q hq).start r = r.val := rfl

@[simp] theorem residues_step (N q : ℕ) (hq : 0 < q)
    (r : (residues N q hq).Label) : (residues N q hq).step r = q := rfl

theorem residues_length_lower {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (r : (residues N q hq).Label) :
    H ≤ (residues N q hq).length r := by
  have hHN : H ≤ N := le_trans (Nat.le_mul_of_pos_left H hq) hfit
  have hpoint : r.val + q * (H - 1) < N := by
    have heq : q * (H - 1) + q = q * H := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    have hlt := Nat.add_lt_add_right r.isLt (q * (H - 1))
    omega
  have hj : H - 1 < (residues N q hq).length r :=
    (lt_truncatedProgressionLength_iff hq).mpr ⟨by omega, hpoint⟩
  omega

noncomputable def comparableResidueProgressions (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) : FiniteProgressionPartition N :=
  (residues N q hq).bind (fun r =>
    mergedIntervals ((residues N q hq).length r) H hH
      (residues_length_lower hq hH hfit r))

@[simp] theorem comparableResidueProgressions_step (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidueProgressions N q H hq hH hfit).Label) :
    (comparableResidueProgressions N q H hq hH hfit).step i = q := by
  rcases i with ⟨r, j⟩
  simp [comparableResidueProgressions]

theorem comparableResidueProgressions_length_bounds (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidueProgressions N q H hq hH hfit).Label) :
    H ≤ (comparableResidueProgressions N q H hq hH hfit).length i ∧
      (comparableResidueProgressions N q H hq hH hfit).length i < 2 * H :=
  mergedIntervals_length_bounds _ H hH (residues_length_lower hq hH hfit i.1) i.2

end Erdos3.FiniteProgressionPartition

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerKernelCoordinates
namespace OAI

section

namespace Erdos3

def nsmulKernelCongr {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (d : ℕ) :
    (nsmulAddMonoidHom (α := G) d).ker ≃+
      (nsmulAddMonoidHom (α := H) d).ker where
  toFun x := ⟨e x.val, by
    change d • e x.val = 0
    rw [← map_nsmul, show d • x.val = 0 from x.property, map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    change d • e.symm y.val = 0
    rw [← map_nsmul, show d • y.val = 0 from y.property, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)

def nsmulKernelPiEquiv {I : Type*} (G : I → Type*) [∀ i, AddCommGroup (G i)]
    (d : ℕ) : (nsmulAddMonoidHom (α := ∀ i, G i) d).ker ≃+
      ∀ i, (nsmulAddMonoidHom (α := G i) d).ker where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun y := ⟨fun i => (y i).val, funext fun i => (y i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBlockLongSideBudget
namespace OAI

section

namespace Erdos3

theorem residueBlock_long_side_budget {θ : ℝ} {N q Q H : ℕ}
    (hθ : 0 < θ) (hN : 0 < N) (hq : 0 < q) (hQ : 0 < Q)
    (hH : (N : ℝ) / (2 * q * Q) ≤ H) (n : ℕ) :
    θ * N / (4 * q * Q * (n + 1 : ℝ)) ≤ θ * H / (2 * (n + 1 : ℝ)) ∧
      0 < θ * H / (2 * (n + 1 : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hHr : (0 : ℝ) < H := (by positivity : 0 < (N : ℝ) / (2 * q * Q)).trans_le hH
  refine ⟨?_, by positivity⟩
  calc
    _ = (θ / (2 * (n + 1 : ℝ))) * ((N : ℝ) / (2 * q * Q)) := by
      field_simp
      ring
    _ ≤ (θ / (2 * (n + 1 : ℝ))) * H :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualLieAlgebra
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

abbrev DualLieAlgebra (L : Type*) [LieRing L] [LieAlgebra ℚ L] := DualNumber ℚ ⊗[ℚ] L

noncomputable def dualBaseLinear : DualLieAlgebra L →ₗ[ℚ] L :=
  (TensorProduct.lid ℚ L).toLinearMap.comp
    ((TrivSqZeroExt.fstHom ℚ ℚ ℚ).toLinearMap.rTensor L)

noncomputable def dualTangentLinear : DualLieAlgebra L →ₗ[ℚ] L :=
  (TensorProduct.lid ℚ L).toLinearMap.comp ((TrivSqZeroExt.sndHom ℚ ℚ).rTensor L)

@[simp] theorem dualBaseLinear_tmul (r : DualNumber ℚ) (x : L) :
    dualBaseLinear (r ⊗ₜ[ℚ] x) = r.fst • x := rfl

@[simp] theorem dualTangentLinear_tmul (r : DualNumber ℚ) (x : L) :
    dualTangentLinear (r ⊗ₜ[ℚ] x) = r.snd • x := rfl

noncomputable def dualConstantLie : L →ₗ⁅ℚ⁆ DualLieAlgebra L where
  toLinearMap := TensorProduct.mk ℚ (DualNumber ℚ) L 1
  map_lie' {x y} := by simp [LieAlgebra.ExtendScalars.bracket_tmul]

noncomputable def dualInfinitesimal : L →ₗ[ℚ] DualLieAlgebra L :=
  TensorProduct.mk ℚ (DualNumber ℚ) L DualNumber.eps

@[simp] theorem dualBaseLinear_constant (x : L) : dualBaseLinear (dualConstantLie x) = x := by
  change (1 : ℚ) • x = x
  exact one_smul ℚ x

@[simp] theorem dualTangentLinear_constant (x : L) : dualTangentLinear (dualConstantLie x) = 0 := by
  change (0 : ℚ) • x = 0
  exact zero_smul ℚ x

@[simp] theorem dualBaseLinear_infinitesimal (x : L) : dualBaseLinear (dualInfinitesimal x) = 0 := by
  change (0 : ℚ) • x = 0
  exact zero_smul ℚ x

@[simp] theorem dualTangentLinear_infinitesimal (x : L) : dualTangentLinear (dualInfinitesimal x) = x := by
  change (1 : ℚ) • x = x
  exact one_smul ℚ x

theorem dualInfinitesimal_injective : Function.Injective (dualInfinitesimal (L := L)) := by
  intro x y h
  simpa only [dualTangentLinear_infinitesimal] using congrArg dualTangentLinear h

theorem dualLie_decomposition (z : DualLieAlgebra L) :
    z = dualConstantLie (dualBaseLinear z) + dualInfinitesimal (dualTangentLinear z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    have hr : r = r.fst • (1 : DualNumber ℚ) + r.snd • DualNumber.eps := by
      ext <;> simp
    change r ⊗ₜ[ℚ] x = (1 : DualNumber ℚ) ⊗ₜ[ℚ] (r.fst • x) +
      DualNumber.eps ⊗ₜ[ℚ] (r.snd • x)
    calc
      _ = (r.fst • (1 : DualNumber ℚ) + r.snd • DualNumber.eps) ⊗ₜ[ℚ] x :=
        congrArg (fun a : DualNumber ℚ => a ⊗ₜ[ℚ] x) hr
      _ = _ := by rw [TensorProduct.add_tmul]; simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add x y hx hy =>
    calc
      _ = (dualConstantLie (dualBaseLinear x) + dualInfinitesimal (dualTangentLinear x)) +
          (dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y)) :=
        congrArg₂ (· + ·) hx hy
      _ = _ := by simp only [map_add]; abel

theorem dualBaseLinear_lie (x y : DualLieAlgebra L) :
    dualBaseLinear ⁅x, y⁆ = ⁅dualBaseLinear x, dualBaseLinear y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [zero_lie (L := DualLieAlgebra L) (M := DualLieAlgebra L)]
    simp
  | tmul r x =>
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [lie_zero (L := DualLieAlgebra L) (M := DualLieAlgebra L)]
      simp
    | tmul q y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, dualBaseLinear_tmul,
        TrivSqZeroExt.fst_mul, smul_lie, lie_smul, smul_smul, mul_comm]
    | add y z hy hz =>
      rw [LieRing.lie_add (r ⊗ₜ[ℚ] x) y z, map_add, hy, hz, map_add, LieRing.lie_add]
  | add x z hx hz => rw [LieRing.add_lie x z y, map_add, hx, hz, map_add, LieRing.add_lie]

noncomputable def dualBaseLie : DualLieAlgebra L →ₗ⁅ℚ⁆ L where
  toLinearMap := dualBaseLinear
  map_lie' {x y} := dualBaseLinear_lie x y

theorem dualInfinitesimal_lie (x y : L) : ⁅dualInfinitesimal x, dualInfinitesimal y⁆ = 0 := by
  change ⁅DualNumber.eps ⊗ₜ[ℚ] x, DualNumber.eps ⊗ₜ[ℚ] y⁆ = 0
  rw [LieAlgebra.ExtendScalars.bracket_tmul, DualNumber.eps_mul_eps, TensorProduct.zero_tmul]

theorem dualLie_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (DualLieAlgebra L) (DualLieAlgebra L) s = ⊥ := by
  have hdual : LieModule.lowerCentralSeries (DualNumber ℚ) (DualLieAlgebra L) (DualLieAlgebra L) s = ⊥ := by
    rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange, hnil, LieSubmodule.baseChange_bot]
  apply SetLike.coe_injective
  change (LieModule.lowerCentralSeries ℚ (DualLieAlgebra L) (DualLieAlgebra L) s : Set (DualLieAlgebra L)) = {0}
  rw [LieModule.coe_lowerCentralSeries_eq_int,
    ← LieModule.coe_lowerCentralSeries_eq_int (DualNumber ℚ) (DualLieAlgebra L) (DualLieAlgebra L) s,
    hdual]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankDependentInputBudget
namespace OAI

section

namespace Erdos3

def rankDependentInputBudget (z : ℝ) : ℝ :=
  2 * z + 2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) +
    ((z + 2) ^ 3 + (z + 2) ^ 18 + z) + 2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalClearedMatrixReal
namespace OAI

section

namespace Erdos3

open scoped Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem matrixDenominator_mul_entry_real (S : Matrix ι κ ℚ) (i : ι) (j : κ) :
    (matrixDenominator S : ℝ) * (S i j : ℝ) = (clearedMatrix S i j : ℝ) := by
  classical
  have h : (clearedMatrix S i j : ℚ) = (matrixDenominator S : ℚ) * S i j :=
    congrFun (congrFun (clearedMatrix_cast S) i) j
  exact_mod_cast h.symm

theorem matrixDenominator_mul_entry_real_integral (S : Matrix ι κ ℚ) (i : ι) (j : κ) :
    ∃ z : ℤ, (matrixDenominator S : ℝ) * (S i j : ℝ) = (z : ℝ) :=
  ⟨clearedMatrix S i j, matrixDenominator_mul_entry_real S i j⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubmoduleRemainder
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rightBracketList_mem_submodule (K W : Submodule ℚ L)
    (hbracket : ∀ x ∈ W, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (f : X → L) (hf : ∀ x, f x ∈ K) (xs : List X) (a : L) (ha : a ∈ W) :
    rightBracketList f xs a ∈ W := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih ⁅a, f x⁆ (hbracket a ha (f x) (hf x))

theorem dynkinWord_mem_submodule_of_nonlinear (K W : Submodule ℚ L) (hWK : W ≤ K)
    (hbracket : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (f : X → L) (hf : ∀ x, f x ∈ K) (w : FreeSemigroup X) (hw : w.tail ≠ []) :
    dynkinWord f w ∈ W := by
  unfold dynkinWord
  cases ht : w.tail with
  | nil => exact False.elim (hw ht)
  | cons x xs =>
    exact rightBracketList_mem_submodule K W
      (fun a ha b hb => hbracket a (hWK ha) b hb) f hf xs ⁅f w.head, f x⁆
        (hbracket _ (hf _) _ (hf _))

theorem lieBCH_sub_add_mem_submodule {s : ℕ} (hs : 1 ≤ s)
    (K W : Submodule ℚ L) (hWK : W ≤ K)
    (hbracket : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (a b : L) (ha : a ∈ K) (hb : b ∈ K) :
    lieBCH s a b - (a + b) ∈ W := by
  classical
  rw [lieBCH_eq_add_nonlinear_sum hs, add_sub_cancel_left]
  apply Submodule.sum_mem
  intro w hw
  apply W.smul_mem
  apply dynkinWord_mem_submodule_of_nonlinear K W hWK hbracket ![a, b]
  · intro i
    fin_cases i
    · exact ha
    · exact hb
  · exact (Finset.mem_filter.mp hw).2

theorem lieBCH_triple_sub_sum_mem_submodule {s : ℕ} (hs : 1 ≤ s)
    (K W : Submodule ℚ L) (hWK : W ≤ K)
    (hbracket : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (a b c : L) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    lieBCH s (lieBCH s a b) c - (a + b + c) ∈ W := by
  have hab := lieBCH_sub_add_mem_submodule hs K W hWK hbracket a b ha hb
  have habK : lieBCH s a b ∈ K := by
    simpa only [sub_add_cancel] using K.add_mem (hWK hab) (K.add_mem ha hb)
  have habc := lieBCH_sub_add_mem_submodule hs K W hWK hbracket (lieBCH s a b) c habK hc
  convert W.add_mem habc hab using 1
  abel

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalPowerGrid
namespace OAI

section

namespace Erdos3

theorem rational_power_clear_denominator (a : ℤ) (d s k : ℕ) (hd : 0 < d) (hk : k ≤ s) :
    (d : ℝ) ^ s * ((a : ℝ) / d) ^ k = (a : ℝ) ^ k * (d : ℝ) ^ (s - k) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : (d : ℝ) ^ s = (d : ℝ) ^ (s - k) * (d : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hpow, div_pow]
  field_simp

theorem realDenominatorGrid_rational_power_scale {ι : Type*}
    (degree : ι → ℕ) (D d s : ℕ) (a : ℤ) (hd : 0 < d) (hdegree : ∀ i, degree i ≤ s)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid D) :
    (fun i => ((a : ℝ) / d) ^ degree i * x i) ∈ realDenominatorGrid (D * d ^ s) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => a ^ degree i * (d : ℤ) ^ (s - degree i) * z i, ?_⟩
  funext i
  have hi : (z i : ℝ) = (D : ℝ) * x i := congrFun hz i
  change ((a ^ degree i * (d : ℤ) ^ (s - degree i) * z i : ℤ) : ℝ) =
    ((D * d ^ s : ℕ) : ℝ) * (((a : ℝ) / d) ^ degree i * x i)
  push_cast
  rw [hi]
  calc
    _ = (D : ℝ) * ((d : ℝ) ^ s * ((a : ℝ) / d) ^ degree i) * x i := by
      rw [rational_power_clear_denominator a d s (degree i) hd (hdegree i)]
      ring
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedWeightedLawModeledTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteProbabilityTest {Ω U : Type*} [Fintype U]
    (law : FiniteProbabilityWeights U) (ψ : U → Ω) : (Ω → ℂ) →ₗ[ℂ] ℂ where
  toFun v := law.complexMean (fun u => v (ψ u))
  map_add' v z := by
    simp only [FiniteProbabilityWeights.complexMean, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c v := by
    change (∑ u, (law.weight u : ℂ) * (c * v (ψ u))) =
      c * ∑ u, (law.weight u : ℂ) * v (ψ u)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring

open _root_.MvPolynomial
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

open _root_.MvPolynomial
open scoped NNReal

end Erdos3

end

end OAI

end


