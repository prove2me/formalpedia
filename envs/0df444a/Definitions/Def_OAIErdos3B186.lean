-- Prove2me | Definitions.Def_OAIErdos3B186
-- name    : OAIErdos3B186
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T06:42:38.005691+00:00
-- url     : https://prove2.me/theorems/5af3d228-0011-4679-95f7-f94cd1a9c1ca
-- title:
--   OpenAI Erdős-3 split, definitions bundle 187 of 188
-- statement:
--   Definitions bundle 187 of 188 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B185`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 187 available.
--
--   Modules: `OAI.Erdos3.BSG.BSG_aux`, `OAI.Erdos3.BSG.BSG_self`, `OAI.Erdos3.BSG.BSG_self'`, `OAI.Erdos3.BSG.balogSzemerediGowers`, `OAI.Erdos3.BSG.big_quadruple_bound`, `OAI.Erdos3.BSG.choiceH`, `OAI.Erdos3.BSG.choiceH_subset`, `OAI.Erdos3.BSG.claim_eight`, `OAI.Erdos3.BSG.claim_five`, `OAI.Erdos3.BSG.claim_four`, `OAI.Erdos3.BSG.claim_one`, `OAI.Erdos3.BSG.claim_seven`, `OAI.Erdos3.BSG.claim_six`, `OAI.Erdos3.BSG.claim_three`, `OAI.Erdos3.BSG.claim_two`, `OAI.Erdos3.BSG.dconv`, `OAI.Erdos3.BSG.dconv_apply_nonneg`, `OAI.Erdos3.BSG.dconv_eq_expect_add`, `OAI.Erdos3.BSG.dconv_eq_expect_sub`, `OAI.Erdos3.BSG.dconv_indicator_one`, `OAI.Erdos3.BSG.dconv_nonneg`, `OAI.Erdos3.BSG.dconv_pos`, `OAI.Erdos3.BSG.density_le_mul_iff_card_le_mul`, `OAI.Erdos3.BSG.density_mul_le_iff_card_mul_le`, `OAI.Erdos3.BSG.exists_large_subset_small_difference`, `OAI.Erdos3.BSG.expect_dconv`, `OAI.Erdos3.BSG.expect_dconv_mul`, `OAI.Erdos3.BSG.expect_indicator_one_dconv_indicator_one`, `OAI.Erdos3.BSG.expect_indicator_one_dconv_indicator_sq`, `OAI.Erdos3.BSG.indicator_one_dconv_indicator_one_eq_addConvolution_div`, `OAI.Erdos3.BSG.indicator_one_dconv_indicator_one_eq_dens`, `OAI.Erdos3.BSG.lemma_one`, `OAI.Erdos3.BSG.lemma_one'`, `OAI.Erdos3.BSG.mem_oneOfPair`, `OAI.Erdos3.BSG.oneOfPair`, `OAI.Erdos3.BSG.oneOfPair_aux`, `OAI.Erdos3.BSG.oneOfPair_bound`, `OAI.Erdos3.BSG.oneOfPair_bound_one`, `OAI.Erdos3.BSG.oneOfPair_bound_two`, `OAI.Erdos3.BSG.oneOfPair_subset`, `OAI.Erdos3.BSG.quadruple_bound`, `OAI.Erdos3.BSG.quadruple_bound_c`, `OAI.Erdos3.BSG.quadruple_bound_left`, `OAI.Erdos3.BSG.quadruple_bound_other`, `OAI.Erdos3.BSG.quadruple_bound_right`, `OAI.Erdos3.DegreeRankLieFiltration.positiveUnivariate_horizontal_mem`, `OAI.Erdos3.FreeCoordinateFrame.generator_height`, `OAI.Erdos3.FreeCoordinateFrame.mono`, `OAI.Erdos3.FreeCoordinateFrame.noConfusion`, `OAI.Erdos3.FreeNilpotentLieAlgebra.of_mem_treeGenerators`, `OAI.Erdos3.NativeDegreeRankFamily.nativeCoefficientCoordinates`, `OAI.Erdos3.NativeDegreeRankFamily.nativeCoefficientCoordinates_eq_real`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_finite_assignment_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_missing_factors`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_permutation_partition_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPermutationProduct_tensorPower`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixed_assignment_product_grouped`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixed_missing_assignment_independent`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixed_permutation_eval`, `OAI.Erdos3.NativeUnitRankFamily.eval`, `OAI.Erdos3.NativeUnitRankFamily.mono`, `OAI.Erdos3.NativeUnitRankFamily.mono_eval`, `OAI.Erdos3.NativeUnitRankFamily.rec`, `OAI.Erdos3.NilpotentLieFiltration.piRealOrbit_normalized`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero`, `OAI.Erdos3.RationalFilteredNilmanifold.HasLowerRankOrbitFamily`, `OAI.Erdos3.RationalFilteredNilmanifold.HasLowerRankOrbitFamily.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.HasUniformLowerRankUnitFamily`, `OAI.Erdos3.RationalFilteredNilmanifold.HasUniformLowerRankUnitFamily.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.HasUniformLowerRankUnitFamily.realizeFamily`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.controlledPullback`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.coordinateNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.coordinateNiltest_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.exists_lower_rank_family`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.exists_uniform_lower_rank_difference_family`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.hasUniformLowerRankUnitFamily`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.rank_invariant_of_frequency_zero`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.uniform_lower_rank_family`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_binary_lower_rank_unit_family`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_lower_rank_product_family`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_normalized_product_unit_family`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_lower_rank_map_difference`, `OAI.Erdos3.RationalFilteredNilmanifold.mapDifferenceObservable`, `OAI.Erdos3.RationalFilteredNilmanifold.productObservable_unit`, `OAI.Erdos3.VectorPolynomial.CoefficientBound.add`, `OAI.Erdos3.VectorPolynomial.CoefficientGrid.add`, `OAI.Erdos3.additiveGraph_image_fst`, `OAI.Erdos3.coefficientSpaceBasisBudget`, `OAI.Erdos3.coefficientSpaceBasisBudget_bound`, `OAI.Erdos3.coefficientSpaceInputBudget`, `OAI.Erdos3.exists_common_reference_correction_budget`, `OAI.Erdos3.exists_frozen_common_factorization_budget`, `OAI.Erdos3.exists_large_graph_subset_small_difference`, `OAI.Erdos3.exists_native_coordinate_polynomial_budget`, `OAI.Erdos3.exists_native_free_evaluation`, `OAI.Erdos3.exists_native_free_unit_observable`, `OAI.Erdos3.exists_native_periodic_factorization_budget`, `OAI.Erdos3.exists_petalComparisonSpace_basis_logHeight`, `OAI.Erdos3.exists_rank_sparse_family`, `OAI.Erdos3.exists_simultaneous_four_point_anchors`, `OAI.Erdos3.exists_submodule_basis_of_spanning_logHeight`, `OAI.Erdos3.finite_product_unit_vector`, `OAI.Erdos3.fourSparseAnchorChange`, `OAI.Erdos3.mem_additiveGraph_iff`, `OAI.Erdos3.mixedAssignmentPartitionVector`, `OAI.Erdos3.mixedAssignmentPartitionVector_unit`, `OAI.Erdos3.mixedMissingProduct`, `OAI.Erdos3.mixedPermutationFamily`, `OAI.Erdos3.mixedPermutationIndex`, `OAI.Erdos3.mixedPermutationProduct`, `OAI.Erdos3.mixedPermutationTensorIndex`, `OAI.Erdos3.mixedPermutation_head`, `OAI.Erdos3.mixedPermutation_replica`, `OAI.Erdos3.mixedPermutation_symm_head`, `OAI.Erdos3.mixedPermutation_symm_replica`, `OAI.Erdos3.mixedReplicatedInput_permuted`, `OAI.Erdos3.sub_corrected_reference_add_errors`, `OAI.Erdos3.toAdd_hom_corrected_factor`, `OAI.Erdos3.toAdd_hom_corrected_reference`, `OAI.Finset.addEnergy'`, `OAI.Finset.addEnergy'_eq_div_energy`, `OAI.Finset.cast_addEnergy'`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B058
import Definitions.Def_OAIErdos3B172

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankSparseFamilies
namespace OAI

section

namespace Erdos3

theorem exists_rank_sparse_family
    {ι κ σ : Type*} [Fintype ι] [Fintype κ] {N : ℕ}
    (S : Finset (ZMod N)) (h₀ : ZMod N) (hh₀ : h₀ ∈ S)
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (v : κ → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (2 * (p + ((p + 2) ^ 3 + (p + 2) ^ 36))) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β : ZMod N → ι → ℝ) (a b c d : ZMod N) (M : ℝ),
        2 * M ≤ Real.exp p →
        (∀ h ∈ S, ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ M / monomialScale T α ∧ Q ∈ realDenominatorGrid l ∧
          rankCoordinateTuple β (b - h, b, a) - E - Q ∈ realFourCoordinateSpan J) →
        (∀ h ∈ S, ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ M / monomialScale T α ∧ Q ∈ realDenominatorGrid l ∧
          rankCoordinateTuple β (c - d, h + (c - d), c) - E - Q ∈ realFourCoordinateSpan J) →
        ∀ h ∈ S, ∃ e₁₂ q₁₂ e₁₃ q₁₃ : ι → ℝ,
          ‖e₁₂‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) / monomialScale T α ∧
          ‖e₁₃‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) / monomialScale T α ∧
          q₁₂ ∈ realDenominatorGrid m ∧ q₁₃ ∈ realDenominatorGrid m ∧
          β h - β h₀ - e₁₂ - q₁₂ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) ∧
          β h - β h₀ - e₁₃ - q₁₃ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) := by
  have hselected (K : Finset (Fin 4)) : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (card_selected_four_le K)).trans hfour
  obtain ⟨m₁₂, hm₁₂, hmp₁₂, hlm₁₂, hsolve₁₂⟩ :=
    exists_anchored_sparse_family (η := S) J {1, 2} v hv hH hl hvH hp hfour
      (hselected _) hcols hHp hlp T hT
  obtain ⟨m₁₃, hm₁₃, hmp₁₃, _, hsolve₁₃⟩ :=
    exists_anchored_sparse_family (η := S) J {1, 3} v hv hH hl hvH hp hfour
      (hselected _) hcols hHp hlp T hT
  refine ⟨m₁₂ * m₁₃, Nat.mul_pos hm₁₂ hm₁₃, ?_,
    hlm₁₂.trans (dvd_mul_right m₁₂ m₁₃), ?_⟩
  · rw [Nat.cast_mul]
    calc
      (m₁₂ : ℝ) * m₁₃ ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) *
          Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) :=
        mul_le_mul hmp₁₂ hmp₁₃ (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · intro α hα β a b c d M hM hcorrect₁₂ hcorrect₁₃ h hh
    obtain ⟨e₁₂, q₁₂, he₁₂, hq₁₂, hrem₁₂⟩ := hsolve₁₂ α hα
      (fun h : S => rankCoordinateTuple β (b - h, b, a)) (fun h : S => β h)
      ⟨h₀, hh₀⟩ M hM (fun h i => rankCoordinateTuple_first12 β a b h i)
      (fun h j => rankCoordinateTuple_fixed12 β a b h h₀ j)
      (fun h => hcorrect₁₂ h h.property) ⟨h, hh⟩
    obtain ⟨e₁₃, q₁₃, he₁₃, hq₁₃, hrem₁₃⟩ := hsolve₁₃ α hα
      (fun h : S => rankCoordinateTuple β (c - d, h + (c - d), c)) (fun h : S => β h)
      ⟨h₀, hh₀⟩ M hM (fun h i => rankCoordinateTuple_first13 β c d h i)
      (fun h j => rankCoordinateTuple_fixed13 β c d h h₀ j)
      (fun h => hcorrect₁₃ h h.property) ⟨h, hh⟩
    exact ⟨e₁₂, q₁₂, e₁₃, q₁₃, he₁₂, he₁₃,
      realDenominatorGrid_subset_of_dvd hm₁₂ (dvd_mul_right m₁₂ m₁₃) hq₁₂,
      realDenominatorGrid_subset_of_dvd hm₁₃ (dvd_mul_left m₁₃ m₁₂) hq₁₃, hrem₁₂, hrem₁₃⟩

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

def fourSparseAnchorChange (h : G) : (G × G) ≃ (G × G) where
  toFun u := (u.1, u.1 - u.2 + h)
  invFun u := (u.1, u.1 - u.2 + h)
  left_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · rfl
    · dsimp
      abel_nf
  right_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · rfl
    · dsimp
      abel_nf

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

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

namespace SparseAnchors


end SparseAnchors

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

noncomputable def nativeCoefficientCoordinates
    {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (hs : 1 ≤ s)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2)) :
    ZMod N → ι → ℝ :=
  fun h i => (f.baseChange ℝ).repr
    ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ
      (W.horizontalCoefficient hs c τ hG α h)) i

end NativeDegreeRankFamily

namespace NativeRankRelation.CommonData

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

end NativeRankRelation.CommonData

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ ν : Type*} [Fintype ι] [Fintype ν] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ ν : Type*} [Fintype ι] [Fintype ν] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRealDependentProjection
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 
  (d : Fin (s + 1)) (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

theorem nativeCoefficientCoordinates_eq_real
    {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (hs : 1 ≤ s)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    (h : ZMod N) :
    W.nativeCoefficientCoordinates hs c τ hG α f h =
      W.rank.filtration.realHigherHorizontalCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
        (W.horizontalCoefficient hs c τ hG α h) := by
  funext i
  exact (W.rank.filtration.realHigherHorizontalCoordinates_component
    (Finsupp.weight (fun _ : Unit => 1) α) f (W.horizontalCoefficient hs c τ hG α h) i).symm

end NativeDegreeRankFamily

namespace NativeRankRelation.CommonData

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

end NativeRankRelation.CommonData

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def coefficientSpaceInputBudget (p : ℝ) : ℝ :=
  p + 4 * p + horizontalCoordinateBudget p + (p + 3) ^ 7 + 1

noncomputable def coefficientSpaceBasisBudget (p : ℝ) : ℝ :=
  let a := coefficientSpaceInputBudget p
  preimageBasisBudget (a + (a + 2) ^ 4 + dependentCoordinateBudget a)

namespace NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end NativeRankRelation.CommonData
end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

variable {Q : ℝ} 

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 
  {Q : ℝ} 

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 
  {Q : ℝ} 

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {X : Type*} [Fintype X] {s r : ℕ} {w : X → ℕ} {hw : ∀ x, 0 < w x}

structure FreeCoordinateFrame
    (b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
      (FreeDegreeRankLieAlgebra X s r w hw)) (p : ℝ) where
  tree_height : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
    rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ p
  sourceBasis : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ
    (FreeNilpotentLieAlgebra X s)
  sourceBasis_trees : ∀ i, sourceBasis i ∈ FreeNilpotentLieAlgebra.treeGenerators X s
  sourceDimension : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ p
  sectionMatrix : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
    (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
  section_right_inverse : LinearMap.toMatrix sourceBasis b
    (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * sectionMatrix = 1
  section_height : ∀ i j, rationalLogHeight (sectionMatrix i j) ≤ p

namespace FreeCoordinateFrame

variable {b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
    (FreeDegreeRankLieAlgebra X s r w hw)} {p q : ℝ}

def mono (F : FreeCoordinateFrame b p) (hpq : p ≤ q) : FreeCoordinateFrame b q where
  tree_height x hx i := (F.tree_height x hx i).trans hpq
  sourceBasis := F.sourceBasis
  sourceBasis_trees := F.sourceBasis_trees
  sourceDimension := F.sourceDimension.trans hpq
  sectionMatrix := F.sectionMatrix
  section_right_inverse := F.section_right_inverse
  section_height i j := (F.section_height i j).trans hpq

end FreeCoordinateFrame
end Erdos3

end

section

namespace Erdos3

open Module

theorem FreeNilpotentLieAlgebra.of_mem_treeGenerators
    (X : Type*) [Fintype X] (s : ℕ) (hs : 1 ≤ s) (x : X) :
    FreeNilpotentLieAlgebra.of X s x ∈ FreeNilpotentLieAlgebra.treeGenerators X s := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨FreeMagma.of x, Finset.mem_filter.mpr ⟨?_, hs⟩, rfl⟩
  exact mem_finiteLieTrees_of_length_le X (FreeMagma.of x) hs

theorem FreeCoordinateFrame.generator_height
    {X : Type*} [Fintype X] {s r : ℕ} {w : X → ℕ} {hw : ∀ x, 0 < w x}
    {b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
      (FreeDegreeRankLieAlgebra X s r w hw)} {p : ℝ}
    (F : FreeCoordinateFrame b p) (hs : 1 ≤ s) (x : X) (i) :
    rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.of X s r w hw x) i) ≤ p :=
  F.tree_height (FreeNilpotentLieAlgebra.of X s x)
    (FreeNilpotentLieAlgebra.of_mem_treeGenerators X s hs x) i

theorem exists_submodule_basis_of_spanning_logHeight
    {V ι κ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (e : Basis ι ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {p : ℝ}
    (hv : ∀ a i, rationalLogHeight (e.repr (v a) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p := by
  classical
  let : FiniteDimensional ℚ V := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro a i
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz a
  rw [← hk]
  exact hv k i

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_petalComparisonSpace_basis_logHeight
    {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]
    (e : Basis μ ℚ V) (C P K : Submodule ℚ V)
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (p : Basis (Fin (finrank ℚ P)) ℚ P)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {q : ℝ} (hq : 0 ≤ q)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ q)
    (hp : ∀ a i, rationalLogHeight (e.repr (p a : V) i) ≤ q)
    (hk : ∀ a i, rationalLogHeight (e.repr (k a : V) i) ≤ q) :
    ∃ b : Basis (Fin (finrank ℚ (petalComparisonSpace C P K))) ℚ (petalComparisonSpace C P K),
      ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => e)).repr (b a : Fin 2 → V) i) ≤ q := by
  classical
  let Δ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.pi (fun _ => LinearMap.id)
  let S₀ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.single ℚ (fun _ : Fin 2 => V) 0
  let S₁ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.single ℚ (fun _ : Fin 2 => V) 1
  have hspace : petalComparisonSpace C P K =
      (C.map Δ ⊔ P.map S₀) ⊔ (K.map S₀ ⊔ K.map S₁) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, u, hu, v, hv, h₀, h₁⟩ := petalComparisonSpace_decompose C P K x hx
      have hh : (Δ a + S₀ b) + (S₀ u + S₁ v) ∈
          (C.map Δ ⊔ P.map S₀) ⊔ (K.map S₀ ⊔ K.map S₁) :=
        Submodule.add_mem_sup (Submodule.add_mem_sup ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
          (Submodule.add_mem_sup ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩)
      convert hh using 1
      ext i
      fin_cases i <;> simp [Δ, S₀, S₁, LinearMap.single_apply, h₀, h₁]
    · apply sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [Δ] using And.intro (Submodule.mem_sup_left ha)
          ((P ⊔ K).zero_mem)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₀, LinearMap.single_apply] using
          And.intro ((C ⊔ K).zero_mem) (Submodule.mem_sup_left ha)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₀, LinearMap.single_apply] using
          And.intro ((C ⊔ K).zero_mem) (Submodule.mem_sup_right ha)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₁, LinearMap.single_apply] using
          And.intro (Submodule.mem_sup_right ha) (Submodule.mem_sup_right (K.neg_mem ha))
  have hspan (U : Submodule ℚ V) (b : Basis (Fin (finrank ℚ U)) ℚ U) :
      Submodule.span ℚ (Set.range (fun j => (b j : V))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ b)) = U
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hmap (U : Submodule ℚ V) (b : Basis (Fin (finrank ℚ U)) ℚ U)
      (φ : V →ₗ[ℚ] (Fin 2 → V)) :
      Submodule.span ℚ (Set.range (fun j => φ (b j : V))) = U.map φ := by
    change Submodule.span ℚ (Set.range (φ ∘ fun j => (b j : V))) = _
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  let v := Sum.elim (Sum.elim (fun j => Δ (c j : V)) (fun j => S₀ (p j : V)))
    (Sum.elim (fun j => S₀ (k j : V)) (fun j => S₁ (k j : V)))
  have hv : Submodule.span ℚ (Set.range v) = petalComparisonSpace C P K := by
    dsimp only [v]
    rw [span_range_sumElim, span_range_sumElim, span_range_sumElim,
      hmap, hmap, hmap, hmap, hspace]
  have hsingle (j : Fin 2) (x : V) (hx : ∀ i, rationalLogHeight (e.repr x i) ≤ q)
      (i : Σ _ : Fin 2, μ) :
      rationalLogHeight ((Pi.basis (fun _ : Fin 2 => e)).repr
        (LinearMap.single ℚ (fun _ : Fin 2 => V) j x) i) ≤ q := by
    rcases i with ⟨i, a⟩
    by_cases hji : j = i
    · subst i
      simpa [Pi.basis_repr, LinearMap.single_apply] using hx a
    · simpa [Pi.basis_repr, LinearMap.single_apply, hji, Ne.symm hji, rationalLogHeight] using hq
  apply exists_submodule_basis_of_spanning_logHeight (Pi.basis (fun _ : Fin 2 => e)) _ v hv
  intro j i
  cases j with
  | inl j =>
    cases j with
    | inl j => simpa [v, Δ, Pi.basis_repr] using hc j i.2
    | inr j => exact hsingle 0 (p j) (hp j) i
  | inr j =>
    cases j with
    | inl j => exact hsingle 0 (k j) (hk j) i
    | inr j => exact hsingle 1 (k j) (hk j) i

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

variable {Q : ℝ} 

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 
  
  {Q : ℝ} 


end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitProductOrbitFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct BigOperators

theorem piRealOrbit_normalized {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}
    (g : ∀ i, (F i).realification.PolynomialOrbit w)
    (hg : ∀ i, (F i).realification.polynomialOrbitEval w 0 (g i) = 1) :
    (pi F).realification.polynomialOrbitEval w 0 (piRealOrbit F g) = 1 := by
  classical
  apply (realBCHPiEquiv F).injective
  funext i
  change NilpotentLieBCHGroup.realificationMap
    (hnil := (pi F).lowerCentralSeries_eq_bot) (hM := (F i).lowerCentralSeries_eq_bot)
    (liePiEval i) ((pi F).realification.polynomialOrbitEval w 0 (piRealOrbit F g)) = _
  rw [piRealOrbit_eval, hg]
  simp only [map_one, Pi.one_apply]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι σ τ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  {I : ι → Type*} [∀ i, Fintype (I i)] {w : σ → ℕ}
  (K : ∀ i, I i → (D i).Niltest w)

omit [Nonempty ι] [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productObservable_unit
    (hunit : ∀ i x, ∑ j, ‖(K i j).observable x‖ ^ 2 = 1) (x : (pi D).Space) :
    ∑ j : ∀ i, I i, ‖productObservable D (fun i => K i (j i)) x‖ ^ 2 = 1 := by
  classical
  simp only [productObservable, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ i, ∑ j, ‖(K i j).observable (productProjection D i x)‖ ^ 2 :=
      (Fintype.prod_sum (fun i j => ‖(K i j).observable (productProjection D i x)‖ ^ 2)).symm
    _ = ∏ _i : ι, (1 : ℝ) := Finset.prod_congr rfl (fun i _ => hunit i (productProjection D i x))
    _ = 1 := by simp only [Finset.prod_const_one]

theorem exists_normalized_product_unit_family
    (R : ∀ i, (D i).DegreeRankStructure r) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hR : ∀ i, (R i).ComplexityLE p)
    (hKn : ∀ i j, (K i j).normBound ≤ 1)
    (hKc : ∀ i j, (K i j).ComplexityLE p)
    (hKu : ∀ i x, ∑ j, ‖(K i j).observable x‖ ^ 2 = 1)
    (a : τ → ∀ i, (D i).filtration.realification.PolynomialOrbit w)
    (ha0 : ∀ t i, (D i).filtration.realification.polynomialOrbitEval w 0 (a t i) = 1) :
    (piRank D R).ComplexityLE (productNiltestBudget p) ∧
    ∃ U : (∀ i, I i) → (pi D).Niltest w,
      (∀ j, (U j).normBound = 1) ∧
      (∀ j, (U j).ComplexityLE (productNiltestBudget p)) ∧
      (∀ x, ∑ j, ‖(U j).observable x‖ ^ 2 = 1) ∧
      (∀ t, (pi D).filtration.realification.polynomialOrbitEval w 0
        (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (a t)) = 1) ∧
      ∀ t j x, ((U j).withOrbit
        (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (a t))).eval x =
          ∏ i, ((K i (j i)).withOrbit (a t i)).eval x := by
  classical
  refine ⟨(piRank_complexity D R hp hι hR).mono _ (productNiltestBudget_geometry hp),
    (fun j => unitBoundedPiNiltest D (fun i => K i (j i)) hp hι
      (fun i => hKc i (j i)) (fun i => hKn i (j i))),
    (fun _ => rfl), (fun j => unitBoundedPiNiltest_complexity D _ hp hι _ _),
    (fun x => productObservable_unit D K hKu x),
    (fun t => NilpotentLieFiltration.piRealOrbit_normalized _ _ (ha0 t)), ?_⟩
  intro t j x
  change (∏ i, (K i (j i)).observable (productProjection D i
    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w x
      (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (a t)))))) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_mk]
  exact congrArg (fun g : (D i).RealGroup => (K i (j i)).observable (QuotientGroup.mk g))
    (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) (a t) x i)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BinaryLowerRankFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeUnitRankFamily {σ : Type*} (w : σ → ℕ) (s r : ℕ)
    (τ I : Type*) [Fintype I] (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L s dim
  rank : model.DegreeRankStructure r
  complexity : rank.ComplexityLE p
  test : I → model.Niltest w
  test_norm : ∀ i, (test i).normBound = 1
  test_complexity : ∀ i, (test i).ComplexityLE p
  unit : ∀ x, ∑ i, ‖(test i).observable x‖ ^ 2 = 1
  orbit : τ → model.filtration.realification.PolynomialOrbit w
  normalized : ∀ t, model.filtration.realification.polynomialOrbitEval w 0 (orbit t) = 1

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff

namespace NativeUnitRankFamily

variable {σ τ I : Type*} [Fintype I] {w : σ → ℕ} {s r : ℕ} {p q : ℝ}
  (F : NativeUnitRankFamily w s r τ I p)

noncomputable def eval (t : τ) (i : I) (x : σ → ℤ) : ℂ :=
  (F.test i).observable (QuotientGroup.mk
    (F.model.filtration.realification.polynomialOrbitEval w x (F.orbit t)))

noncomputable def mono (hpq : p ≤ q) : NativeUnitRankFamily w s r τ I q :=
  { F with
    complexity := F.complexity.mono F.rank hpq
    test_complexity := fun i => (F.test_complexity i).mono hpq }

@[simp] theorem mono_eval (hpq : p ≤ q) (t : τ) (i : I) (x : σ → ℤ) :
    (F.mono hpq).eval t i x = F.eval t i x := rfl

end NativeUnitRankFamily

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (T : D.DegreeRankStructure r) {p : ℝ}
  (V : D.UnitVerticalObservable (T.realSubgroup s r) I p)

theorem rank_invariant_of_frequency_zero
    (hzero : ∀ x ∈ T.filtration.layer s r, V.frequency x = 0)
    (z : D.RealGroup) (hz : z ∈ T.realSubgroup s r) (i : I) (x : D.Space) :
    V.observable i (z • x) = V.observable i x := by
  have hle : T.filtration.layer s r ≤ V.frequency.ker := hzero
  have hr : realifyFunctional V.frequency z.coord = 0 :=
    (mem_realified_frequency_kernel_iff V.frequency z.coord).mp
      (Submodule.baseChange_mono ℝ hle hz)
  rw [V.vertical i z hz x, hr, AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

section Coordinates

variable {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p)

noncomputable def coordinateNiltest {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) : D.Niltest w where
  orbit := g
  observable := V.observable i
  normBound := 1
  lipBound := V.lipBound
  norm_le := V.norm i
  lipschitz := V.lipschitz i

theorem coordinateNiltest_complexity {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i : I)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    (V.coordinateNiltest g i).ComplexityLE (p + 4) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + (V.lipBound : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp p := by nlinarith [V.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Coordinates

theorem exists_lower_rank_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
      {p : ℝ} (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
      {w : σ → ℕ} (g : D.filtration.realification.PolynomialOrbit w),
      0 ≤ p → R.ComplexityLE p →
      (∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = 0) →
      ∃ n : ℕ, n ≤ d ∧
        ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
          ∃ U : Q.DegreeRankStructure r,
            ∃ hQF : Q.filtration = D.filtration.quotientLie
                (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal,
              U.filtration = R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
              Q.lattice = D.lattice.map (D.filtration.quotientStepHom
                (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal) ∧
              U.ComplexityLE ((p + C) ^ C) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∃ S : I → Q.Niltest w,
                 (∀ i, (S i).orbit = R.rankQuotientOrbit Q hQF g) ∧
                 (∀ i, (S i).normBound = 1) ∧
                 (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
                 (∀ y : Q.Space, ∑ i, ‖(S i).observable y‖ ^ 2 = 1) ∧
                 (∀ i x, (S i).observable (QuotientGroup.mk
                   (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                     (hM := Q.filtration.lowerCentralSeries_eq_bot)
                     (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
                   V.observable i (QuotientGroup.mk x)) ∧
                 ∀ i x, (S i).eval x = V.observable i
                   (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g))) := by
  obtain ⟨a, _, hdescent⟩ := DegreeRankStructure.exists_rankInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 7) ^ 11
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C a) ^ a + P)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ r d D R p V w g hp hR hzero
  let q := (p + 7) ^ 11
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hp4q : p + 4 ≤ q := by
    apply (show p + 4 ≤ p + 7 by linarith).trans
    exact (pow_one (p + 7)).symm.le.trans
      (pow_le_pow_right₀ (by linarith) (by decide : 1 ≤ 11))
  have hbudget' : (q + a) ^ a + q ≤ (p + C) ^ C := by
    simpa [q, P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (q + a) ^ a)).trans hbudget'
  have haC : (q + a) ^ a ≤ (p + C) ^ C := (le_add_of_nonneg_right hq).trans hbudget'
  obtain ⟨n, hn, Q, U, hU, hQF, hQL, hUc, he⟩ := R.exists_controlled_lower_rank_quotient hp hR
  have h11 : (p + 3) ^ 11 ≤ q := pow_le_pow_left₀ (by positivity) (by linarith) 11
  have h5 : (p + 3) ^ 5 ≤ q :=
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (by decide : 5 ≤ 11)).trans h11
  have hUq : U.ComplexityLE q := hUc.mono U h11
  refine ⟨n, hn, Q, U, hQF, hU, hQL, hUq.mono U hqC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  have htests := fun i => hdescent R Q hQF hQL (V.coordinateNiltest g i) q hq
    ((V.coordinateNiltest_complexity g i hp hR.1).mono hp4q) hUq.1
    (fun i j => (he j i).trans h5)
    (fun z hz x => V.rank_invariant_of_frequency_zero R hzero z hz i x)
  choose S hSo hSn hSc hSp hSe using htests
  refine ⟨S, hSo, hSn, (fun i => (hSc i).mono haC), ?_, hSp, hSe⟩
  intro y
  induction y using Quotient.inductionOn with
  | h y =>
    obtain ⟨x, hx⟩ := D.filtration.realQuotientStepHom_surjective
      (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal y
    have heq : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x = y := hx
    rw [← heq]
    simpa only [hSp, coordinateNiltest] using V.unit (QuotientGroup.mk x)

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

universe u v t

theorem uniform_lower_rank_family {L : Type u} {I : Type v} {σ : Type t}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (R : D.DegreeRankStructure (r + 1)) {p : ℝ}
    (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
    (w : σ → ℕ) (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    (hzero : ∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = 0) :
    let C := (exists_lower_rank_family.{u, v, t} s).choose
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
        ∃ U : Q.DegreeRankStructure r,
          ∃ hQF : Q.filtration = D.filtration.quotientLie
              (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal,
            U.filtration = R.filtration.quotientRank r
              (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
            Q.lattice = D.lattice.map (D.filtration.quotientStepHom
              (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal) ∧
            U.ComplexityLE ((p + C) ^ C) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
               IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 Q.basis
             ∃ S : I → Q.Niltest w,
               (∀ i, (S i).normBound = 1) ∧
               (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
               (∀ y : Q.Space, ∑ i, ‖(S i).observable y‖ ^ 2 = 1) ∧
               (∀ i x, (S i).observable (QuotientGroup.mk
                 (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                   (hM := Q.filtration.lowerCentralSeries_eq_bot)
                   (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
                 V.observable i (QuotientGroup.mk x)) ∧
               ∀ (g : D.filtration.realification.PolynomialOrbit w) i x,
                 ((S i).withOrbit (R.rankQuotientOrbit Q hQF g)).eval x =
                   V.observable i
                     (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g))) := by
  dsimp only
  obtain ⟨n, hn, Q, U, hQF, hUF, hQL, hUc, hS⟩ :=
    (exists_lower_rank_family.{u, v, t} s).choose_spec.2 D R V
      (1 : D.filtration.realification.PolynomialOrbit w) hp hR hzero
  refine ⟨n, hn, Q, U, hQF, hUF, hQL, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨S, _, hSn, hSc, hSu, hSp, _⟩ := hS
  refine ⟨S, hSn, hSc, hSu, hSp, ?_⟩
  intro g i x
  rw [Niltest.withOrbit_eval, R.rankQuotientOrbit_eval Q hQF]
  exact hSp i _

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

def HasUniformLowerRankUnitFamily {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
    (v : I → D.Space → ℂ) (w : σ → ℕ) (p : ℝ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧
    ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
      ∃ U : Q.DegreeRankStructure r, U.ComplexityLE p ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
           IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 Q.basis
         ∃ K : I → Q.Niltest w,
           (∀ i, (K i).normBound = 1) ∧ (∀ i, (K i).ComplexityLE p) ∧
           (∀ y : Q.Space, ∑ i, ‖(K i).observable y‖ ^ 2 = 1) ∧
           ∃ a : D.filtration.realification.PolynomialOrbit w →
               Q.filtration.realification.PolynomialOrbit w,
             (∀ g, D.filtration.realification.polynomialOrbitEval w 0 g = 1 →
               Q.filtration.realification.polynomialOrbitEval w 0 (a g) = 1) ∧
             ∀ g i x, ((K i).withOrbit (a g)).eval x = v i
               (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)))

universe u v t

theorem UnitVerticalObservable.hasUniformLowerRankUnitFamily
    {L : Type u} {I : Type v} {σ : Type t}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (R : D.DegreeRankStructure (r + 1)) {p : ℝ}
    (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
    (w : σ → ℕ) (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    (hzero : ∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = 0) :
    let C := (UnitVerticalObservable.exists_lower_rank_family.{u, v, t} s).choose
    D.HasUniformLowerRankUnitFamily R V.observable w ((p + C) ^ C) := by
  obtain ⟨n, hn, Q, U, hQF, _, _, hUc, hK⟩ :=
    UnitVerticalObservable.uniform_lower_rank_family D R V w hp hR hzero
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, _, hKe⟩ := hK
  refine ⟨K, hKn, hKc, hKu, R.rankQuotientOrbit Q hQF, ?_, hKe⟩
  intro g hg
  rw [R.rankQuotientOrbit_eval Q hQF, hg]
  exact map_one _

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

def HasLowerRankOrbitFamily {L I σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
    (w : σ → ℕ) (f : τ → I → (σ → ℤ) → ℂ) (p : ℝ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧
    ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
      ∃ U : Q.DegreeRankStructure r, U.ComplexityLE p ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
           IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 Q.basis
         ∃ K : I → Q.Niltest w,
           (∀ i, (K i).normBound = 1) ∧ (∀ i, (K i).ComplexityLE p) ∧
           (∀ y : Q.Space, ∑ i, ‖(K i).observable y‖ ^ 2 = 1) ∧
           ∃ a : τ → Q.filtration.realification.PolynomialOrbit w,
             (∀ t, Q.filtration.realification.polynomialOrbitEval w 0 (a t) = 1) ∧
             ∀ t i x, ((K i).withOrbit (a t)).eval x = f t i x)

theorem HasUniformLowerRankUnitFamily.realizeFamily {L I σ τ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {v : I → D.Space → ℂ} {w : σ → ℕ} {p : ℝ}
    (h : D.HasUniformLowerRankUnitFamily R v w p)
    (f : τ → I → (σ → ℤ) → ℂ)
    (hf : ∀ t, ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.filtration.realification.polynomialOrbitEval w 0 g = 1 ∧
      ∀ i x, v i (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval w x g)) = f t i x) :
    D.HasLowerRankOrbitFamily R w f p := by
  classical
  choose b hb0 hb using hf
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, hKe⟩ := hK
  exact ⟨K, hKn, hKc, hKu, (fun t => a (b t)),
    (fun t => ha0 (b t) (hb0 t)),
    fun t i x => (hKe (b t) i x).trans (hb t i x)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

theorem HasLowerRankOrbitFamily.mono {L I σ τ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {w : σ → ℕ} {f : τ → I → (σ → ℤ) → ℂ} {p q : ℝ}
    (h : D.HasLowerRankOrbitFamily R w f p) (hpq : p ≤ q) :
    D.HasLowerRankOrbitFamily R w f q := by
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc.mono U hpq, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, hKe⟩ := hK
  exact ⟨K, hKn, (fun i => (hKc i).mono hpq), hKu, a, ha0, hKe⟩

theorem exists_lower_rank_product_family {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {I : ι → Type*} [∀ i, Fintype (I i)]
    {s r : ℕ} {d : ι → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (R : ∀ i, (D i).DegreeRankStructure (r + 1))
    (w : σ → ℕ) (f : ∀ i, τ → I i → (σ → ℤ) → ℂ) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (h : ∀ i, (D i).HasLowerRankOrbitFamily (R i) w (f i) p) :
    ∃ n : ι → ℕ, (∀ i, n i ≤ d i) ∧
      ∃ Q : ∀ i, RationalFilteredNilmanifold (L i ⧸ (R i).filtration.layerIdeal s (r + 1)) s (n i),
        ∃ U : ∀ i, (Q i).DegreeRankStructure r,
          (piRank Q U).ComplexityLE (productNiltestBudget p) ∧
          (letI : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             fun _ => moduleTopology ℝ _
           letI : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             fun _ => IsModuleTopology.topologicalAddGroup ℝ _
           letI : ∀ i, T2Space (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             fun i => realification_moduleTopology_t2 (Q i).basis
           letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1)))
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 (pi Q).basis
           ∃ K : (∀ i, I i) → (pi Q).Niltest w,
             (∀ j, (K j).normBound = 1) ∧
             (∀ j, (K j).ComplexityLE (productNiltestBudget p)) ∧
             (∀ x, ∑ j, ‖(K j).observable x‖ ^ 2 = 1) ∧
             ∃ a : τ → (pi Q).filtration.realification.PolynomialOrbit w,
               (∀ t, (pi Q).filtration.realification.polynomialOrbitEval w 0 (a t) = 1) ∧
               ∀ t j x, ((K j).withOrbit (a t)).eval x = ∏ i, f i t (j i) x) := by
  classical
  choose n hn Q U hUc hK using h
  refine ⟨n, hn, Q, U,
    (piRank_complexity Q U hp hι hUc).mono _ (productNiltestBudget_geometry hp), ?_⟩
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    fun i => realification_moduleTopology_t2 (Q i).basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi Q).basis
  choose K hKn hKc hKu a ha0 hKe using hK
  obtain ⟨_, V, hVn, hVc, hVu, hVa, hVe⟩ := exists_normalized_product_unit_family Q K U hp hι hUc
    (fun i j => (hKn i j).le) hKc hKu (fun t i => a i t) (fun t i => ha0 i t)
  refine ⟨V, hVn, hVc, hVu,
    (fun t => NilpotentLieFiltration.piRealOrbit (fun i => (Q i).filtration) (fun i => a i t)),
    hVa, ?_⟩
  intro t j x
  rw [hVe]
  exact Finset.prod_congr rfl (fun i _ => hKe i t (j i) x)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

theorem exists_binary_lower_rank_unit_family
    {σ τ : Type*} {I J L₀ L₁ : Type} [Fintype I] [Fintype J]
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
    {s r d₀ d₁ : ℕ} (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (D₁ : RationalFilteredNilmanifold L₁ s d₁)
    (R₀ : D₀.DegreeRankStructure (r + 1)) (R₁ : D₁.DegreeRankStructure (r + 1))
    (w : σ → ℕ) (f₀ : τ → I → (σ → ℤ) → ℂ) (f₁ : τ → J → (σ → ℤ) → ℂ)
    {p : ℝ} (hp : 2 ≤ p)
    (h₀ : D₀.HasLowerRankOrbitFamily R₀ w f₀ p)
    (h₁ : D₁.HasLowerRankOrbitFamily R₁ w f₁ p) :
    ∃ F : NativeUnitRankFamily w s r τ (I × J) (productNiltestBudget p),
      F.dim ≤ d₀ + d₁ ∧ ∀ t ij x, F.eval t ij x = f₀ t ij.1 x * f₁ t ij.2 x := by
  classical
  let D := optionFactors D₀ (fun _ : Unit => D₁)
  let R : ∀ i : Option Unit, (D i).DegreeRankStructure (r + 1)
    | none => R₀
    | some _ => R₁
  let K : Option Unit → Type
    | none => I
    | some _ => J
  let : ∀ i, Fintype (K i) := fun i => match i with
    | none => inferInstanceAs (Fintype I)
    | some _ => inferInstanceAs (Fintype J)
  let f : ∀ i, τ → K i → (σ → ℤ) → ℂ
    | none => f₀
    | some _ => f₁
  have h : ∀ i, (D i).HasLowerRankOrbitFamily (R i) w (f i) p := fun i => by
    match i with
    | none => exact h₀
    | some _ => exact h₁
  obtain ⟨n, hn, Q, U, hU, hfamily⟩ := exists_lower_rank_product_family D R w f
    (by linarith) (by simpa using hp) h
  let L (i : Option Unit) :=
    optionLieSpace L₀ (fun _ : Unit => L₁) i ⧸ (R i).filtration.layerIdeal s (r + 1)
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i) := fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] L i) := fun i => realification_moduleTopology_t2 (Q i).basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi Q).basis
  obtain ⟨V, hVn, hVc, hVu, a, ha, he⟩ := hfamily
  let e : (∀ i, K i) ≃ I × J := {
    toFun := fun k => (k none, k (some ()))
    invFun := fun ij i => match i with
      | none => ij.1
      | some _ => ij.2
    left_inv := by
      intro k
      funext i
      rcases i with _ | ⟨⟩ <;> rfl
    right_inv := fun _ => rfl
  }
  let F : NativeUnitRankFamily w s r τ (I × J) (productNiltestBudget p) := {
    L := ∀ i, L i
    dim := Fintype.card (Σ i : Option Unit, Fin (n i))
    model := pi Q
    rank := piRank Q U
    complexity := hU
    test := fun ij => V (e.symm ij)
    test_norm := fun ij => hVn (e.symm ij)
    test_complexity := fun ij => hVc (e.symm ij)
    unit := fun x => (e.symm.sum_comp (fun k => ‖(V k).observable x‖ ^ 2)).trans (hVu x)
    orbit := a
    normalized := ha
  }
  refine ⟨F, ?_, ?_⟩
  · change Fintype.card (Σ i : Option Unit, Fin (n i)) ≤ d₀ + d₁
    simp only [Fintype.card_sigma, Fintype.card_fin]
    rw [Fintype.sum_option, Fintype.sum_unique]
    exact Nat.add_le_add (hn none) (hn (some ()))
  · intro t ij x
    have hprod := he t (e.symm ij) x
    rw [Fintype.prod_option, Fintype.prod_unique] at hprod
    exact hprod

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LowerRankObservableDifference
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem HasUniformLowerRankUnitFamily.mono {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype I] {s r d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {R : D.DegreeRankStructure (r + 1)} {v : I → D.Space → ℂ} {w : σ → ℕ}
    {p q : ℝ} (h : HasUniformLowerRankUnitFamily D R v w p) (hpq : p ≤ q) :
    HasUniformLowerRankUnitFamily D R v w q := by
  obtain ⟨n, hn, Q, S, hS, hK⟩ := h
  refine ⟨n, hn, Q, S, hS.mono S hpq, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, hKe⟩ := hK
  exact ⟨K, hKn, (fun i => (hKc i).mono hpq), hKu, a, ha0, hKe⟩

namespace UnitVerticalObservable

universe u v w t

theorem exists_uniform_lower_rank_difference_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type u} {I : Type v} {J : Type w} {σ : Type t}
      [LieRing L] [LieAlgebra ℚ L]
      [Fintype I] [Fintype J]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {r d : ℕ} (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure (r + 1)) {p : ℝ}
      (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
      (U : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) J p),
      0 ≤ p → R.ComplexityLE p →
      (∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = U.frequency x) →
      ∀ w : σ → ℕ,
        HasUniformLowerRankUnitFamily D R (V.differenceObservable U) w ((p + C) ^ C) := by
  let a := (exists_lower_rank_family.{u, max v w, t} s).choose
  let P : Polynomial ℕ := (Polynomial.X + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L I J σ _ _ _ _ _ _ _ _ r d D R p V U hp hR hfreq w
  have hb : (p + 2 + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have h := hasUniformLowerRankUnitFamily D R (rankDifference R V U hfreq) w
    (by linarith) (hR.mono R (by linarith)) (fun _ _ => rfl)
  exact h.mono hb

end UnitVerticalObservable
end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredQuotientCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M I : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup E.RealGroup} {p : ℝ} (V : E.UnitVerticalObservable T I p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (S : Subgroup D.RealGroup)
  (hS : S ≤ T.comap (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
  (hentries : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p)

noncomputable def controlledPullback :
    D.UnitVerticalObservable S I (p + (p + 3) ^ 2 + (p + 2) ^ 4) :=
  V.pullback φ hφ S hS ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
    (D.nativeSpaceMap_lipschitz E φ hφ hp hD hE hentries)
    (by
      change (V.lipBound : ℝ) * Real.exp ((p + 3) ^ 2) ≤ _
      calc
        _ ≤ Real.exp p * Real.exp ((p + 3) ^ 2) :=
          mul_le_mul_of_nonneg_right V.lip_bound (Real.exp_pos _).le
        _ = Real.exp (p + (p + 3) ^ 2) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity)))
    (by
      intro i
      exact (rational_functional_value_logHeight E.basis V.frequency hp
        (by simpa only [Fintype.card_fin] using hE.1) V.height (φ (D.basis i))
        (fun j => hentries j i)).trans
          (le_add_of_nonneg_left (add_nonneg hp (sq_nonneg (p + 3)))))

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_native_free_evaluation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X L : Type*) [Fintype X] [LieRing L] [LieAlgebra ℚ L]
      (r d : ℕ) (hr : r ≤ s) (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
      (f : X → L) (hf : ∀ x, f x ∈ R.filtration.layer (w x) 0)
      (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p → R.ComplexityLE p →
      (∀ x i, rationalLogHeight (D.basis.repr (f x) i) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (FreeDegreeRankLieAlgebra X s r w hw) s
          (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = FreeDegreeRankLieAlgebra.filtration X s r w hw hr ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (D.basis.repr
            (FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ D.lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot) (hM := D.filtration.lowerCentralSeries_eq_bot)
            (FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf)) := by
  obtain ⟨a, _, hfree⟩ := exists_free_degree_rank_nilmanifold s
  obtain ⟨c, _, hcover⟩ := RationalFilteredNilmanifold.exists_native_source_cover
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q₀ := Polynomial.X + B₀
  let V₀ := ((Q₀ + 3) ^ (6 * s + 2) + Q₀ + 2) ^ 4
  let P₀ := Q₀ + V₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ r d hr D R w hw f hf p hp hX hR hfH
  let B := (p + a) ^ a
  let q := p + B
  let v := ((q + 3) ^ (6 * s + 2) + q + 2) ^ 4
  let P := q + v
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpq : p ≤ q := le_add_of_nonneg_right hB
  have hBq : B ≤ q := le_add_of_nonneg_left hp
  have hq : 0 ≤ q := hp.trans hpq
  have hqP : q ≤ P := le_add_of_nonneg_right (by dsimp only [v]; positivity)
  have hvP : v ≤ P := le_add_of_nonneg_left hq
  have hP : 0 ≤ P := hq.trans hqP
  have hsum : P + (P + c) ^ c ≤ (p + C) ^ C := by
    simpa [B₀, Q₀, V₀, P₀, B, q, v, P, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P + c) ^ c)).trans hsum
  have hcoverC : (P + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans hsum
  have hBC : B ≤ (p + C) ^ C := hBq.trans (hqP.trans hPC)
  obtain ⟨E₀, Q, hQ, hQcomplex, hcentral, _, _, htree, e, he, hdim, S, hS, hSH⟩ :=
    hfree X r hr w hw 1 (by decide) p hp hX
      (by simpa only [Nat.cast_one, Real.exp_zero] using Real.exp_le_exp.mpr hp)
  let φ := FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf
  have hφ (i j) : rationalLogHeight (D.basis.repr (φ (E₀.basis j)) i) ≤ v := by
    have h := FreeDegreeRankLieAlgebra.lift_basis_matrix_logHeight R.filtration w hw f hf e he
      E₀.basis D.basis S hS hq (hdim.trans hBq)
      (by simpa only [Fintype.card_fin] using hR.1.1.trans hpq)
      (fun i j => (hSH i j).trans hBq)
      (fun i j k => (hR.1.2.2.1 i j k).trans hpq)
      (fun x i => (hfH x i).trans hpq) i j
    rw [LinearMap.toMatrix_apply] at h
    exact h
  obtain ⟨Λ, _, _, _, _, _, N, hN, hin, hout, hgeom, hmap⟩ :=
    hcover E₀ D φ hP (hQcomplex.1.mono E₀ (hBq.trans hqP))
      (hR.1.mono D (hpq.trans hqP)) (fun i j => (hφ i j).trans hvP)
  refine ⟨E₀.withLattice Λ N hN hin hout, Q.withLattice Λ N hN hin hout, hQ, ?_,
    hcentral, ⟨{
      tree_height := fun x hx i => (htree x hx i).trans hBC
      sourceBasis := e
      sourceBasis_trees := he
      sourceDimension := hdim.trans hBC
      sectionMatrix := S
      section_right_inverse := hS
      section_height := fun i j => (hSH i j).trans hBC
    }⟩, fun i j => (hφ i j).trans (hvP.trans hPC), hmap⟩
  exact Q.withLattice_complexity Λ N hN hin hout hQcomplex hBC
    (hgeom.mono _ hcoverC)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_free_unit_observable (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X L I : Type*) [Fintype X] [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (r d : ℕ) (hr : r ≤ s) (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
      (f : X → L) (hf : ∀ x, f x ∈ R.filtration.layer (w x) 0)
      (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p → R.ComplexityLE p →
      (∀ x i, rationalLogHeight (D.basis.repr (f x) i) ≤ p) →
      ∀ U : D.UnitVerticalObservable (R.realSubgroup s r) I p,
      let φ := FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf
      ∃ E : RationalFilteredNilmanifold (FreeDegreeRankLieAlgebra X s r w hw) s
          (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = FreeDegreeRankLieAlgebra.filtration X s r w hw hr ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ D.lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (Q.realSubgroup s r) I ((p + C) ^ C),
             V.frequency = U.frequency.comp φ.toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.observable i (QuotientGroup.mk (realificationMap
                 (hnil := E.filtration.lowerCentralSeries_eq_bot)
                 (hM := D.filtration.lowerCentralSeries_eq_bot) φ x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_free_evaluation s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let T₀ := Polynomial.X + A₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (A₀ + (T₀ + (T₀ + 3) ^ 2 + (T₀ + 2) ^ 4))
  refine ⟨C, hC, ?_⟩
  intro X L I _ _ _ _ _ _ _ _ r d hr D R w hw f hf p hp hX hR hfH U φ
  let A := (p + a) ^ a
  let t := p + A
  let q := t + (t + 3) ^ 2 + (t + 2) ^ 4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right hA
  have hAt : A ≤ t := le_add_of_nonneg_left hp
  have ht : 0 ≤ t := hp.trans hpt
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hcost : A + q ≤ (p + C) ^ C := by
    simpa [A₀, T₀, A, t, q, Polynomial.eval₂_pow] using hbudget p hp
  have hAC : A ≤ (p + C) ^ C := (le_add_of_nonneg_right hq).trans hcost
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_left hA).trans hcost
  obtain ⟨E, Q, hQ, hcomplex, hcentral, ⟨frame⟩, hmatrix, hlattice⟩ :=
    hfree X L r d hr D R w hw f hf p hp hX hR hfH
  let := moduleTopology ℝ (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  have hlayer (i j : ℕ) :
      (Q.filtration.layer i j).map φ.toLinearMap ≤ R.filtration.layer i j := by
    rintro y ⟨x, hx, rfl⟩
    rw [hQ] at hx
    exact FreeDegreeRankLieAlgebra.lift_mem_layer R.filtration w hw f hf hr hx
  have htop : Q.realSubgroup s r ≤ (R.realSubgroup s r).comap
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) φ) := by
    intro z hz
    change realificationLieHom φ z.coord ∈ (R.filtration.layer s r).baseChange ℝ
    have hz' : z.coord ∈ (Q.filtration.layer s r).baseChange ℝ := hz
    have h := Submodule.baseChange_mono ℝ (hlayer s r)
    rw [realification_map] at h
    exact h ⟨z.coord, hz', rfl⟩
  let V := (U.mono hpt).controlledPullback φ hlattice (Q.realSubgroup s r) htop ht
    (hcomplex.1.mono E hAt) (hR.1.mono D hpt) (fun i j => (hmatrix i j).trans hAt)
  refine ⟨E, Q, hQ, hcomplex.mono Q hAC, hcentral,
    ⟨frame.mono hAC⟩, (fun i j => (hmatrix i j).trans hAC), hlattice, ?_⟩
  exact ⟨V.mono hqC, rfl, fun i x => rfl⟩

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {L M I J : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] [Fintype J] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup D.RealGroup} {S : Subgroup E.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p) (U : E.UnitVerticalObservable S J p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

noncomputable def mapDifferenceObservable (a : I × J) (x : D.Space) : ℂ :=
  V.observable a.1 x * star (U.observable a.2 (D.nativeSpaceMap E φ hφ x))

theorem exists_uniform_lower_rank_map_difference (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M I J σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] [Fintype I] [Fintype J]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {r d e : ℕ} (D : RationalFilteredNilmanifold L s d)
      (E : RationalFilteredNilmanifold M s e)
      (R : D.DegreeRankStructure (r + 1)) (S : E.DegreeRankStructure (r + 1))
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
        (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
      {p : ℝ} (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
      (U : E.UnitVerticalObservable (S.realSubgroup s (r + 1)) J p),
      0 ≤ p → R.ComplexityLE p → S.ComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (∀ x ∈ R.filtration.layer s (r + 1), φ x ∈ S.filtration.layer s (r + 1)) →
      (∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = U.frequency (φ x)) →
      ∀ w : σ → ℕ,
        HasUniformLowerRankUnitFamily D R (mapDifferenceObservable V U φ hφ) w ((p + C) ^ C) := by
  obtain ⟨a, _, hdescent⟩ := UnitVerticalObservable.exists_uniform_lower_rank_difference_family s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + 3) ^ 2 + (X + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L M I J σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r d e D E R S φ hφ p V U hp hR hS hentries htop hfreq w
  let q := p + (p + 3) ^ 2 + (p + 2) ^ 4
  have hpq : p ≤ q := by
    dsimp only [q]
    linarith [sq_nonneg (p + 3), show 0 ≤ (p + 2) ^ 4 from by positivity]
  have hq : 0 ≤ q := hp.trans hpq
  have hb : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hreal : R.realSubgroup s (r + 1) ≤ (S.realSubgroup s (r + 1)).comap
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
    intro z hz
    change realificationLieHom φ z.coord ∈ (S.filtration.layer s (r + 1)).baseChange ℝ
    have hmap : (R.filtration.layer s (r + 1)).map φ.toLinearMap ≤
        S.filtration.layer s (r + 1) := by
      rintro y ⟨x, hx, rfl⟩
      exact htop x hx
    have h := Submodule.baseChange_mono ℝ hmap
    rw [realification_map] at h
    exact h ⟨z.coord, hz, rfl⟩
  let U' := U.controlledPullback φ hφ (R.realSubgroup s (r + 1)) hreal hp hR.1 hS.1 hentries
  have heq : ∀ x ∈ R.filtration.layer s (r + 1), (V.mono hpq).frequency x = U'.frequency x := hfreq
  have h := hdescent D R (V.mono hpq) U' hq (hR.mono R hpq) heq w
  exact h.mono hb

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {L M I J X : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] [Fintype J] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup D.RealGroup} {S : Subgroup E.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p) (U : E.UnitVerticalObservable S J p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {L M A I J : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] [Fintype J] {s t d e N degree : ℕ} [NeZero N]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup D.RealGroup} {S : Subgroup E.RealGroup} {p q : ℝ}
  (V : D.UnitVerticalObservable T I q) (U : E.UnitVerticalObservable S J q)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPermutationTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_product_unit_vector {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I]
    (f : A → I → ℂ) (hf : ∀ a, ∑ i, ‖f a i‖ ^ 2 = 1) :
    ∑ v : A → I, ‖∏ a, f a (v a)‖ ^ 2 = 1 := by
  simp only [norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (a : A) (i : I) => ‖f a i‖ ^ 2)]
  simp only [hf, Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedPermutationFamily {s : ℕ} (e : Equiv.Perm (Fin s)) :
    ReplicatedPermutation (mixedCorrelationDegree s) :=
  Fin.cases (motive := fun b : Fin 2 => Equiv.Perm (Fin (mixedCorrelationDegree s b)))
    (Equiv.refl _) (fun _ => e)

theorem mixedPermutation_head {s : ℕ} (e : Equiv.Perm (Fin s)) :
    replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e) (mixedHead s) =
      mixedHead s := rfl

theorem mixedPermutation_replica {s : ℕ} (e : Equiv.Perm (Fin s)) (j : Fin s) :
    replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e) (mixedReplica j) =
      mixedReplica (e j) := rfl

theorem mixedPermutation_symm_head {s : ℕ} (e : Equiv.Perm (Fin s)) :
    (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm (mixedHead s) =
      mixedHead s := by
  have H := (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm_apply_apply
    (mixedHead s)
  simpa only [mixedPermutation_head] using H

theorem mixedPermutation_symm_replica {s : ℕ} (e : Equiv.Perm (Fin s)) (j : Fin s) :
    (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm (mixedReplica j) =
      mixedReplica (e.symm j) := by
  have H := (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm_apply_apply
    (mixedReplica (e.symm j))
  simpa only [mixedPermutation_replica, Equiv.apply_symm_apply] using H

theorem mixedReplicatedInput_permuted {s : ℕ} {α : Type*} (e : Equiv.Perm (Fin s))
    (h : α) (v : Fin s → α) :
    (fun j => mixedReplicatedInput h v
      ((replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm j)) =
      mixedReplicatedInput h (fun i => v (e.symm i)) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rw [mixedPermutation_symm_head, mixedReplicatedInput_head, mixedReplicatedInput_head]
  · rw [mixedPermutation_symm_replica, mixedReplicatedInput_replica, mixedReplicatedInput_replica]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p)

theorem mixed_permutation_eval
    (hsym : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
      W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x)
    (e : Equiv.Perm (Fin s)) (k : Fin W.outputDim) (h : ℤ) (v : Fin s → ℤ) :
    W.eval k (mixedReplicatedInput h (fun j => v (e j))) = W.eval k (mixedReplicatedInput h v) := by
  have H := hsym (mixedPermutationFamily e.symm) k (mixedReplicatedInput h v)
  simpa only [mixedReplicatedInput_permuted, Equiv.symm_symm] using H

theorem mixed_assignment_product_grouped
    (hsym : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
      W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x)
    (h : ℤ) (x : Fin s → ℤ) (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → Fin W.outputDim) :
    (∏ v : Fin s → Fin s, W.eval (a ((assignmentSplitEquiv s).symm v))
      (mixedReplicatedInput h (fun j => x (v j)))) =
      (∏ e : Equiv.Perm (Fin s), W.eval (a (Sum.inl e)) (mixedReplicatedInput h x)) *
        ∏ v : MissingAssignment s, W.eval (a (Sum.inr v))
          (mixedReplicatedInput h (fun j => x (v.val j))) := by
  classical
  rw [assignment_product_split (fun v k => W.eval k (mixedReplicatedInput h (fun j => x (v j)))) a]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  exact W.mixed_permutation_eval hsym e _ h x

theorem mixed_missing_assignment_independent (v : MissingAssignment s) :
    ∃ j : Fin s, ∀ (k : Fin W.outputDim) (x y : Fin (s + 1) → ℤ),
      (∀ a, a ≠ j.succ → x a = y a) →
      W.eval k (mixedReplicatedInput (x 0) (fun i => x (v.val i).succ)) =
        W.eval k (mixedReplicatedInput (y 0) (fun i => y (v.val i).succ)) := by
  obtain ⟨j, hj⟩ := missingAssignment_coordinate v
  refine ⟨j, ?_⟩
  intro k x y hxy
  congr 1
  funext a
  rcases mixedReplicated_cases a with rfl | ⟨i, rfl⟩
  · rw [mixedReplicatedInput_head, mixedReplicatedInput_head]
    apply hxy
    exact (Fin.succ_ne_zero j).symm
  · rw [mixedReplicatedInput_replica, mixedReplicatedInput_replica]
    apply hxy
    exact fun heq => hj i (Fin.succ_injective s heq)

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_finite_assignment_expansion (s n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin (n + 2) → ℤ) => W.eval k
          (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ a : Fin (n + 1), x a.succ)))
        (fun a : (Fin s → Fin (n + 1)) → Fin W.outputDim => fun x =>
          ∏ v : Fin s → Fin (n + 1), W.eval (a v)
            (mixedReplicatedInput (x 0) (fun j => x (v j).succ))) := by
  let : Nonempty (MixedReplicatedIndex s) := replicatedMixed_nonempty s
  obtain ⟨A, _, hexpand⟩ := exists_finite_assignment_equivalence n (mixedRepeatedCoordinates s)
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C ((n + 1) ^ s) * X + X)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hsum : (p + A) ^ A + ((n + 1) ^ s : ℕ) * p + p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (p + A) ^ A := by positivity
  have hnp : 0 ≤ ((n + 1) ^ s : ℕ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hAC : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hnC : ((n + 1) ^ s : ℕ) * p ≤ (p + C) ^ C := by linarith
  let M (j : Fin (n + 1) × MixedReplicatedIndex s) : ((Fin (n + 2) → ℤ) →+ ℤ) :=
    { toFun := fun x => mixedChoiceSample (x 0) (fun a => x a.succ) j
      map_zero' := by rcases j with ⟨a, b, k⟩; fin_cases b <;> rfl
      map_add' := by intro x y; rcases j with ⟨a, b, k⟩; fin_cases b <;> rfl }
  have hM (x : Fin (n + 2) → ℤ) :
      (fun j => M j x) = mixedChoiceSample (x 0) (fun a => x a.succ) := rfl
  have E := (hexpand W (mixedRepeatedCoordinates_nodup s)).linearPullbackHom M
  have H : NativeIntegerVectorEquivalence s ((p + A) ^ A)
      (fun k (x : Fin (n + 2) → ℤ) => W.eval k
        (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ a : Fin (n + 1), x a.succ)))
      (fun a : (Fin (mixedRepeatedCoordinates s).length → Fin (n + 1)) → Fin W.outputDim =>
        fun x => ∏ v, W.eval (a v)
          (mixedReplicatedInput (x 0) (fun j => x (mixedChoiceAssignmentEquiv s n v j).succ))) := by
    simpa only [hM, finiteChoiceExpansion, mixedChoiceSample_sum, mixedChoiceSample_leaf,
      replicatedMixed_card, Nat.add_sub_cancel] using E
  have hdim : (Fintype.card ((Fin s → Fin (n + 1)) → Fin W.outputDim) : ℝ) ≤
      Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp p ^ ((n + 1) ^ s) := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
      _ = Real.exp (((n + 1) ^ s : ℕ) * p) := (Real.exp_nat_mul p ((n + 1) ^ s)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnC
  apply H.of_coordinate_maps _ _ id (fun a v => a (mixedChoiceAssignmentEquiv s n v))
    (fun _ _ => rfl) _ _ hdim hAC
  · intro a x
    exact ((mixedChoiceAssignmentEquiv s n).prod_comp (fun v : Fin s → Fin (n + 1) =>
      W.eval (a v) (mixedReplicatedInput (x 0) (fun j => x (v j).succ)))).symm
  · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedPermutationProduct {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ)
    (a : Equiv.Perm (Fin s) → I) (x : Fin (s + 1) → ℤ) : ℂ :=
  ∏ e, f (a e) (mixedReplicatedInput (x 0) (fun j => x j.succ))

noncomputable def mixedMissingProduct {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ)
    (a : MissingAssignment s → I) (x : Fin (s + 1) → ℤ) : ℂ := by
  classical
  exact ∏ v, f (a v) (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ))

noncomputable def mixedAssignmentPartitionVector {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ)
    (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → I) (x : Fin (s + 1) → ℤ) : ℂ :=
  mixedPermutationProduct f (fun e => a (Sum.inl e)) x *
    mixedMissingProduct f (fun v => a (Sum.inr v)) x

theorem mixedAssignmentPartitionVector_unit {s : ℕ} {I : Type*} [Fintype I]
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ) (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1)
    (x : Fin (s + 1) → ℤ) :
    ∑ a, ‖mixedAssignmentPartitionVector f a x‖ ^ 2 = 1 := by
  classical
  let F (r : Equiv.Perm (Fin s) ⊕ MissingAssignment s) (i : I) :=
    match r with
    | Sum.inl _ => f i (mixedReplicatedInput (x 0) (fun j => x j.succ))
    | Sum.inr v => f i (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ))
  have hF : ∀ r, ∑ i, ‖F r i‖ ^ 2 = 1 := by
    intro r
    cases r <;> exact hf _
  simpa only [mixedAssignmentPartitionVector, mixedPermutationProduct, mixedMissingProduct,
    Fintype.prod_sum_type, F] using finite_product_unit_vector F hF

theorem NativeMultidegreeNilcharacter.exists_mixed_missing_factors {s : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p)
    (a : MissingAssignment s → Fin W.outputDim) :
    ∃ A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ,
      (∀ k x, ‖A k x‖ ≤ 1) ∧
      (∀ k x y, (∀ l, l ≠ k → x l = y l) → A k x = A k y) ∧
      ∀ x, (∏ k, A k x) = mixedMissingProduct W.eval a x := by
  classical
  apply exists_missing_coordinate_product_factors
    (fun v x => W.eval (a v) (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ)))
    (fun _ _ => W.norm_eval _ _)
  intro v
  obtain ⟨j, hj⟩ := W.mixed_missing_assignment_independent v
  exact ⟨j.succ, hj (a v)⟩

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_permutation_partition_expansion (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x) →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin (s + 1) → ℤ) => W.eval k
          (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ j : Fin s, x j.succ)))
        (fun a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → Fin W.outputDim => fun x =>
          (∏ e : Equiv.Perm (Fin s), W.eval (a (Sum.inl e))
            (mixedReplicatedInput (x 0) (fun j => x j.succ))) *
          ∏ v : MissingAssignment s, W.eval (a (Sum.inr v))
            (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ))) := by
  cases s with
  | zero => omega
  | succ n =>
      obtain ⟨C, hC, hexpand⟩ := exists_mixed_finite_assignment_expansion (n + 1) n
      refine ⟨C, hC, ?_⟩
      intro p W hsym
      classical
      have E := hexpand W
      apply E.of_coordinate_maps _ _ id
        (fun a v => a ((assignmentSplitEquiv (n + 1)).symm v))
        (fun _ _ => rfl) _ E.left_dimension _ le_rfl
      · intro a x
        exact (W.mixed_assignment_product_grouped hsym (x 0) (fun j => x j.succ) a).symm
      · have hcard : Fintype.card (Equiv.Perm (Fin (n + 1)) ⊕ MissingAssignment (n + 1)) =
            Fintype.card (Fin (n + 1) → Fin (n + 1)) :=
          Fintype.card_congr (assignmentSplitEquiv (n + 1))
        simpa only [Fintype.card_fun, hcard] using E.right_dimension

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedPermutationIndex (s : ℕ) : Equiv.Perm (Fin s) ≃ Fin s.factorial :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_perm, Fintype.card_fin])

noncomputable def mixedPermutationTensorIndex {s : ℕ} (d : ℕ)
    (a : Equiv.Perm (Fin s) → Fin d) : Fin (d ^ s.factorial) :=
  tensorIndexEquiv d s.factorial (fun j => a ((mixedPermutationIndex s).symm j))

theorem NativeMultidegreeNilcharacter.mixedPermutationProduct_tensorPower {s : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p)
    (a : Equiv.Perm (Fin s) → Fin W.outputDim) (x : Fin (s + 1) → ℤ) :
    mixedPermutationProduct W.eval a x =
      (W.tensorPower s.factorial).eval (mixedPermutationTensorIndex W.outputDim a)
        (mixedReplicatedInput (x 0) (fun j => x j.succ)) := by
  simp only [tensorPower_eval, mixedPermutationTensorIndex, Equiv.symm_apply_apply]
  exact ((mixedPermutationIndex s).symm.prod_comp
    (fun e => W.eval (a e) (mixedReplicatedInput (x 0) (fun j => x j.succ)))).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreePowerBound
namespace OAI

section

namespace Erdos3

theorem exists_native_coordinate_polynomial_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      nativeCoordinateSeparationBudget s P ≤ (P + C) ^ C ∧
      ((s : ℝ) + 1) * nativeDependentDenominatorBudget s P ≤ (P + C) ^ C ∧
      nativeDependentSlowBudget s P ≤ (P + C) ^ C ∧ (P + 3) ^ 7 ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let G := X + X * (R + 1 + (X + 3) ^ 7)
  let U := 4 * X + (X + 3) ^ 7 + G + Polynomial.C s * X + (X + 3) ^ 2 + 4
  let V := U + (U + 2) ^ 3 + X + 2
  let Z := 2 * V + 2 * (V + ((V + 2) ^ 3 + (V + 2) ^ 36)) +
    ((V + 2) ^ 3 + (V + 2) ^ 18 + V) + 2
  let Q := Z + (Z + Z * ((Z + 2) ^ 7 + Z))
  let cut := ((V + 2) ^ 48 + (V + 2) ^ 24 + V + 1) +
    ((Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1)
  let den := Q + (Q + 2) ^ 3 + (Q + 2) ^ 36
  let slow := (Q + 2) ^ 3 + (Q + 2) ^ 18 + Q + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (cut + Polynomial.C (s + 1) * den + slow + (X + 3) ^ 7)
  refine ⟨C, hC, ?_⟩
  intro P hP
  have hU : U.eval₂ (Nat.castRingHom ℝ) P = nativeCoordinateBaseBudget s P := by
    simp [U, G, R, X, nativeCoordinateBaseBudget, horizontalCoordinateBudget,
      refiltrationCoordinateBudget, Polynomial.eval₂_pow]
  have hV : V.eval₂ (Nat.castRingHom ℝ) P = nativeCoordinateInputBudget s P := by
    simp [V, X, Polynomial.eval₂_pow, hU, nativeCoordinateInputBudget]
  have hZ : Z.eval₂ (Nat.castRingHom ℝ) P =
      rankDependentInputBudget (nativeCoordinateInputBudget s P) := by
    simp [Z, Polynomial.eval₂_pow, hV, rankDependentInputBudget]
  have hQ : Q.eval₂ (Nat.castRingHom ℝ) P = nativeDependentBudget s P := by
    simp [Q, Polynomial.eval₂_pow, hZ, nativeDependentBudget, sparseGeneratorBudget]
  have hsum : nativeCoordinateSeparationBudget s P +
      ((s : ℝ) + 1) * nativeDependentDenominatorBudget s P +
      nativeDependentSlowBudget s P + (P + 3) ^ 7 ≤ (P + C) ^ C := by
    simpa [cut, den, slow, X, Polynomial.eval₂_pow, hV, hQ,
      nativeCoordinateSeparationBudget, separationBudget, nativeDependentDenominatorBudget,
      nativeDependentSlowBudget] using hbudget P hP
  have hinput := nativeCoordinateInputBudget_nonneg s hP
  have hdep := nativeDependentBudget_nonneg s hP
  have hcut : 0 ≤ nativeCoordinateSeparationBudget s P :=
    add_nonneg (separationBudget_nonneg hinput) (separationBudget_nonneg hdep)
  have hden : 0 ≤ ((s : ℝ) + 1) * nativeDependentDenominatorBudget s P := by
    unfold nativeDependentDenominatorBudget
    positivity
  have hslow : 0 ≤ nativeDependentSlowBudget s P := by
    unfold nativeDependentSlowBudget
    positivity
  have hf : 0 ≤ (P + 3) ^ 7 := by positivity
  exact ⟨by linarith only [hsum, hden, hslow, hf],
    by linarith only [hsum, hcut, hslow, hf],
    by linarith only [hsum, hcut, hden, hf],
    by linarith only [hsum, hcut, hden, hslow]⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonAnchorPolynomialCorrections
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

namespace DegreeRankLieFiltration

theorem positiveUnivariate_horizontal_mem {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : ∀ d : Fin s,
      (F.layer (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (d.val + 1))) 1).baseChange ℝ) :
    positiveUnivariate (fun d => (v d).val) ∈
      F.realification.associatedDegree.adaptedLieSubalgebra (fun _ : Unit => 1) := by
  apply positiveUnivariate_coefficients_mem
  intro d
  change (v d).val ∈
    (F.layer (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (d.val + 1))) 0).baseChange ℝ
  rw [F.rank_zero_eq_one]
  exact (v d).property

end DegreeRankLieFiltration

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

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

namespace NilpotentLieFiltration

theorem polynomialOrbitEval_zero_iff_coefficient_zero
    {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) (g : F.PolynomialOrbit w) :
    F.polynomialOrbitEval w 0 g = 1 ↔ coefficients g.log 0 = 0 := by
  constructor
  · intro h
    have hc := congrArg NilpotentLieBCHGroup.coord h
    simpa only [F.polynomialOrbitEval_coord, Pi.zero_apply, Int.cast_zero,
      eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using hc
  · intro h
    apply NilpotentLieBCHGroup.ext
    simpa only [F.polynomialOrbitEval_coord, Pi.zero_apply, Int.cast_zero,
      eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using h

end NilpotentLieFiltration

theorem toAdd_hom_corrected_factor {G V : Type*} [Group G] [AddCommGroup V]
    (f : G →* Multiplicative V) (g₀ ε g γ : G) :
    Multiplicative.toAdd (f (g₀⁻¹ * ε⁻¹ * g * γ⁻¹)) =
      Multiplicative.toAdd (f g) - Multiplicative.toAdd (f g₀) -
        Multiplicative.toAdd (f ε) - Multiplicative.toAdd (f γ) := by
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

namespace VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem CoefficientBound.add (b : Basis ι ℝ L) (T : σ → ℝ) {M N : ℝ}
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientBound b T M P) (hQ : CoefficientBound b T N Q) :
    CoefficientBound b T (M + N) (P + Q) := by
  intro α i
  simp only [map_add, Finsupp.add_apply]
  exact (abs_add_le _ _).trans ((add_le_add (hP α i) (hQ α i)).trans_eq (add_div _ _ _).symm)

theorem CoefficientGrid.add (b : Basis ι ℝ L) (l : ℕ)
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientGrid b l P) (hQ : CoefficientGrid b l Q) :
    CoefficientGrid b l (P + Q) := by
  intro α
  obtain ⟨a, ha⟩ := hP α
  obtain ⟨c, hc⟩ := hQ α
  refine ⟨a + c, ?_⟩
  funext i
  simp only [Pi.add_apply, Int.cast_add, map_add, Finsupp.add_apply]
  change (a i : ℝ) + (c i : ℝ) =
    (l : ℝ) * (b.repr (coefficients P α) i + b.repr (coefficients Q α) i)
  exact (congrArg₂ (· + ·) (congrFun ha i) (congrFun hc i)).trans (mul_add _ _ _).symm

end VectorPolynomial

theorem toAdd_hom_corrected_reference {G V : Type*} [Group G] [AddCommGroup V]
    (f : G →* Multiplicative V) (ε g γ : G) :
    Multiplicative.toAdd (f (ε⁻¹ * g * γ⁻¹)) =
      Multiplicative.toAdd (f g) - Multiplicative.toAdd (f ε) - Multiplicative.toAdd (f γ) := by
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

theorem sub_corrected_reference_add_errors {V : Type*} [AddCommGroup V]
    (x y a b a₀ b₀ : V) :
    x - (y - a₀ - b₀) - (a + a₀) - (b + b₀) = x - y - a - b := by
  abel

end Erdos3

end

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

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

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

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

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

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

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

scoped[Combinatorics.Additive'] notation3:max "E[" s ", " t "]" => _root_.OAI.Finset.addEnergy' s t
scoped[Combinatorics.Additive'] notation3:max "E[" s "]" => _root_.OAI.Finset.addEnergy' s s

theorem addEnergy'_eq_div_energy (s t : Finset G) :
    addEnergy' s t = (_root_.Finset.addEnergy s t : ℚ≥0) / Fintype.card G ^ 3 := rfl

theorem cast_addEnergy' (s t : Finset G) :
    (addEnergy' s t : ℝ) = (_root_.Finset.addEnergy s t : ℝ) / (Fintype.card G : ℝ) ^ 3 := by
  rw [addEnergy'_eq_div_energy]
  simp

end Finset

end

section

namespace Erdos3.BSG

open _root_.Finset _root_.OAI.Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate Indicator
  Combinatorics.Additive'

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [Semifield K] [CharZero K] [StarRing K]

def dconv (f g : G → K) : G → K :=
  fun a => 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

scoped[BSGConvolution] infixl:71 " ○ " => _root_.OAI.Erdos3.BSG.dconv

open scoped BSGConvolution

theorem dconv_eq_expect_add (f g : G → K) (a : G) :
    (f ○ g) a = 𝔼 t, f (a + t) * conj (g t) := by
  unfold dconv
  refine expect_nbij (fun x => x.2) (fun x _ => mem_univ _) ?_ ?_ fun b _ =>
    ⟨(a + b, b), mem_filter.mpr ⟨mem_univ _, add_sub_cancel_right _ _⟩, rfl⟩
  · intro x hx
    have heq : x.1 = a + x.2 := (sub_eq_iff_eq_add).mp (mem_filter.mp hx).2
    simp only [heq, Pi.conj_apply]
  · unfold Set.InjOn
    intro x hx y hy hxy
    apply Prod.ext
    · have hx' := (sub_eq_iff_eq_add).mp (mem_filter.mp hx).2
      have hy' := (sub_eq_iff_eq_add).mp (mem_filter.mp hy).2
      simp only [hx', hy', hxy]
    · exact hxy

theorem dconv_eq_expect_sub (f g : G → K) (a : G) :
    (f ○ g) a = 𝔼 t, f t * conj (g (t - a)) := by
  rw [dconv_eq_expect_add]
  symm
  refine Fintype.expect_equiv (Equiv.subRight a) _ _ fun t => ?_
  simp only [Equiv.subRight_apply]
  rw [add_comm a, sub_add_cancel]

theorem expect_dconv_mul (f g h : G → K) :
    𝔼 a, (f ○ g) a * h a = 𝔼 a, 𝔼 b, f a * conj (g b) * h (a - b) := by
  simp_rw [dconv_eq_expect_sub, expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ => Fintype.expect_equiv (Equiv.subLeft x) _ _ fun y => by simp

theorem expect_dconv (f g : G → K) :
    𝔼 a, (f ○ g) a = (𝔼 a, f a) * 𝔼 a, conj (g a) := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_dconv_mul f g 1

theorem dconv_indicator_one (f : G → K) (s : Finset G) :
    f ○ 𝟭_[s] = (∑ a ∈ s, τ (-a) f) /ℚ Fintype.card G := by
  ext
  simp [dconv_eq_expect_add, Set.indicator_apply, expect]

theorem indicator_one_dconv_indicator_one_eq_dens (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = (s ∩ (a +ᵥ t)).dens := by
  rw [← dens_vadd_finset (-a), inter_comm, vadd_finset_inter]
  simp [dconv_indicator_one, Set.indicator_apply, NNRat.smul_def, dens, div_eq_inv_mul,
    ← filter_mem_eq_inter, ← neg_vadd_mem_iff, sub_eq_add_neg]

theorem indicator_one_dconv_indicator_one_eq_addConvolution_div (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = s.addConvolution (-t) a / card G := by
  rw [indicator_one_dconv_indicator_one_eq_dens, dens, card_inter_vadd]
  simp

theorem expect_indicator_one_dconv_indicator_one (s t : Finset G) :
    𝔼 a, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) a = s.dens * t.dens := by
  simp [expect_dconv, Set.conj_indicator_one_apply]
  simp [← Pi.one_def]

theorem expect_indicator_one_dconv_indicator_sq (s t : Finset G) :
    𝔼 x, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) x ^ 2 = E[s, t] := by
  suffices
      ∑ x, #{yz ∈ s ×ˢ t | yz.1 - yz.2 = x} ^ 2 =
        #{x ∈ (s ×ˢ s) ×ˢ t ×ˢ t | x.1.1 + x.2.1 = x.1.2 + x.2.2} by
    simp only [expect, card_univ, indicator_one_dconv_indicator_one_eq_dens, dens, NNRat.cast_div,
      NNRat.cast_natCast, sq, div_mul_div_comm, ← sum_div, NNRat.smul_def, NNRat.cast_inv,
      addEnergy', NNRat.cast_pow, card_inter_vadd, ← card_sub_eq]
    field_simp
    norm_cast
  simp only [_root_.Finset.card_eq_sum_ones, sq, Finset.sum_mul_sum, sum_filter, sum_product, boole_mul,
    univ.sum_comm, Finset.sum_ite_eq, mem_univ, ite_true, sub_eq_sub_iff_add_eq_add]
  exact sum_comm

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open _root_.Finset _root_.OAI.Finset Function
open scoped ComplexConjugate BSGConvolution

variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [Semifield K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
  [StarRing K] [StarOrderedRing K] {f g : G → K}

omit [IsStrictOrderedRing K] in
theorem dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  fun _ => expect_nonneg fun x _ => mul_nonneg (hf x.1) (star_nonneg_iff.mpr (hg x.2))

omit [IsStrictOrderedRing K] in
theorem dconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ○ g) a :=
  dconv_nonneg hf hg a

theorem dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  change 0 < f a at ha
  change 0 < g b at hb
  refine ⟨dconv_nonneg hf hg, a - b, ?_⟩
  change 0 < (f ○ g) (a - b)
  rw [dconv_eq_expect_add]
  apply expect_pos' (fun x _ => mul_nonneg (hf (a - b + x)) (star_nonneg_iff.mpr (hg x)))
  refine ⟨b, mem_univ _, ?_⟩
  rw [sub_add_cancel]
  exact mul_pos ha (star_pos_iff.mpr hb)

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open _root_.Finset hiding card
open _root_.OAI.Finset
open Fintype
open scoped BigOperators Pointwise Combinatorics.Additive' Indicator BSGConvolution

section
variable {α : Type*} [Fintype α] [DecidableEq α] {H : Finset (α × α)} {A B X : Finset α} {a b x : α}
  {K : ℝ}

omit [Fintype α] in
lemma oneOfPair_aux (hH : H ⊆ X ×ˢ X) : #{yz ∈ H | yz.1 = x} = #{c ∈ X | (x, c) ∈ H} := by
  refine card_nbij' Prod.snd (fun c ↦ (x, c)) ?_ (by simp [Set.MapsTo])
    (by grind [Set.LeftInvOn]) (by simp [Set.LeftInvOn])
  simpa +contextual [Set.MapsTo, eq_comm] using fun a b hab _ ↦ (mem_product.1 (hH hab)).2

noncomputable def oneOfPair (H : Finset (α × α)) (X : Finset α) : Finset α :=
  {x ∈ X | (3 / 4 : ℝ) * X.dens ≤ {c ∈ X | (x, c) ∈ H}.dens}

lemma oneOfPair_subset : oneOfPair H X ⊆ X := filter_subset ..

lemma mem_oneOfPair :
    x ∈ oneOfPair H X ↔ x ∈ X ∧ (3 / 4 : ℝ) * X.dens ≤ {c ∈ X | (x, c) ∈ H}.dens := mem_filter

lemma oneOfPair_bound_one :
    (∑ x ∈ X \ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α ≤ (3 / 4) * X.dens ^ 2 := calc
  _ ≤ (∑ _x ∈ X \ oneOfPair H X, 3 / 4 * X.dens : ℝ) / card α := by
    gcongr
    grind [oneOfPair]
  _ = (X \ oneOfPair H X).dens * (3 / 4 * X.dens) := by simp [dens]; ring
  _ ≤ X.dens * (3 / 4 * X.dens) := by grw [sdiff_subset]
  _ = _ := by ring

lemma oneOfPair_bound_two (hH : H ⊆ X ×ˢ X) (Hcard : (7 / 8 : ℝ) * X.dens ^ 2 ≤ H.dens) :
    (1 / 8 : ℝ) * X.dens ^ 2 ≤ X.dens * (oneOfPair H X).dens := calc
  _ ≤ H.dens - (3 / 4 : ℝ) * X.dens ^ 2 := by linarith
  _ ≤ H.dens - (∑ x ∈ X \ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    gcongr; exact oneOfPair_bound_one
  _ = H.dens - (∑ x ∈ X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α
    + (∑ x ∈ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    rw [sum_sdiff_eq_sub oneOfPair_subset, sub_add, sub_div]
  _ = (∑ x ∈ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    simp only [dens, Fintype.card_prod, Nat.cast_mul, NNRat.cast_div, NNRat.cast_natCast,
      NNRat.cast_mul, ← sum_div, div_div, add_eq_right, sub_eq_zero, ← oneOfPair_aux hH]
    norm_cast
    rw [← card_eq_sum_card_fiberwise fun x hx ↦ (mem_product.1 (hH hx)).1]
  _ ≤ (∑ _x ∈ oneOfPair H X, (X.dens : ℝ)) / card α := by gcongr with i; exact filter_subset ..
  _ = X.dens * (oneOfPair H X).dens := by simp [dens]; ring

lemma oneOfPair_bound (hH : H ⊆ X ×ˢ X) (hX : X.Nonempty)
    (Hcard : (7 / 8 : ℝ) * X.dens ^ 2 ≤ H.dens) (h : A.dens / (2 * K) ≤ X.dens) :
    A.dens / (2 ^ 4 * K : ℝ) ≤ (oneOfPair H X).dens := calc
    _ = (A.dens / (2 * K) : ℝ) / 8 := by ring
    _ ≤ (X.dens / 8 : ℝ) := by gcongr
    _ ≤ (oneOfPair H X).dens :=
      le_of_mul_le_mul_left ((oneOfPair_bound_two hH Hcard).trans_eq' (by ring)) <| by positivity

lemma quadruple_bound_c {a b : α} (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X) :
    (X.dens : ℝ) / 2 ≤ {c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.dens := by
  rw [mem_oneOfPair] at ha hb
  rw [filter_and, cast_dens_inter, ← filter_or]
  have : ({c ∈ X | (a, c) ∈ H ∨ (b, c) ∈ H}.dens : ℝ) ≤ X.dens := by grw [filter_subset]
  linarith [ha.2, hb.2, this]

end

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A B : Finset G} {x : G}

omit [Fintype G] in
lemma quadruple_bound_right {a b : G} (H : Finset (G × G)) (X : Finset G) (h : x = a - b) :
    (#({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦ ((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) : ℝ)
      ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = a - b) := by
  rw [← h, Nat.cast_le]
  refine card_le_card_of_injOn Sigma.snd (by simp +contextual [Set.MapsTo, *]) ?_
  simp +contextual [Set.InjOn]
  aesop

variable {K : Type*} [Semifield K] [CharZero K] [StarRing K]

section lemma1

lemma claim_one : 𝔼 x : G, (𝟭_[A, K] ○ 𝟭_[B]) x * (A ∩ (x +ᵥ B)).dens = E[A, B] := by
  simp only [← expect_indicator_one_dconv_indicator_sq, ← indicator_one_dconv_indicator_one_eq_dens,
    sq]

lemma claim_two :
    (E[A, B]) ^ 2 / (A.dens * B.dens) ≤
      𝔼 x, (𝟭_[(A : Set G), ℝ] ○ 𝟭_[B]) x * (A ∩ (x +ᵥ B)).dens ^ 2 := by
  let f := fun x ↦ ((𝟭_[(A : Set G), ℝ] ○ 𝟭_[B]) x).sqrt
  have hf : ∀ x, f x ^ 2 = (𝟭_[A, ℝ] ○ 𝟭_[B]) x := by
    intro x
    rw [Real.sq_sqrt]
    exact dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have := expect_mul_sq_le_sq_mul_sq univ f (fun x ↦ f x * (A ∩ (x +ᵥ B)).dens)
  refine div_le_of_le_mul₀ (by positivity) ?_ ?_
  · refine expect_nonneg fun i _ ↦ ?_

    exact mul_nonneg (dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg _)
      (by positivity)
  simp only [← sq, ← mul_assoc, hf, expect_indicator_one_dconv_indicator_one, mul_pow, claim_one]
    at this
  grind

lemma claim_three {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H).dens =
      (∑ ab ∈ H, 𝔼 x, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] (ab.1 - x) * 𝟭_[B] (ab.2 - x)))
        / card G ^ 2 := by
  simp only [dens, Fintype.card_prod, Nat.cast_mul, NNRat.cast_div, NNRat.cast_natCast,
    NNRat.cast_mul, mul_div, Fintype.expect_eq_sum_div_card, ← sum_div]
  field_simp
  simp only [sum_comm (s := H), mul_sum, _root_.Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  congr! 1 with x
  rw [inter_comm, ← filter_mem_eq_inter, sum_filter]
  congr! 1 with ⟨a, b⟩ hab
  have : a ∈ A ∧ b ∈ A := by simpa using hH hab
  simp [this, Set.indicator_apply, ← neg_vadd_mem_iff, neg_add_eq_sub]
  grind

lemma claim_four (ab : G × G) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] (ab.1 - x) * 𝟭_[B] (ab.2 - x)) ≤
      B.dens * (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) := by
  obtain ⟨a, b⟩ := ab
  have (x : G) : (𝟭_[A, ℝ] ○ 𝟭_[B]) x ≤ B.dens := by
    simp only [dconv_eq_expect_add, Set.conj_indicator_one_apply, dens,
      Fintype.expect_eq_sum_div_card, NNRat.cast_div, NNRat.cast_natCast]
    gcongr
    simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    simp only [Set.indicator_apply, mul_boole, SetLike.mem_coe,
      ← sum_filter (· ∈ B), filter_mem_eq_inter, univ_inter]
    gcongr with i
    grind
  have : 𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] ((a, b).1 - x) * 𝟭_[B] ((a, b).2 - x)) ≤
    B.dens * 𝔼 x : G, (𝟭_[B] ((a, b).1 - x) * 𝟭_[B] ((a, b).2 - x)) := by
    rw [mul_expect]
    gcongr with s hs
    · exact mul_nonneg Set.indicator_one_apply_nonneg Set.indicator_one_apply_nonneg
    · exact this _
  refine this.trans_eq ?_
  congr 1
  simp only [dconv_eq_expect_add]
  exact Fintype.expect_equiv (Equiv.subLeft b) _ _ <| by simp

lemma claim_five {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H).dens ≤
      B.dens * (∑ ab ∈ H, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2)) / card G ^ 2 := by
  rw [claim_three hH, mul_sum]; gcongr; exact claim_four _

noncomputable def choiceH (A B : Finset G) (c : ℝ) : Finset (G × G) :=
  {ab ∈ A ×ˢ A |
    (𝟭_[B, ℝ] ○ 𝟭_[B]) (ab.1 - ab.2) ≤ c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))}

lemma choiceH_subset {c : ℝ} : choiceH A B c ⊆ A ×ˢ A := filter_subset ..

lemma claim_six (c : ℝ) (hc : 0 ≤ c) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens ≤
      c / 2 * (E[A, B] ^ 2 / (A.dens * B.dens)) := by
  have : ∑ ab ∈ choiceH A B c, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) ≤
      #(choiceH A B c) * (c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2
  replace : (∑ ab ∈ choiceH A B c, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2)) / card G ^ 2 ≤
      (choiceH A B c).dens * (c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))) := by
    grw [this, mul_div_right_comm]; simp [dens, sq]
  have hH : ((choiceH A B c).dens : ℝ) ≤ A.dens ^ 2 := by grw [choiceH_subset]; simp [sq]
  grw [claim_five choiceH_subset, ← mul_div, this, hH]
  field_simp
  rfl

lemma claim_seven {c : ℝ} (hc : 0 ≤ c) :
    𝔼 x : G,
      (𝟭_[A, ℝ] ○ 𝟭_[B]) x *
          ((c / 2) * (E[A, B] ^ 2 / (A.dens ^ 2 * B.dens ^ 2)) +
            ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens) ≤
      𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (c * (A ∩ (x +ᵥ B)).dens ^ 2) :=
  calc
    _ = (c / 2 * (E[A, B] ^ 2 / (A.dens * B.dens))) + 𝔼 x : G,
          (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens := by
        simp only [mul_add, expect_add_distrib, expect_indicator_one_dconv_indicator_one,
          ← expect_mul, ← mul_pow]
        field_simp
    _ ≤ _ := by
      grw [claim_six c hc, ← add_mul, add_halves]
      simp only [mul_left_comm _ c, ← mul_expect]
      gcongr
      exact claim_two

lemma claim_eight {c : ℝ} (hc : 0 ≤ c) (A B : Finset G) :
    ∃ x : G, ((c / 2) * (E[A, B] ^ 2 / (A.dens ^ 2 * B.dens ^ 2)) +
          ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens) ≤
      c * (A ∩ (x +ᵥ B)).dens ^ 2 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  by_contra!
  refine (claim_seven hc (A := A) (B := B)).not_gt <| expect_lt_expect (fun x _ ↦ ?_) ?_
  · grw [this x]
    exact dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have : 0 < 𝟭_[(A : Set G), ℝ] ○ 𝟭_[B] := by apply dconv_pos <;> simpa
  rw [Pi.lt_def] at this
  obtain ⟨-, i, hi : 0 < _⟩ := this
  exact ⟨i, by simp, mul_lt_mul_of_pos_left (this i) hi⟩

lemma lemma_one {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hE : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B])
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x : G, ∃ X ⊆ A ∩ (x +ᵥ B), A.dens / (Real.sqrt 2 * K) ≤ X.dens ∧
      (1 - c) * X.dens ^ 2 ≤
      ((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.dens ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)).dens := by
  obtain ⟨x, hx⟩ := claim_eight hc.le A B
  set X := A ∩ (x +ᵥ B)
  refine ⟨x, X, subset_rfl, ?_, ?_⟩
  · have : (2 : ℝ)⁻¹ * (E[A, B] / (A.dens * B.dens)) ^ 2 ≤ X.dens ^ 2 := by
      refine le_of_mul_le_mul_left (hx.trans' ?_) hc
      exact (le_add_of_nonneg_right <| NNRat.cast_nonneg _).trans_eq' (by ring)
    grw [← sq_le_sq₀ (by positivity) (by positivity), ← this, ← hE]

    field_simp
    norm_num
  rw [one_sub_mul, sub_le_comm]
  refine ((le_add_of_nonneg_left (by positivity)).trans hx).trans' ?_
  rw [sq, ← NNRat.cast_mul, ← dens_product, ← cast_dens_sdiff (filter_subset _ _), ← filter_not,
    ← filter_mem_eq_inter]
  gcongr ↑(dens ?_)
  rintro ⟨a, b⟩
  simp +contextual only [not_le, mem_product, mem_inter, and_imp, mem_filter, choiceH, and_self,
    true_and, X]
  rintro _ _ _ _ h
  grw [h, ← hE]
  apply le_of_eq
  field_simp [hA, hB, hK, le_div_iff₀, div_le_iff₀] at hE ⊢

lemma lemma_one' {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hE : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B])
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x : G, ∃ X ⊆ A ∩ (x +ᵥ B), A.dens / (2 * K) ≤ X.dens ∧
      (1 - c) * X.dens ^ 2 ≤
      ((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.dens ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)).dens := by
  obtain ⟨x, X, hX₁, hX₂, hX₃⟩ := lemma_one hc hK hE hA hB
  refine ⟨x, X, hX₁, hX₂.trans' ?_, hX₃⟩
  gcongr _ / (?_ * _)
  rw [Real.sqrt_le_iff]
  norm_num

end lemma1

section lemma2
variable {H : Finset (G × G)} {X : Finset G}

lemma quadruple_bound_other {a b c : G} {K : ℝ} {H : Finset (G × G)}
    (hac : (a, c) ∈ H) (hbc : (b, c) ∈ H)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    (A.dens / (2 ^ 4 * K ^ 2)) ^ 2 ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 2 := by
  rw [filter_product (s := B ×ˢ B) (t := B ×ˢ B) (fun z ↦ z.1 - z.2 = a - c)
    (fun z ↦ z.1 - z.2 = b - c), card_product, sq, sq (card G : ℝ), Nat.cast_mul,
      mul_div_mul_comm]
  gcongr ?_ * ?_
  · grw [card_sub_eq, hH _ hac, indicator_one_dconv_indicator_one_eq_addConvolution_div]
  · grw [card_sub_eq, hH _ hbc, indicator_one_dconv_indicator_one_eq_addConvolution_div]

lemma quadruple_bound_left {a b : G} {K : ℝ} {H : Finset (G × G)}
    (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    X.dens / 2 * (A.dens / (2 ^ 4 * K ^ 2)) ^ 2 ≤
      #({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦
      ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 3  :=
  calc
    _ ≤ (∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, ((A.dens / (2 ^ 4 * K ^ 2)) ^ 2 : ℝ))
      / card G := by
      grw [sum_const, quadruple_bound_c ha hb]
      apply le_of_eq
      simp [dens]
      ring
    _ ≤ (∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, #(((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ((a₁, a₂), a₃, a₄) ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 2 : ℝ)
          / card G := by
      gcongr with i hi
      simp only [mem_filter] at hi
      convert quadruple_bound_other hi.2.1 hi.2.2 hH
    _ = _ := by rw [_root_.Finset.card_sigma, Nat.cast_sum, ← sum_div]; ring

lemma quadruple_bound {K : ℝ} {x : G} (hx : x ∈ oneOfPair H X - oneOfPair H X)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    (A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4) ≤
      #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
      card G ^ 3 := by
  rw [mem_sub] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  grw [← quadruple_bound_right H X rfl, ← quadruple_bound_left ha hb hH]
  apply le_of_eq
  ring

lemma big_quadruple_bound {K : ℝ}
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2))
    (hX : A.dens / (2 * K) ≤ X.dens) :
    (oneOfPair H X - oneOfPair H X).dens * (A.dens ^ 3 / (2 ^ 10 * K ^ 5)) ≤ B.dens ^ 4 :=
  calc
    _ = (oneOfPair H X - oneOfPair H X).dens * ((A.dens ^ 2 * (A.dens / (2 * K)))
      / (2 ^ 9 * K ^ 4)) := by ring
    _ ≤ (oneOfPair H X - oneOfPair H X).dens * ((A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4)) := by
      gcongr
    _ = (∑ _x ∈ oneOfPair H X - oneOfPair H X, (A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4) : ℝ)
      / card G := by simp [dens]; ring
    _ ≤ (∑ x ∈ oneOfPair H X - oneOfPair H X,
          #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
            card G ^ 3 : ℝ)
      / card G := by gcongr (∑ _ ∈ _, ?_) / _ with x hx; exact quadruple_bound hx hH
    _ ≤ 𝔼 x, (#(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
          card G ^ 3 : ℝ) := by grw [Fintype.expect_eq_sum_div_card, ← subset_univ]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, ← sum_div]
      norm_cast
      rw [← card_eq_sum_card_fiberwise (by simp [Set.mapsTo_univ])]
      simp [dens]
      field_simp

lemma BSG_aux {K : ℝ} (hK : 0 < K) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B]) :
    ∃ x : G, ∃ A' ⊆ A ∩ (x +ᵥ B), (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧
      (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * B.dens ^ 4 / A.dens ^ 3 := by
  obtain ⟨x, X, hX₁, hX₂, hX₃⟩ := lemma_one' (c := 1 / 8) (by norm_num) hK hAB hA hB
  set H : Finset (G × G) := (X ×ˢ X).filter
    fun ⟨a, b⟩ ↦ A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)
  have : (0 : ℝ) < X.dens := hX₂.trans_lt' (by positivity)
  refine ⟨x, oneOfPair H X, (filter_subset _ _).trans hX₁, ?_, ?_⟩
  · rw [← mul_inv, inv_mul_eq_div]
    refine oneOfPair_bound (filter_subset _ _) (by simpa using this) ?_ hX₂
    convert hX₃ using 2
    · norm_num
    · unfold H
      ring_nf
  have := big_quadruple_bound (H := H) (fun x hx ↦ (mem_filter.1 hx).2) hX₂
  rw [le_div_iff₀ (by positivity)]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at this
  grind

end lemma2

theorem balogSzemerediGowers {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧
      (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * B.dens ^ 4 / A.dens ^ 3 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hK := eq_or_lt_of_le hK
  · simp
  · grind [BSG_aux]

theorem BSG_self {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.dens ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧ (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * A.dens := by
  convert balogSzemerediGowers hK hA ?_ using 5 <;> grind

theorem BSG_self' {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.dens ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧ (A' - A').dens ≤ 2 ^ 14 * K ^ 6 * A'.dens := by
  obtain ⟨A', hA', hAA', hAK'⟩ := BSG_self hK hA hAK
  refine ⟨A', hA', hAA', hAK'.trans ?_⟩
  calc
    _ = 2 ^ 14 * K ^ 6 * ((2 ^ 4)⁻¹ * K⁻¹ * A.dens) := ?_
    _ ≤ _ := by gcongr
  grind

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
theorem density_mul_le_iff_card_mul_le (s t : Finset G) (c : ℝ) :
    c * (s.dens : ℝ) ≤ t.dens ↔ c * (s.card : ℝ) ≤ t.card := by
  simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast]
  rw [← mul_div_assoc]
  exact div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos (α := G))

omit [DecidableEq G] in
theorem density_le_mul_iff_card_le_mul (s t : Finset G) (c : ℝ) :
    (s.dens : ℝ) ≤ c * t.dens ↔ (s.card : ℝ) ≤ c * t.card := by
  simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast]
  rw [← mul_div_assoc]
  exact div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos (α := G))

theorem exists_large_subset_small_difference (A : Finset G) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (henergy : K⁻¹ * (A.card : ℝ) ^ 3 ≤ (Finset.addEnergy A A : ℝ)) :
    ∃ S ⊆ A, S.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ (S.card : ℝ) ∧
      ((S - S).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * S.card := by
  have he : K⁻¹ * (A.dens : ℝ) ^ 3 ≤ (Finset.addEnergy' A A : ℝ) := by
    rw [Finset.cast_addEnergy']
    simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, div_pow]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right henergy (by positivity)
  obtain ⟨S, hSA, hsize, hsmall⟩ := BSG_self' hK.le hA he
  have hsize' := (density_mul_le_iff_card_mul_le A S ((2 ^ 4 : ℝ)⁻¹ * K⁻¹)).mp
    (by simpa only [mul_assoc] using hsize)
  have hsmall' := (density_le_mul_iff_card_le_mul (S - S) S ((2 ^ 14 : ℝ) * K ^ 6)).mp
    (by simpa only [mul_assoc] using hsmall)
  have hpos : (0 : ℝ) < S.card :=
    (mul_pos (mul_pos (by positivity) (inv_pos.mpr hK))
      (by exact_mod_cast hA.card_pos)).trans_le hsize'
  exact ⟨S, hSA, Finset.card_pos.mp (by exact_mod_cast hpos), hsize', hsmall'⟩

end Erdos3.BSG

end

section

namespace Erdos3

open scoped Pointwise

variable {G V : Type*} [DecidableEq G] [DecidableEq V]

theorem mem_additiveGraph_iff (H : Finset G) (b : G → V) (x : G × V) :
    x ∈ additiveGraph H b ↔ x.1 ∈ H ∧ x.2 = b x.1 := by
  rw [additiveGraph, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hh, rfl⟩
  · intro hx
    exact ⟨x.1, hx.1, Prod.ext rfl hx.2.symm⟩

theorem additiveGraph_image_fst (H : Finset G) (b : G → V) (S : Finset (G × V))
    (hS : S ⊆ additiveGraph H b) : additiveGraph (S.image Prod.fst) b = S := by
  ext x
  rw [mem_additiveGraph_iff]
  constructor
  · rintro ⟨hx, he⟩
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    have hgy := (mem_additiveGraph_iff H b y).mp (hS hy)
    have hxy : x = y := Prod.ext hyx.symm (by rw [he, ← hyx, hgy.2])
    exact hxy.symm ▸ hy
  · intro hx
    exact ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, ((mem_additiveGraph_iff H b x).mp (hS hx)).2⟩

variable [AddCommGroup G] [Fintype G] [AddCommGroup V] [Fintype V]

theorem exists_large_graph_subset_small_difference
    (H : Finset G) (hH : H.Nonempty) (b : G → V) {K : ℝ} (hK : 0 < K)
    (henergy : K⁻¹ * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H b) (additiveGraph H b) : ℝ)) :
    ∃ J ⊆ H, J.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ (J.card : ℝ) ∧
      ((additiveGraph J b - additiveGraph J b).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * J.card := by
  obtain ⟨S, hS, hSn, hsize, hdiff⟩ := BSG.exists_large_subset_small_difference
    (additiveGraph H b) (hH.image _) hK (by simpa only [additiveGraph_card] using henergy)
  let J := S.image Prod.fst
  have hgraph : additiveGraph J b = S := additiveGraph_image_fst H b S hS
  have hcard : S.card = J.card := by rw [← hgraph, additiveGraph_card]
  refine ⟨J, ?_, hSn.image _, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact ((mem_additiveGraph_iff H b y).mp (hS hy)).1
  · simpa only [additiveGraph_card, hcard] using hsize
  · rw [hgraph, ← hcard]
    exact hdiff

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData

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


