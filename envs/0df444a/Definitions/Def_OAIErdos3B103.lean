-- Prove2me | Definitions.Def_OAIErdos3B103
-- name    : OAIErdos3B103
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T19:16:59.455892+00:00
-- url     : https://prove2.me/theorems/1f36698a-1a05-4790-a80c-26b4be050249
-- title:
--   OpenAI Erdős-3 split, definitions bundle 104 of 106
-- statement:
--   Definitions bundle 104 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B102`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 104 available.
--
--   Modules: `OAI.Erdos3.BasisBlockInvariant.coarser`, `OAI.Erdos3.BasisBlockInvariant.graded`, `OAI.Erdos3.NilpotentLieFiltration.RealAdaptedCoefficientGrid`, `OAI.Erdos3.NilpotentLieFiltration.adaptedFullPolynomialHom`, `OAI.Erdos3.NilpotentLieFiltration.adaptedFullPolynomialHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.bch_triple_remainder_mem_subalgebra_sup_layer`, `OAI.Erdos3.NilpotentLieFiltration.bracket_mem_subalgebra_sup_layer_succ`, `OAI.Erdos3.NilpotentLieFiltration.comparison_middle_identity`, `OAI.Erdos3.NilpotentLieFiltration.compatible_factors_mem_mod_layer_of_separation`, `OAI.Erdos3.NilpotentLieFiltration.controlled_compatible_factors_mem`, `OAI.Erdos3.NilpotentLieFiltration.controlled_compatible_factors_mod_layer`, `OAI.Erdos3.NilpotentLieFiltration.controlled_outer_factors_mem`, `OAI.Erdos3.NilpotentLieFiltration.controlled_separation_at_layer`, `OAI.Erdos3.NilpotentLieFiltration.exists_adapted_polynomial_list_lift`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_fast_coefficient_generators`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_reduced_fast_kernel_generators`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_symbol_comparison`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_symbol_grade_corrections`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_symbol_comparison`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_symbol_comparison_mod_layer`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_symbol_grade_step`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_polynomial_product_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_polynomial_product_grid`, `OAI.Erdos3.NilpotentLieFiltration.exists_outer_polynomial_product_bounds`, `OAI.Erdos3.NilpotentLieFiltration.exists_real_adapted_representation`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule_monomial_blocks`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule_spanning`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule_spanning_height`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomial_mem_adapted`, `OAI.Erdos3.NilpotentLieFiltration.outer_factors_mem_mod_layer_of_separation`, `OAI.Erdos3.NilpotentLieFiltration.outer_factors_mem_of_separation`, `OAI.Erdos3.NilpotentLieFiltration.outer_sum_mem_of_identity_mod_layer`, `OAI.Erdos3.NilpotentLieFiltration.outer_sum_mem_subalgebra_sup_layer`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_iff_formal`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_iff_formal`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedCoefficientBound_iff_formal`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedCoefficientGrid_iff_formal`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedCoefficientGrid_mono`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedCoefficientGrid_polynomial_iff`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedDirectionalDerivative_grid`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotient_mem_iff`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareEquiv`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareEquiv_fst`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareEquiv_snd`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareEquiv_tmul`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareLieEquiv`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap_height`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSnd_kernel_monomial_blocks`, `OAI.Erdos3.NilpotentLieFiltration.shiftedGradedPolynomial_mem_adapted`, `OAI.Erdos3.NilpotentLieFiltration.symbol_current_grade_residual_mem`, `OAI.Erdos3.VectorPolynomial.CoefficientBound`, `OAI.Erdos3.VectorPolynomial.CoefficientBound.mono`, `OAI.Erdos3.VectorPolynomial.CoefficientBound.neg`, `OAI.Erdos3.VectorPolynomial.CoefficientBound.sub`, `OAI.Erdos3.VectorPolynomial.CoefficientGrid`, `OAI.Erdos3.VectorPolynomial.CoefficientGrid.sub`, `OAI.Erdos3.VectorPolynomial.coefficientBound_iff_norm`, `OAI.Erdos3.VectorPolynomial.positiveUnivariate`, `OAI.Erdos3.VectorPolynomial.positiveUnivariate_coefficient`, `OAI.Erdos3.VectorPolynomial.positiveUnivariate_coefficientBound`, `OAI.Erdos3.VectorPolynomial.positiveUnivariate_coefficientGrid`, `OAI.Erdos3.VectorPolynomial.positiveUnivariate_coefficient_eq_zero`, `OAI.Erdos3.VectorPolynomial.positiveUnivariate_coefficients_mem`, `OAI.Erdos3.VectorPolynomial.positiveUnivariate_zero`, `OAI.Erdos3.basisCoordinateProjection_coarser_block`, `OAI.Erdos3.fastCoefficientGeneratorHeight`, `OAI.Erdos3.fastKernelGeneratorHeight`, `OAI.Erdos3.sectionCorrectedPolynomial`, `OAI.Erdos3.sectionCorrectedPolynomial_coefficientBound`, `OAI.Erdos3.sectionCorrectedPolynomial_coefficientGrid`, `OAI.Erdos3.sectionCorrectedPolynomial_coefficient_grid`, `OAI.Erdos3.sectionCorrectedPolynomial_coefficient_norm`, `OAI.Erdos3.sectionCorrectedPolynomial_coefficients`, `OAI.Erdos3.sectionCorrectedPolynomial_denominator_bounds`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B026
import Definitions.Def_OAIErdos3B027

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientBlocks
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι δ ε : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisCoordinateProjection_coarser_block (b : Basis ι K V) (c : ι → δ)
    (f : δ → ε) (d : δ) (e : ε) [Decidable (f d = e)] (x : V) :
    basisCoordinateProjection b {i | f (c i) = e}
      (basisCoordinateProjection b {i | c i = d} x) =
      if f d = e then basisCoordinateProjection b {i | c i = d} x else 0 := by
  classical
  apply b.repr.injective
  ext i
  by_cases hi : c i = d <;> by_cases hd : f d = e <;>
    simp_all [basisCoordinateProjection_repr]

theorem BasisBlockInvariant.coarser [Fintype ι]
    (b : Basis ι K V) (c : ι → δ) (U : Submodule K V)
    (hU : BasisBlockInvariant b c U) (f : δ → ε) :
    BasisBlockInvariant b (fun i => f (c i)) U := by
  classical
  intro e x hx
  rw [← sum_basisBlockProjection b c x, map_sum]
  apply U.sum_mem
  intro d _
  rw [basisCoordinateProjection_coarser_block]
  split_ifs
  · exact hU d x hx
  · exact U.zero_mem

theorem BasisBlockInvariant.graded [Fintype ι]
    (b : Basis ι K V) (c : ι → δ) (U : Submodule K V)
    (hU : BasisBlockInvariant b c U) (f : δ → ℕ) :
    BasisGradedSubmodule b (fun i => f (c i)) U :=
  hU.coarser b c U f

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareSnd_kernel_monomial_blocks :
    BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1)
      (F.reducedSquareSndSymbolMap w).ker.toSubmodule :=
  basisBlockInvariant_ker (F.reducedSquareSymbolBasis e ω hF w)
    (F.quotientTopSymbolBasis e ω hF w) (fun z => z.val.1) (fun z => z.val.1)
    (F.reducedSquareSndSymbolMap w).toLinearMap (F.reducedSquareSndSymbolMap_monomial_blocks e ω hF w)

theorem firstCoefficientFastSubmodule_monomial_blocks (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U) :
    BasisBlockInvariant (F.firstCoefficientBasis e ω hF w) (fun z => z.val.1)
      (F.firstCoefficientFastSubmodule w hw U) := by
  rw [F.firstCoefficientFastSubmodule_eq_image]
  apply BasisBlockInvariant.map (F.reducedSquareSymbolBasis e ω hF w)
    (F.firstCoefficientBasis e ω hF w) (fun z => z.val.1) (fun z => z.val.1)
    (F.reducedSquareCoefficientMap w) (F.reducedSquareCoefficientMap_monomial_blocks e ω hF w)
  exact hU.inf _ _ _ _ (F.reducedSquareSnd_kernel_monomial_blocks e ω hF w)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FastCoefficientSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareCoefficientMap_height [Fintype (ReducedSquareSymbolIndex s w ω)]
    {H : ℕ} (x : F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : ∀ i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr x i) H)
    (j : FirstCoefficientIndex w ω) :
    RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (F.reducedSquareCoefficientMap w x) j)
      ((Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
        H ^ Fintype.card (ReducedSquareSymbolIndex s w ω)) := by
  simpa only [mul_one] using linearMap_coordinate_height
    (F.reducedSquareSymbolBasis e ω hF w) (F.firstCoefficientBasis e ω hF w)
    (F.reducedSquareCoefficientMap w) (F.reducedSquareCoefficientMap_basis_height e ω hF w) x hx j

theorem firstCoefficientFastSubmodule_spanning (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hv : Submodule.span ℚ (Set.range v) = U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule) :
    Submodule.span ℚ (Set.range (fun i => F.reducedSquareCoefficientMap w (v i))) =
      F.firstCoefficientFastSubmodule w hw U := by
  rw [F.firstCoefficientFastSubmodule_eq_image, ← hv, Submodule.map_span, ← Set.range_comp]
  rfl

theorem firstCoefficientFastSubmodule_spanning_height [Fintype (ReducedSquareSymbolIndex s w ω)]
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule)
    {H : ℕ} (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H) :
    ∃ z : κ → F.FirstCoefficientModule w,
      Submodule.span ℚ (Set.range z) = F.firstCoefficientFastSubmodule w hw U ∧
      ∀ i j, RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (z i) j)
        ((Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
          H ^ Fintype.card (ReducedSquareSymbolIndex s w ω)) :=
  ⟨fun i => F.reducedSquareCoefficientMap w (v i),
    F.firstCoefficientFastSubmodule_spanning w hw U v hspan,
    fun i j => F.reducedSquareCoefficientMap_height e ω hF w (v i) (hv i) j⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedFastCoefficientGenerators
namespace OAI

section

namespace Erdos3

def fastKernelGeneratorHeight (n m r H : ℕ) : ℕ :=
  (m + 1) * (rationalKernelHeight r ((n + 1) * H ^ n) * H) ^ m

def fastCoefficientGeneratorHeight (n m r H : ℕ) : ℕ :=
  (n + 1) * fastKernelGeneratorHeight n m r H ^ n

namespace NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]

theorem exists_bounded_reduced_fast_kernel_generators
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopSymbolIndex s w ω) ∧
      ∃ z : κ → F.squareFiltration.quotientTop.PolynomialSymbol w,
        Submodule.span ℚ (Set.range z) = U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule ∧
        ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (z i) j)
          (fastKernelGeneratorHeight (Fintype.card (ReducedSquareSymbolIndex s w ω))
            (Fintype.card κ) r H) := by
  have hPv (i : κ) (j : QuotientTopSymbolIndex s w ω) :
      RationalHeightLE ((F.quotientTopSymbolBasis e ω hF w).repr (F.reducedSquareSndSymbolMap w (v i)) j)
        ((Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
          H ^ Fintype.card (ReducedSquareSymbolIndex s w ω)) := by
    simpa only [mul_one, LieHom.coe_toLinearMap] using linearMap_coordinate_height
      (F.reducedSquareSymbolBasis e ω hF w) (F.quotientTopSymbolBasis e ω hF w)
      (F.reducedSquareSndSymbolMap w).toLinearMap
      (F.reducedSquareSndSymbolMap_basis_height e ω hF w) (v i) (hv i) j
  have hB : 1 ≤ (Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
      H ^ Fintype.card (ReducedSquareSymbolIndex s w ω) := by
    have hp : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
    exact Nat.succ_le_of_lt (by positivity)
  have he := exists_bounded_span_kernel_generators
    (F.reducedSquareSymbolBasis e ω hF w) (F.quotientTopSymbolBasis e ω hF w)
    (F.reducedSquareSndSymbolMap w).toLinearMap v hB hv hPv
  simpa only [hspan, fastKernelGeneratorHeight, LieHom.ker_toSubmodule] using he

theorem exists_bounded_fast_coefficient_generators (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopSymbolIndex s w ω) ∧
      ∃ z : κ → F.FirstCoefficientModule w,
        Submodule.span ℚ (Set.range z) = F.firstCoefficientFastSubmodule w hw U ∧
        ∀ i j, RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (z i) j)
          (fastCoefficientGeneratorHeight (Fintype.card (ReducedSquareSymbolIndex s w ω))
            (Fintype.card κ) r H) := by
  have he := F.exists_bounded_reduced_fast_kernel_generators e ω hF w U v hspan hH hv
  obtain ⟨r, hr, z, hz, hzh⟩ := he
  exact ⟨r, hr, F.firstCoefficientFastSubmodule_spanning_height e ω hF w hw U z hz hzh⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolCommonCorrections
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem bracket_mem_subalgebra_sup_layer_succ (U : LieSubalgebra ℚ L)
    {j : ℕ} (hj : 1 ≤ j) {a b : L}
    (ha : a ∈ U.toSubmodule ⊔ F.layer j) (hb : b ∈ U.toSubmodule ⊔ F.layer j) :
    ⁅a, b⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
  obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨v, hv, y, hy, rfl⟩ := Submodule.mem_sup.mp hb
  have hu1 : u ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hv1 : v ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have huv : ⁅u, v⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer (j + 1)) (U.lie_mem hu hv)
  have huy : ⁅u, y⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
    apply (le_sup_right : F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer (j + 1))
    simpa only [Nat.add_comm 1 j] using F.lie_mem hu1 hy
  have hxv : ⁅x, v⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_right : F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer (j + 1)) (F.lie_mem hx hv1)
  have hxy : ⁅x, y⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_right : F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer (j + 1))
      (F.antitone (by omega : j + 1 ≤ j + j) (F.lie_mem hx hy))
  rw [add_lie, lie_add, lie_add]
  exact Submodule.add_mem _ (Submodule.add_mem _ huv huy) (Submodule.add_mem _ hxv hxy)

theorem bch_triple_remainder_mem_subalgebra_sup_layer (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) {j : ℕ} (hj : 1 ≤ j) (a b c : L)
    (ha : a ∈ U.toSubmodule ⊔ F.layer j)
    (hb : b ∈ U.toSubmodule ⊔ F.layer j)
    (hc : c ∈ U.toSubmodule ⊔ F.layer j) :
    lieBCH s (lieBCH s a b) c - (a + b + c) ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
  lieBCH_triple_sub_sum_mem_submodule hs _ _
    (sup_le_sup_left (F.antitone (Nat.le_succ j)) _)
    (fun _ hx _ hy => F.bracket_mem_subalgebra_sup_layer_succ U hj hx hy) a b c ha hb hc

theorem outer_sum_mem_subalgebra_sup_layer (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) {j : ℕ} (hj : 1 ≤ j) (a d p p' : L)
    (ha : a ∈ U.toSubmodule ⊔ F.layer j)
    (hd : d ∈ U.toSubmodule ⊔ F.layer j)
    (hp : p ∈ U) (hp' : p' ∈ U)
    (heq : p = lieBCH s (lieBCH s a p') d) :
    a + d ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
  have hrem := F.bch_triple_remainder_mem_subalgebra_sup_layer hs U hj a p' d ha
    ((le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer j) hp') hd
  rw [← heq] at hrem
  have hpW : p ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer (j + 1)) hp
  have hp'W : p' ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer (j + 1)) hp'
  convert Submodule.sub_mem _ (Submodule.sub_mem _ hpW hp'W) hrem using 1
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem outer_factors_mem_of_separation (U : LieSubalgebra ℚ L)
    (A D P P' : F.Group) (hP : P.coord ∈ U) (hP' : P'.coord ∈ U)
    (hidentity : P = A * P' * D)
    (hseparate : ∀ j : ℕ, 1 ≤ j → j ≤ s →
      A.coord + D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      A.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧
        D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    A.coord ∈ U ∧ D.coord ∈ U := by
  have hind : ∀ n : ℕ, n ≤ s →
      A.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) ∧
        D.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.zero_add, F.one_eq_top, sup_top_eq]
      exact ⟨Submodule.mem_top, Submodule.mem_top⟩
    | succ n ih =>
      intro hn
      obtain ⟨ha, hd⟩ := ih (by omega)
      apply hseparate (n + 1) (by omega) hn
      apply F.outer_sum_mem_subalgebra_sup_layer (by omega) U (by omega)
        A.coord D.coord P.coord P'.coord ha hd hP hP'
      exact congrArg NilpotentLieBCHGroup.coord hidentity
  change A.coord ∈ U.toSubmodule ∧ D.coord ∈ U.toSubmodule
  simpa only [F.terminal, sup_bot_eq] using hind s le_rfl

theorem comparison_middle_identity (E P R E' P' R' : F.Group)
    (h : E * P * R = E' * P' * R') :
    P = (E⁻¹ * E') * P' * (R' * R⁻¹) := by
  have heq := congrArg (fun x : F.Group => E⁻¹ * x * R⁻¹) h
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using heq

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem outer_sum_mem_of_identity_mod_layer (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) {j k : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    (a d p p' : L) (ha : a ∈ U.toSubmodule ⊔ F.layer j) (hd : d ∈ U.toSubmodule ⊔ F.layer j)
    (hp : p ∈ U.toSubmodule ⊔ F.layer k) (hp' : p' ∈ U.toSubmodule ⊔ F.layer k)
    (heq : p - lieBCH s (lieBCH s a p') d ∈ F.layer k) :
    a + d ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
  have hkw : U.toSubmodule ⊔ F.layer k ≤ U.toSubmodule ⊔ F.layer (j + 1) :=
    sup_le_sup_left (F.antitone hjk) _
  have hwj : U.toSubmodule ⊔ F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer j :=
    sup_le_sup_left (F.antitone (Nat.le_succ j)) _
  have hrem := F.bch_triple_remainder_mem_subalgebra_sup_layer hs U hj a p' d ha (hwj (hkw hp')) hd
  have herr : p - lieBCH s (lieBCH s a p') d ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    Submodule.mem_sup_right (F.antitone hjk heq)
  convert Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (hkw hp) (hkw hp')) herr) hrem using 1
  abel

theorem outer_factors_mem_mod_layer_of_separation (U : LieSubalgebra ℚ L)
    (k : ℕ) (hk : k ≤ s + 1) (A D P P' : F.Group)
    (hP : P.coord ∈ U.toSubmodule ⊔ F.layer k) (hP' : P'.coord ∈ U.toSubmodule ⊔ F.layer k)
    (hidentity : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) P =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (A * P' * D))
    (hseparate : ∀ j : ℕ, 1 ≤ j → j < k →
      A.coord + D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      A.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧ D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    A.coord ∈ U.toSubmodule ⊔ F.layer k ∧ D.coord ∈ U.toSubmodule ⊔ F.layer k := by
  cases k with
  | zero =>
    have hall (x : L) : x ∈ F.layer 0 := F.antitone (Nat.zero_le 1) (by rw [F.one_eq_top]; trivial)
    exact ⟨Submodule.mem_sup_right (hall _), Submodule.mem_sup_right (hall _)⟩
  | succ k =>
    have herr : P.coord - lieBCH s (lieBCH s A.coord P'.coord) D.coord ∈ F.layer (k + 1) := by
      apply (lieQuotientMap_eq_zero (F.layerIdeal (k + 1)) _).mp
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg NilpotentLieBCHGroup.coord hidentity)
    have hind : ∀ n : ℕ, n ≤ k →
        A.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) ∧ D.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [Nat.zero_add, F.one_eq_top, sup_top_eq]
        exact ⟨Submodule.mem_top, Submodule.mem_top⟩
      | succ n ih =>
        intro hn
        obtain ⟨ha, hd⟩ := ih (by omega)
        apply hseparate (n + 1) (by omega) (by omega)
        exact F.outer_sum_mem_of_identity_mod_layer (by omega) U (by omega) (by omega)
          A.coord D.coord P.coord P'.coord ha hd hP hP' herr
    exact hind k le_rfl

theorem compatible_factors_mem_mod_layer_of_separation (U : LieSubalgebra ℚ L)
    (k : ℕ) (hk : k ≤ s + 1) (E P R E' P' R' : F.Group)
    (hP : P.coord ∈ U.toSubmodule ⊔ F.layer k) (hP' : P'.coord ∈ U.toSubmodule ⊔ F.layer k)
    (hidentity : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (E * P * R) =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (E' * P' * R'))
    (hseparate : ∀ j : ℕ, 1 ≤ j → j < k →
      (E⁻¹ * E').coord + (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      (E⁻¹ * E').coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧
        (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    (E⁻¹ * E').coord ∈ U.toSubmodule ⊔ F.layer k ∧ (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer k := by
  let q := NilpotentLieBCHGroup.quotientHom (hnil := F.lowerCentralSeries_eq_bot) (F.layerIdeal k)
  change q (E * P * R) = q (E' * P' * R') at hidentity
  have hmiddle : q P = q ((E⁻¹ * E') * P' * (R' * R⁻¹)) := by
    have h := congrArg (fun x => (q E)⁻¹ * x * (q R)⁻¹) hidentity
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  exact F.outer_factors_mem_mod_layer_of_separation U k hk (E⁻¹ * E') (R' * R⁻¹) P P' hP hP' hmiddle hseparate

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem controlled_outer_factors_mem (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (A D P P' : F.realification.Group)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP' : P'.coord ∈ realificationLieSubalgebra U)
    (hidentity : P = A * P' * D)
    (ha : ‖(e.baseChange ℝ).equivFun A.coord‖ ≤ Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hd : (e.baseChange ℝ).equivFun D.coord ∈ realDenominatorGrid l) :
    A.coord ∈ realificationLieSubalgebra U ∧ D.coord ∈ realificationLieSubalgebra U := by
  let W := realLieSubalgebraOverRat (realificationLieSubalgebra U)
  change A.coord ∈ W ∧ D.coord ∈ W
  apply F.realification.outer_factors_mem_of_separation W A D P P' hP hP' hidentity
  intro j _ _ hsum
  let M : Matrix ι (κ ⊕ ι) ℚ := fun i z => e.repr (subalgebraLayerFamily e v ω (j + 1) z) i
  have hM : ∀ i z, RationalHeightLE (M i z) H :=
    fun i z => subalgebraLayerFamily_height e v ω (j + 1) hH hv z i
  have hcols : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hsum' : (e.baseChange ℝ).equivFun A.coord + (e.baseChange ℝ).equivFun D.coord ∈
      Submodule.span ℝ (Set.range (fun z i => (M i z : ℝ))) := by
    rw [← map_add]
    exact (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan (j + 1) _).mp hsum
  obtain ⟨ha', hd'⟩ := controlled_small_vector_separation M hH hl hM (by linarith)
    (hι.trans (by linarith)) hcols
    (hHp.trans (Real.exp_le_exp.mpr (by linarith)))
    (hlp.trans (Real.exp_le_exp.mpr (by linarith))) _ _ ha hd hsum'
  exact ⟨(F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan (j + 1) _).mpr ha',
    (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan (j + 1) _).mpr hd'⟩

theorem controlled_compatible_factors_mem (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (E P R E' P' R' : F.realification.Group)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP' : P'.coord ∈ realificationLieSubalgebra U)
    (hidentity : E * P * R = E' * P' * R')
    (ha : ‖(e.baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hd : (e.baseChange ℝ).equivFun (R' * R⁻¹).coord ∈ realDenominatorGrid l) :
    (E⁻¹ * E').coord ∈ realificationLieSubalgebra U ∧
      (R' * R⁻¹).coord ∈ realificationLieSubalgebra U :=
  F.controlled_outer_factors_mem e ω hlayers U v hspan hH hl hv hp hι hκ hHp hlp
    (E⁻¹ * E') (R' * R⁻¹) P P' hP hP'
    (F.realification.comparison_middle_identity E P R E' P' R' hidentity) ha hd

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem controlled_separation_at_layer (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (j : ℕ) (x y : ℝ ⊗[ℚ] L)
    (hx : ‖(e.baseChange ℝ).equivFun x‖ ≤ Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hy : (e.baseChange ℝ).equivFun y ∈ realDenominatorGrid l)
    (hsum : x + y ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j) :
    x ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j ∧
      y ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j := by
  let M : Matrix ι (κ ⊕ ι) ℚ := fun i z => e.repr (subalgebraLayerFamily e v ω j z) i
  have hM : ∀ i z, RationalHeightLE (M i z) H :=
    fun i z => subalgebraLayerFamily_height e v ω j hH hv z i
  have hcols : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hsum' : (e.baseChange ℝ).equivFun x + (e.baseChange ℝ).equivFun y ∈
      Submodule.span ℝ (Set.range (fun z i => (M i z : ℝ))) := by
    rw [← map_add]
    exact (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan j _).mp hsum
  obtain ⟨hx', hy'⟩ := controlled_small_vector_separation M hH hl hM (by linarith)
    (hι.trans (by linarith)) hcols (hHp.trans (Real.exp_le_exp.mpr (by linarith)))
    (hlp.trans (Real.exp_le_exp.mpr (by linarith))) _ _ hx hy hsum'
  exact ⟨(F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan j _).mpr hx',
    (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan j _).mpr hy'⟩

theorem controlled_compatible_factors_mod_layer (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (k : ℕ) (hk : k ≤ s + 1)
    (E P R E' P' R' : F.realification.Group)
    (hP : P.coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k)
    (hP' : P'.coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k)
    (hidentity : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (E * P * R) =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (E' * P' * R'))
    (ha : ‖(e.baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hd : (e.baseChange ℝ).equivFun (R' * R⁻¹).coord ∈ realDenominatorGrid l) :
    (E⁻¹ * E').coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k ∧
      (R' * R⁻¹).coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k := by
  apply F.realification.compatible_factors_mem_mod_layer_of_separation
    (realLieSubalgebraOverRat (realificationLieSubalgebra U)) k hk E P R E' P' R' hP hP' hidentity
  intro j _ _ hsum
  exact F.controlled_separation_at_layer e ω hlayers U v hspan hH hl hv hp hι hκ hHp hlp (j + 1)
    (E⁻¹ * E').coord (R' * R⁻¹).coord ha hd hsum

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_symbol_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ E P R E' P' R' : F.RealPolynomialSymbolGroup w,
      P.coord ∈ realificationLieSubalgebra U → P'.coord ∈ realificationLieSubalgebra U →
      E * P * R = E' * P' * R' →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E' →
      F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R' →
      (E⁻¹ * E').coord ∈ realificationLieSubalgebra U ∧
        (R' * R⁻¹).coord ∈ realificationLieSubalgebra U := by
  obtain ⟨cs, _, hslow⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨cr, _, hrat⟩ := exists_symbol_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) +
    (Polynomial.X + Polynomial.C cs) ^ cs + (Polynomial.X + Polynomial.C cr) ^ cr + Polynomial.X + 2
  let B : Polynomial ℕ := (2 * Q + 2) ^ 48 + (2 * Q + 2) ^ 24 + 2 * Q + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
    T hT E P R E' P' R' hP hP' heq hE hE' hR hR'
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let q : ℝ := (p + (s + 2)) ^ (s + 2) + (p + cs) ^ cs + (p + cr) ^ cr + p + 2
  have hd0 : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  have hs0 : 0 ≤ (p + cs) ^ cs := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsq : (p + cs) ^ cs ≤ q := by dsimp [q]; linarith
  have hrq : (p + cr) ^ cr ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    ((Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)).trans
          (by dsimp [q]; linarith)
  have hcutoff : separationBudget (2 * q) ≤ (p + C) ^ C := by
    simpa [B, Q, q, separationBudget, Polynomial.eval₂_pow] using hbound p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hAslow : F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + cs) ^ cs)) (E⁻¹ * E') := by
    have hinputs : ∀ g ∈ [E⁻¹, E'], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hlayers w T _ E).mpr hE
      · exact hE'
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hslow F b ω hlayers w hw H p hH hp hι hσ hHp hb T hTpos [E⁻¹, E'] (by simp) hinputs
  obtain ⟨m, hm, hmp, _, hproducts⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  have hDgrid : F.SymbolRationalGrid b ω hlayers w m (R' * R⁻¹) := by
    have hinputs : ∀ g ∈ [R', R⁻¹], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hR'
      · exact F.symbolRationalGrid_inv b ω hlayers w l hR
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [R', R⁻¹] (by simp) hinputs
  have hAnorm : ‖((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * q) / Real.exp (separationBudget (2 * q)) := by
    have hnorm := F.symbolSlowBound_log_norm b ω hlayers w T
      (Real.one_le_exp (separationBudget_nonneg (by positivity : 0 ≤ 2 * q)))
      (fun i => (Real.exp_le_exp.mpr hcutoff).trans (hT i)) (Real.exp_nonneg _) (E⁻¹ * E') hAslow
    exact hnorm.trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (hsq.trans (by linarith))) (Real.exp_nonneg _))
  exact (F.polynomialSymbolFiltration w).controlled_compatible_factors_mem
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) U v hspan hH hm hv hq hdim (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hmp.trans (Real.exp_le_exp.mpr hrq))
    E P R E' P' R' hP hP' heq hAnorm hDgrid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem realSymbolGradeQuotient_mem_iff {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (k : ℕ) (g : F.RealPolynomialSymbolGroup w) :
    F.realSymbolGradeQuotientHom w k g ∈
        (NilpotentLieBCHGroup.realificationSubgroup
          (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w k) ↔
      g.coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔
        (F.polynomialSymbolFiltration w).realification.layer k :=
  NilpotentLieBCHGroup.quotient_mem_map_subgroup_iff
    ((F.polynomialSymbolFiltration w).realification.layerIdeal k)
    (realLieSubalgebraOverRat (realificationLieSubalgebra U)) g

theorem exists_controlled_symbol_comparison_mod_layer (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ k : ℕ, k ≤ s + 1 → ∀ E P R E' P' R' : F.RealPolynomialSymbolGroup w,
      F.realSymbolGradeQuotientHom w k P ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) →
      F.realSymbolGradeQuotientHom w k P' ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) →
      F.realSymbolGradeQuotientHom w k (E * P * R) = F.realSymbolGradeQuotientHom w k (E' * P' * R') →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E' →
      F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R' →
      F.realSymbolGradeQuotientHom w k (E⁻¹ * E') ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) ∧
      F.realSymbolGradeQuotientHom w k (R' * R⁻¹) ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) := by
  obtain ⟨cs, _, hslow⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨cr, _, hrat⟩ := exists_symbol_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) +
    (Polynomial.X + Polynomial.C cs) ^ cs + (Polynomial.X + Polynomial.C cr) ^ cr + Polynomial.X + 2
  let B : Polynomial ℕ := (2 * Q + 2) ^ 48 + (2 * Q + 2) ^ 24 + 2 * Q + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
    T hT k hk E P R E' P' R' hP hP' heq hE hE' hR hR'
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let q : ℝ := (p + (s + 2)) ^ (s + 2) + (p + cs) ^ cs + (p + cr) ^ cr + p + 2
  have hd0 : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  have hs0 : 0 ≤ (p + cs) ^ cs := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsq : (p + cs) ^ cs ≤ q := by dsimp [q]; linarith
  have hrq : (p + cr) ^ cr ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    ((Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)).trans
          (by dsimp [q]; linarith)
  have hcutoff : separationBudget (2 * q) ≤ (p + C) ^ C := by
    simpa [B, Q, q, separationBudget, Polynomial.eval₂_pow] using hbound p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hAslow : F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + cs) ^ cs)) (E⁻¹ * E') := by
    have hinputs : ∀ g ∈ [E⁻¹, E'], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hlayers w T _ E).mpr hE
      · exact hE'
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hslow F b ω hlayers w hw H p hH hp hι hσ hHp hb T hTpos [E⁻¹, E'] (by simp) hinputs
  obtain ⟨m, hm, hmp, _, hproducts⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  have hDgrid : F.SymbolRationalGrid b ω hlayers w m (R' * R⁻¹) := by
    have hinputs : ∀ g ∈ [R', R⁻¹], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hR'
      · exact F.symbolRationalGrid_inv b ω hlayers w l hR
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [R', R⁻¹] (by simp) hinputs
  have hAnorm : ‖((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * q) / Real.exp (separationBudget (2 * q)) := by
    have hnorm := F.symbolSlowBound_log_norm b ω hlayers w T
      (Real.one_le_exp (separationBudget_nonneg (by positivity : 0 ≤ 2 * q)))
      (fun i => (Real.exp_le_exp.mpr hcutoff).trans (hT i)) (Real.exp_nonneg _) (E⁻¹ * E') hAslow
    exact hnorm.trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (hsq.trans (by linarith))) (Real.exp_nonneg _))
  have hresult := (F.polynomialSymbolFiltration w).controlled_compatible_factors_mod_layer
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) U v hspan hH hm hv hq hdim (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hmp.trans (Real.exp_le_exp.mpr hrq)) k hk
    E P R E' P' R' ((F.realSymbolGradeQuotient_mem_iff w U k P).mp hP)
      ((F.realSymbolGradeQuotient_mem_iff w U k P').mp hP') heq hAnorm hDgrid
  exact ⟨(F.realSymbolGradeQuotient_mem_iff w U k _).mpr hresult.1,
    (F.realSymbolGradeQuotient_mem_iff w U k _).mpr hresult.2⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_bounded_symbol_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF w).repr (v i) z) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
        ∀ E₀ P₀ R₀ E P R : F.RealPolynomialSymbolGroup w,
          P₀.coord ∈ realificationLieSubalgebra U → P.coord ∈ realificationLieSubalgebra U →
          E₀ * P₀ * R₀ = E * P * R →
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E₀ →
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
          F.SymbolRationalGrid b ω hF w l R₀ → F.SymbolRationalGrid b ω hF w l R →
          (E₀⁻¹ * E).coord ∈ realificationLieSubalgebra U ∧
          (R * R₀⁻¹).coord ∈ realificationLieSubalgebra U ∧
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + C) ^ C)) (E₀⁻¹ * E) ∧
          F.SymbolRationalGrid b ω hF w m (R * R₀⁻¹) := by
  have hcompExists := exists_controlled_symbol_comparison s a
  obtain ⟨cc, _, hcomp⟩ := hcompExists
  have hslowExists := exists_symbol_slow_product_bound s a 2
  obtain ⟨cs, _, hslow⟩ := hslowExists
  have hratExists := exists_symbol_rational_product_bound s 2
  obtain ⟨cr, _, hrat⟩ := hratExists
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C cc) ^ cc +
    (Polynomial.X + Polynomial.C cs) ^ cs + (Polynomial.X + Polynomial.C cr) ^ cr
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
  have hsum : (p + cc) ^ cc + (p + cs) ^ cs + (p + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbound p hp
  have hc0 : 0 ≤ (p + cc) ^ cc := by positivity
  have hs0 : 0 ≤ (p + cs) ^ cs := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hcb : (p + cc) ^ cc ≤ (p + C) ^ C := by linarith
  have hsb : (p + cs) ^ cs ≤ (p + C) ^ C := by linarith
  have hrb : (p + cr) ^ cr ≤ (p + C) ^ C := by linarith
  have hproductsExists := hrat F b ω hF w hw H p hH hp hι hσ hHp hb l hl hlp
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hproductsExists
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrb), hlm, ?_⟩
  intro T hT E₀ P₀ R₀ E P R hP₀ hP heq hE₀ hE hR₀ hR
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hmem := hcomp F b ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
    T (fun i => (Real.exp_le_exp.mpr hcb).trans (hT i)) E₀ P₀ R₀ E P R
    hP₀ hP heq hE₀ hE hR₀ hR
  refine ⟨hmem.1, hmem.2, ?_, ?_⟩
  · have hinputs : ∀ x ∈ [E₀⁻¹, E], F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hF w T _ E₀).mpr hE₀
      · exact hE
    have hpair : F.SymbolSlowBound b ω hF w T (Real.exp ((p + cs) ^ cs)) (E₀⁻¹ * E) := by
      simpa only [List.prod_cons, List.prod_nil, mul_one] using
        hslow F b ω hF w hw H p hH hp hι hσ hHp hb T hTpos [E₀⁻¹, E] (by simp) hinputs
    exact F.symbolSlowBound_mono b ω hF w T hTpos (Real.exp_le_exp.mpr hsb) _ hpair
  · have hinputs : ∀ x ∈ [R, R₀⁻¹], F.SymbolRationalGrid b ω hF w l x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hR
      · exact F.symbolRationalGrid_inv b ω hF w l hR₀
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hproducts [R, R₀⁻¹] (by simp) hinputs

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem symbol_current_grade_residual_mem
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ (F.PolynomialSymbol w))
    (hU : BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
      (fun z => ω z.val.2) U.toSubmodule)
    (k : ℕ) (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hE : F.realSymbolGradeQuotientHom w k E₀ = F.realSymbolGradeQuotientHom w k E)
    (hR : F.realSymbolGradeQuotientHom w k R = F.realSymbolGradeQuotientHom w k R₀) :
    let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
      (fun z => ω z.val.2) k
    π (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord - π (E₀⁻¹ * E).coord - π (R * R₀⁻¹).coord ∈
      realificationLieSubalgebra U := by
  exact (F.polynomialSymbolFiltration w).realGradeProjection_normalized_residual_mem
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w)
    (realificationLieSubalgebra U).toSubmodule
    (hU.baseChange (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule)
    k E P R E₀ R₀ hP hE hR

theorem exists_controlled_symbol_grade_step (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ {η : Type*} (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)),
        (∀ i, BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
          (fun z => ω z.val.2) (U i).toSubmodule) →
        ∀ (k : ℕ) (X E R A D : F.RealPolynomialSymbolGroup w),
        (∀ i, F.realSymbolGradeQuotientHom w k (E⁻¹ * X * R⁻¹) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U i)).map
            (F.realSymbolGradeQuotientHom w k)) →
        A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k →
        D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k →
        (let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) k
         ∀ i, π (E⁻¹ * X * R⁻¹).coord - π A.coord - π D.coord ∈ realificationLieSubalgebra (U i)) →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) A →
        F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l D →
        (E * A) * (A⁻¹ * (E⁻¹ * X * R⁻¹) * D⁻¹) * (D * R) = X ∧
          F.realSymbolGradeQuotientHom w k (E * A) = F.realSymbolGradeQuotientHom w k E ∧
          F.realSymbolGradeQuotientHom w k (D * R) = F.realSymbolGradeQuotientHom w k R ∧
          (∀ i, F.realSymbolGradeQuotientHom w (k + 1) (A⁻¹ * (E⁻¹ * X * R⁻¹) * D⁻¹) ∈
            (NilpotentLieBCHGroup.realificationSubgroup
              (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U i)).map
              (F.realSymbolGradeQuotientHom w (k + 1))) ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A) ∧
          F.SymbolRationalGrid b ω hlayers w m (D * R) := by
  obtain ⟨cs, hcs, hslow⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨cr, hcr, hrat⟩ := exists_symbol_rational_product_bound s 2
  refine ⟨max cs cr, hcs.trans (le_max_left _ _), ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  have hs : (p + cs) ^ cs ≤ (p + (max cs cr : ℕ)) ^ max cs cr :=
    shifted_power_self_mono hp (by omega) (le_max_left _ _)
  have hr : (p + cr) ^ cr ≤ (p + (max cs cr : ℕ)) ^ max cs cr :=
    shifted_power_self_mono hp (by omega) (le_max_right _ _)
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hr), hlm, ?_⟩
  intro η U hU k X E R A D hY hA hD hgrade hEslow hAslow hRgrid hDgrid
  let G := F.polynomialSymbolFiltration w
  let B := F.polynomialSymbolBasis b ω hlayers w
  have hUr : ∀ i, BasisGradedSubmodule (B.baseChange ℝ) (fun z => ω z.val.2)
      (realificationLieSubalgebra (U i)).toSubmodule :=
    fun i => (hU i).baseChange B (fun z => ω z.val.2) (U i).toSubmodule
  have hYr : ∀ i, (E⁻¹ * X * R⁻¹).coord ∈
      (realificationLieSubalgebra (U i)).toSubmodule ⊔ (G.realLayer k).toSubmodule :=
    fun i => (G.real_quotient_mem_subgroup_iff (realificationLieSubalgebra (U i)) k _).mp (hY i)
  obtain ⟨hprod, hEq, hRq, hnext⟩ := G.simultaneous_real_grade_correction B (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) (fun i => realificationLieSubalgebra (U i))
    hUr k X E R A D hYr hA hD hgrade
  refine ⟨hprod, hEq, hRq, ?_, ?_, ?_⟩
  · intro i
    exact (G.real_quotient_mem_subgroup_iff (realificationLieSubalgebra (U i)) (k + 1) _).mpr (hnext i)
  · have hi : ∀ g ∈ [E, A], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hEslow
      · exact hAslow
    have h := hslow F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT [E, A] (by simp) hi
    simp only [List.prod_cons, List.prod_nil, mul_one] at h
    exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr hs) _ h
  · have hi : ∀ g ∈ [D, R], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hDgrid
      · exact hRgrid
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [D, R] (by simp) hi

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_common_symbol_grade_corrections (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : η → κ → F.PolynomialSymbol w),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w)
        (fun z => z.val.1) (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ j i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v j i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (k : ℕ) (x : F.RealPolynomialSymbol w) (E R : η → F.RealPolynomialSymbolGroup w),
        let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) k
        (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
        (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
        (∀ j, π x - π (E j).coord - π (R j).coord ∈ realificationLieSubalgebra (U j)) →
        ∃ A D : F.RealPolynomialSymbolGroup w,
          A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
          D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) A ∧
          F.SymbolRationalGrid b ω hlayers w m D ∧
          ∀ j, π x - π A.coord - π D.coord ∈ realificationLieSubalgebra (U j) := by
  obtain ⟨C, hC, hbound⟩ := exists_common_correction_budget s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hv T hT
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let N : ℝ := (p + (s + 2)) ^ (s + 2)
  let q : ℝ := N * (p + 1) + (p + 2) ^ a + p + 2
  let t : ℝ := ((q + 2) ^ 10 + 2) ^ 4
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have ha : 0 ≤ (p + 2) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hNp : 0 ≤ N * (p + 1) := mul_nonneg hN (by positivity)
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hNterm : N ≤ N * (p + 1) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (show 1 ≤ p + 1 by linarith) hN
  have hNq : N ≤ q := hNterm.trans (by dsimp [q]; linarith)
  have hNpq : N * p ≤ q :=
    (mul_le_mul_of_nonneg_left (show p ≤ p + 1 by linarith) hN).trans (by dsimp [q]; linarith)
  have haq : (p + 2) ^ a ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ N :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hcols : ((Fintype.card (SymbolBasisIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_mul]
    exact (mul_le_mul hdim hκ (Nat.cast_nonneg _) hN).trans hNpq
  have hrows : (Fintype.card (Σ _ : η, SymbolBasisIndex w ω) : ℝ) ≤ q := by
    simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
    exact (mul_le_mul hη hdim (Nat.cast_nonneg _) hp).trans (by simpa only [mul_comm] using hNpq)
  have hall : separationBudget t + (t + 2) ^ 36 + ((t + 2) ^ 18 + t) ≤ (p + C) ^ C := by
    exact hbound p hp
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : 0 ≤ separationBudget t := separationBudget_nonneg ht
  have hden0 : 0 ≤ (t + 2) ^ 36 := by positivity
  have hslow0 : 0 ≤ (t + 2) ^ 18 + t := by positivity
  have hcut : separationBudget t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right hden0).trans ((le_add_of_nonneg_right hslow0).trans hall)
  have hden : (t + 2) ^ 36 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hs).trans ((le_add_of_nonneg_right hslow0).trans hall)
  have hslow : (t + 2) ^ 18 + t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (add_nonneg hs hden0)).trans hall
  let e := F.polynomialSymbolBasis b ω hlayers w
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_block_subspace_corrections e (fun z => z.val.1)
    (fun j => (U j).toSubmodule) v hspan hblock hH hl hv hq (hdim.trans hNq) hcols hrows
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hden), hlm, ?_⟩
  intro k x E R
  dsimp only
  intro hE hR hres
  let π := basisGradeProjection (e.baseChange ℝ) (fun z => ω z.val.2) k
  have hπ (z : F.RealPolynomialSymbol w) : π (π z) = π z :=
    basisCoordinateProjection_idempotent (e.baseChange ℝ) {z | ω z.val.2 = k} z
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hW : ∀ α, 0 < monomialScale T α := monomialScale_pos T hTpos
  have hWmin : ∀ z : SymbolBasisIndex w ω, Real.exp (separationBudget t) ≤ monomialScale T z.val.1 :=
    fun z => le_monomialScale_of_ne_zero T (Real.one_le_exp hs)
      (fun i => (Real.exp_le_exp.mpr hcut).trans (hT i))
      (F.symbolBasisIndex_monomial_ne_zero b ω hlayers w z)
  have he : ∀ j z, |(e.baseChange ℝ).equivFun (π (E j).coord) z| ≤ Real.exp q / monomialScale T z.val.1 := by
    intro j z
    exact ((basisCoordinateProjection_abs_repr_le (e.baseChange ℝ) {z | ω z.val.2 = k} (E j).coord z).trans
      (hE j z)).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr haq) (hW _).le)
  have hr : ∀ j, (e.baseChange ℝ).equivFun (π (R j).coord) ∈ realDenominatorGrid l :=
    fun j => basisCoordinateProjection_real_grid (e.baseChange ℝ) {z | ω z.val.2 = k} l (R j).coord (hR j)
  obtain ⟨u, d, hu, hd, hcommon⟩ := hsolve (monomialScale T) hW hWmin
    (fun j => π (E j).coord) (fun j => π (R j).coord) (π x) he hr hres
  refine ⟨⟨π u⟩, ⟨π d⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer e (fun z => ω z.val.2)
      (F.polynomialSymbolFiltration_layer b ω hlayers w) k u
  · exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer e (fun z => ω z.val.2)
      (F.polynomialSymbolFiltration_layer b ω hlayers w) k d
  · intro z
    exact ((basisCoordinateProjection_abs_repr_le (e.baseChange ℝ) {z | ω z.val.2 = k} u z).trans
      (hu z)).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hslow) (hW _).le)
  · exact basisCoordinateProjection_real_grid (e.baseChange ℝ) {z | ω z.val.2 = k} m d hd
  · intro j
    have hgraded : BasisGradedSubmodule e (fun z => ω z.val.2) (U j).toSubmodule := by
      have heq : (fun z : SymbolBasisIndex w ω => ω z.val.2) = (fun z => Finsupp.weight w z.val.1) :=
        funext (fun z => z.property.symm)
      rw [heq]
      exact (hblock j).graded e (fun z => z.val.1) (U j).toSubmodule (Finsupp.weight w)
    have h := hgraded.baseChange e (fun z => ω z.val.2) (U j).toSubmodule k
      (π x - u - d) (hcommon j)
    change π (π x - u - d) ∈ (U j).toSubmodule.baseChange ℝ at h
    change π x - π (π u) - π (π d) ∈ (U j).toSubmodule.baseChange ℝ
    simpa only [map_sub, hπ] using h

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedSquareCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realifiedSquareEquiv :
    (ℝ ⊗[ℚ] F.squareLieSubalgebra) ≃ₗ[ℚ] F.realification.squareLieSubalgebra :=
  let e := ((F.squareCoordinates.baseChange ℚ ℝ _ _).trans
    (TensorProduct.prodRight ℚ ℝ ℝ L (F.layer 2))).trans
      ((LinearEquiv.refl ℝ (ℝ ⊗[ℚ] L)).prodCongr (realificationSubmoduleEquiv (F.layer 2)))
  (e.restrictScalars ℚ).trans F.realification.squareCoordinates.symm

theorem realifiedSquareEquiv_tmul (r : ℝ) (x : F.squareLieSubalgebra) :
    (F.realifiedSquareEquiv (r ⊗ₜ[ℚ] x)).val =
      (r ⊗ₜ[ℚ] x.val.1, r ⊗ₜ[ℚ] x.val.2) := by
  apply Prod.ext
  · change r ⊗ₜ[ℚ] x.val.2 + r ⊗ₜ[ℚ] (x.val.1 - x.val.2) = r ⊗ₜ[ℚ] x.val.1
    rw [← TensorProduct.tmul_add]
    congr 1
    abel
  · rfl

theorem realifiedSquareEquiv_fst (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    F.realification.squareFst (F.realifiedSquareEquiv x) = realificationLieHom F.squareFst x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => exact congrArg Prod.fst (F.realifiedSquareEquiv_tmul r x)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realifiedSquareEquiv_snd (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    F.realification.squareSnd (F.realifiedSquareEquiv x) = realificationLieHom F.squareSnd x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => exact congrArg Prod.snd (F.realifiedSquareEquiv_tmul r x)
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realifiedSquareLieEquiv :
    (ℝ ⊗[ℚ] F.squareLieSubalgebra) ≃ₗ⁅ℚ⁆ F.realification.squareLieSubalgebra where
  toFun := F.realifiedSquareEquiv
  invFun := F.realifiedSquareEquiv.symm
  left_inv := F.realifiedSquareEquiv.left_inv
  right_inv := F.realifiedSquareEquiv.right_inv
  map_add' := F.realifiedSquareEquiv.map_add
  map_smul' := F.realifiedSquareEquiv.map_smul
  map_lie' := by
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · change F.realification.squareFst (F.realifiedSquareEquiv ⁅x, y⁆) =
        F.realification.squareFst ⁅F.realifiedSquareEquiv x, F.realifiedSquareEquiv y⁆
      simp only [realifiedSquareEquiv_fst, LieHom.map_lie]
    · change F.realification.squareSnd (F.realifiedSquareEquiv ⁅x, y⁆) =
        F.realification.squareSnd ⁅F.realifiedSquareEquiv x, F.realifiedSquareEquiv y⁆
      simp only [realifiedSquareEquiv_snd, LieHom.map_lie]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealAdaptedCoefficientGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

def RealAdaptedCoefficientGrid (l : ℕ) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) : Prop :=
  (fun z : AdaptedBasisIndex w ω => ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x z)
    ∈ realDenominatorGrid l

theorem realAdaptedCoefficientGrid_polynomial_iff (l : ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.RealAdaptedCoefficientGrid b ω hF w l g.coord ↔
      F.PolynomialRationalGrid b w l (F.realAdaptedPolynomialGroupHom w g) :=
  (F.polynomialRationalGrid_groupHom_iff b w ω hF l g).symm

theorem realAdaptedCoefficientGrid_mono {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hx : F.RealAdaptedCoefficientGrid b ω hF w l x) :
    F.RealAdaptedCoefficientGrid b ω hF w m x :=
  realDenominatorGrid_subset_of_dvd hl hlm hx

theorem realAdaptedDirectionalDerivative_grid [Fintype σ] (l : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x) (h : σ → ℤ) :
    F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l
      (F.realAdaptedDirectionalDerivative (fun i => (h i : ℚ)) x) := by
  classical
  have hfull := (F.realAdaptedCoefficientGrid_polynomial_iff b ω hF (fun _ => 1) l
    (⟨x⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp hx
  obtain ⟨a, ha⟩ := hfull
  have hcoord (z : AdaptedBasisIndex (fun _ : σ => 1) ω) : ∃ n : ℤ, (n : ℝ) = (l : ℝ) *
      ((F.adaptedMonomialBasis b ω hF (fun _ => 1)).baseChange ℝ).repr
        (F.realAdaptedDirectionalDerivative (fun i => (h i : ℚ)) x) z := by
    rw [← F.realAdaptedPolynomialTensor_coordinates (fun _ => 1) b ω hF,
      F.realAdaptedDirectionalDerivative_polynomial]
    let f := ((b.baseChange ℝ).coord z.val.2).restrictScalars ℚ
    exact directionalDerivative_integral_coordinate f
      (F.realAdaptedPolynomialMap (fun _ => 1) x) l
      (fun β => ⟨a (β, z.val.2), congrFun ha (β, z.val.2)⟩) h z.val.1
  choose a ha using hcoord
  exact ⟨a, funext ha⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

def CoefficientBound (b : Basis ι ℝ L) (T : σ → ℝ) (M : ℝ)
    (P : VectorPolynomial σ ℚ L) : Prop :=
  ∀ α i, |b.repr (coefficients P α) i| ≤ M / monomialScale T α

def CoefficientGrid (b : Basis ι ℝ L) (l : ℕ) (P : VectorPolynomial σ ℚ L) : Prop :=
  ∀ α, (fun i => b.repr (coefficients P α) i) ∈ realDenominatorGrid l

theorem coefficientBound_iff_norm [Fintype ι] (b : Basis ι ℝ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ L) :
    CoefficientBound b T M P ↔ ∀ α, ‖b.equivFun (coefficients P α)‖ ≤ M / monomialScale T α := by
  constructor
  · intro h α
    exact (pi_norm_le_iff_of_nonneg (div_nonneg hM (monomialScale_pos T hT α).le)).mpr (h α)
  · intro h α i
    exact (norm_le_pi_norm (b.equivFun (coefficients P α)) i).trans (h α)

theorem CoefficientBound.mono (b : Basis ι ℝ L) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} {P : VectorPolynomial σ ℚ L} (h : CoefficientBound b T M P) (hMN : M ≤ N) :
    CoefficientBound b T N P := by
  intro α i
  exact (h α i).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT α).le)

theorem CoefficientBound.neg (b : Basis ι ℝ L) (T : σ → ℝ) {M : ℝ}
    {P : VectorPolynomial σ ℚ L} (h : CoefficientBound b T M P) : CoefficientBound b T M (-P) := by
  intro α i
  simpa only [map_neg, Finsupp.neg_apply, abs_neg] using h α i

theorem CoefficientBound.sub (b : Basis ι ℝ L) (T : σ → ℝ) {M N : ℝ}
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientBound b T M P) (hQ : CoefficientBound b T N Q) :
    CoefficientBound b T (M + N) (P - Q) := by
  intro α i
  simp only [map_sub, Finsupp.sub_apply]
  exact (abs_sub _ _).trans ((add_le_add (hP α i) (hQ α i)).trans_eq (by ring))

theorem CoefficientGrid.sub (b : Basis ι ℝ L) (l : ℕ)
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientGrid b l P) (hQ : CoefficientGrid b l Q) :
    CoefficientGrid b l (P - Q) := by
  intro α
  simp only [map_sub, Finsupp.sub_apply]
  exact realDenominatorGrid_sub l _ _ (hP α) (hQ α)

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF in
theorem gradedPolynomial_mem_adapted (w : σ → ℕ) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω w) :
    P ∈ F.realification.adaptedLieSubalgebra w := by
  intro α
  have h := F.realGradeProjection_mem_layer b ω hF (Finsupp.weight w α) (coefficients P α)
  have he : basisGradeProjection (b.baseChange ℝ) ω (Finsupp.weight w α) (coefficients P α) = coefficients P α := hP α
  rw [he] at h
  exact h

include hF in
theorem shiftedGradedPolynomial_mem_adapted (w : σ → ℕ) (r : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω w r) :
    P ∈ F.realification.adaptedLieSubalgebra w := by
  intro α
  have h := F.realGradeProjection_mem_layer b ω hF (Finsupp.weight w α + r) (coefficients P α)
  have he : basisGradeProjection (b.baseChange ℝ) ω (Finsupp.weight w α + r) (coefficients P α) = coefficients P α := hP α
  rw [he] at h
  exact F.realification.antitone (Nat.le_add_right _ _) h

include b ω hF in
theorem exists_real_adapted_representation (w : σ → ℕ) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ F.realification.adaptedLieSubalgebra w) :
    ∃ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w, F.realAdaptedPolynomialMap w x = P := by
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF ⟨P, hP⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem realAdaptedCoefficientBound_iff_formal (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientBound b ω hF w T M x ↔
      CoefficientBound (b.baseChange ℝ) T M (F.realAdaptedPolynomialMap w x) :=
  F.realAdaptedCoefficientBound_polynomial_iff b ω hF w T hT hM ⟨x⟩

theorem realAdaptedCoefficientGrid_iff_formal (w : σ → ℕ) (l : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientGrid b ω hF w l x ↔
      CoefficientGrid (b.baseChange ℝ) l (F.realAdaptedPolynomialMap w x) := by
  rw [F.realAdaptedCoefficientGrid_polynomial_iff b ω hF w l ⟨x⟩]
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext (fun i => congrFun ha (α, i))⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

noncomputable def adaptedFullPolynomialHom (F : NilpotentLieFiltration L s) (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* PolynomialGroup σ F.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.adaptedLieSubalgebra w).incl

@[simp] theorem adaptedFullPolynomialHom_coord (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.adaptedFullPolynomialHom w g).coord = (g.coord : VectorPolynomial σ ℚ L) := rfl

theorem exists_adapted_polynomial_list_lift (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (rs : List (PolynomialGroup σ F.lowerCentralSeries_eq_bot))
    (hadapted : ∀ r ∈ rs, r.coord ∈ F.adaptedLieSubalgebra w) :
    ∃ xs : List (F.adaptedPolynomialFiltration w).Group,
      xs.map (F.adaptedFullPolynomialHom w) = rs := by
  induction rs with
  | nil => exact ⟨[], rfl⟩
  | cons r rs ih =>
    obtain ⟨xs, hxs⟩ := ih (fun x hx => hadapted x (List.mem_cons_of_mem r hx))
    let x : (F.adaptedPolynomialFiltration w).Group := ⟨⟨r.coord, hadapted r (List.mem_cons_self)⟩⟩
    have hx : F.adaptedFullPolynomialHom w x = r := NilpotentLieBCHGroup.ext rfl
    exact ⟨x :: xs, by rw [List.map_cons, hx, hxs]⟩

theorem polynomialRationalGrid_iff_formal {ι : Type*} (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (w : σ → ℕ) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialRationalGrid b w l g ↔
      CoefficientGrid (b.baseChange ℝ) l (F.realification.adaptedFullPolynomialHom w g).coord := by
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext (fun i => congrFun ha (α, i))⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

theorem polynomialSlowBound_iff_formal {ι : Type*} (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialSlowBound b w T M g ↔
      CoefficientBound (b.baseChange ℝ) T M (F.realification.adaptedFullPolynomialHom w g).coord :=
  Iff.rfl

theorem exists_formal_polynomial_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot), rs.length ≤ k →
      (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
      (∀ r ∈ rs, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) r.coord) →
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) rs.prod.coord := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_slow_product_bound s a k
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure T hT rs hlen hadapted hbound
  obtain ⟨xs, hxs⟩ := F.realification.exists_adapted_polynomial_list_lift (fun _ => 1) rs hadapted
  have hxlen : xs.length ≤ k := by simpa only [← hxs, List.length_map] using hlen
  have hxbound : ∀ x ∈ xs, F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) x := by
    intro x hx
    have hmem : F.realification.adaptedFullPolynomialHom (fun _ => 1) x ∈ rs := by
      rw [← hxs]
      exact List.mem_map_of_mem hx
    exact (F.polynomialSlowBound_iff_formal b _ T _ x).mpr (hbound _ hmem)
  have hout := (F.polynomialSlowBound_iff_formal b _ T _ xs.prod).mp (
    hprod F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) H p hH hp hι hσ hHp hstructure
      T hT xs hxlen hxbound)
  rwa [map_list_prod, hxs] at hout

theorem exists_formal_polynomial_product_grid (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot), rs.length ≤ k →
        (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ r ∈ rs, CoefficientGrid (b.baseChange ℝ) l r.coord) →
        CoefficientGrid (b.baseChange ℝ) m rs.prod.coord := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_rational_product_bound s k
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    hprod F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro rs hlen hadapted hbound
  obtain ⟨xs, hxs⟩ := F.realification.exists_adapted_polynomial_list_lift (fun _ => 1) rs hadapted
  have hxlen : xs.length ≤ k := by simpa only [← hxs, List.length_map] using hlen
  have hxgrid : ∀ x ∈ xs, F.PolynomialRationalGrid b (fun _ => 1) l x := by
    intro x hx
    have hmem : F.realification.adaptedFullPolynomialHom (fun _ => 1) x ∈ rs := by
      rw [← hxs]
      exact List.mem_map_of_mem hx
    exact (F.polynomialRationalGrid_iff_formal b _ l x).mpr (hbound _ hmem)
  have hout := (F.polynomialRationalGrid_iff_formal b _ m xs.prod).mp (hgrid xs hxlen hxgrid)
  rwa [map_list_prod, hxs] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

section Modules

variable {σ ι κ L M : Type*} [AddCommGroup L] [Module ℚ L]
  [AddCommGroup M] [Module ℚ M]

noncomputable def sectionCorrectedPolynomial (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  p - VectorPolynomial.map ((S.baseChange ℝ).restrictScalars ℚ)
    (VectorPolynomial.map ((φ.baseChange ℝ).restrictScalars ℚ) p - q)

@[simp] theorem sectionCorrectedPolynomial_coefficients (φ : L →ₗ[ℚ] M)
    (S : M →ₗ[ℚ] L) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) (α : σ →₀ ℕ) :
    coefficients (sectionCorrectedPolynomial φ S p q) α =
      coefficients p α - S.baseChange ℝ
        (φ.baseChange ℝ (coefficients p α) - coefficients q α) := by
  simp only [sectionCorrectedPolynomial, map_sub, Finsupp.sub_apply, coefficients_map,
    LinearMap.restrictScalars_apply]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sectionCorrectedPolynomial_coefficient_norm
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K : ℕ} (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) (T : σ → ℝ) (A B : ℝ)
    (α : σ →₀ ℕ)
    (hp : ‖(b.baseChange ℝ).equivFun (coefficients p α)‖ ≤ A / monomialScale T α)
    (hq : ‖(c.baseChange ℝ).equivFun (coefficients q α)‖ ≤ B / monomialScale T α) :
    ‖(b.baseChange ℝ).equivFun (coefficients (sectionCorrectedPolynomial φ S p q) α)‖ ≤
      (A + (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
        ((((Fintype.card ι : ℝ) + 1) * (H + 1)) * A + B)) / monomialScale T α := by
  rw [sectionCorrectedPolynomial_coefficients]
  apply (realified_section_correction_coordinate_norm b c φ S hφ hS
    (coefficients p α) (coefficients q α)).trans
  calc
    _ ≤ A / monomialScale T α + (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
        (((Fintype.card ι : ℝ) + 1) * (H + 1) * (A / monomialScale T α) +
          B / monomialScale T α) := by
      exact add_le_add hp (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hp (by positivity)) hq) (by positivity))
    _ = _ := by ring

theorem sectionCorrectedPolynomial_denominator_bounds
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K l : ℕ} (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K) (hl : 0 < l) :
    0 < matrixDenominator (LinearMap.toMatrix c b S) *
      matrixDenominator (LinearMap.toMatrix b c φ) * l ∧
    l ∣ matrixDenominator (LinearMap.toMatrix c b S) *
      matrixDenominator (LinearMap.toMatrix b c φ) * l ∧
    matrixDenominator (LinearMap.toMatrix c b S) *
      matrixDenominator (LinearMap.toMatrix b c φ) * l ≤
      K ^ (Fintype.card ι * Fintype.card κ) *
        H ^ (Fintype.card κ * Fintype.card ι) * l := by
  exact ⟨Nat.mul_pos (Nat.mul_pos (matrixDenominator_pos _) (matrixDenominator_pos _)) hl,
    dvd_mul_left _ _,
    Nat.mul_le_mul_right l (Nat.mul_le_mul (matrixDenominator_le _ hS)
      (matrixDenominator_le _ hφ))⟩

theorem sectionCorrectedPolynomial_coefficient_grid
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) {l : ℕ} (hl : 0 < l) (α : σ →₀ ℕ)
    (hp : (b.baseChange ℝ).equivFun (coefficients p α) ∈ realDenominatorGrid l)
    (hq : (c.baseChange ℝ).equivFun (coefficients q α) ∈ realDenominatorGrid l) :
    (b.baseChange ℝ).equivFun (coefficients (sectionCorrectedPolynomial φ S p q) α) ∈
      realDenominatorGrid (matrixDenominator (LinearMap.toMatrix c b S) *
        matrixDenominator (LinearMap.toMatrix b c φ) * l) := by
  let D := matrixDenominator (LinearMap.toMatrix b c φ)
  let E := matrixDenominator (LinearMap.toMatrix c b S)
  have hinner : (c.baseChange ℝ).equivFun
      (φ.baseChange ℝ (coefficients p α) - coefficients q α) ∈
      realDenominatorGrid (D * l) := by
    rw [map_sub]
    exact realDenominatorGrid_sub (D * l) _ _
      (realified_linear_coordinate_grid b c φ l _ hp)
      (realDenominatorGrid_subset_of_dvd hl (dvd_mul_left l D) hq)
  have hcorr : (b.baseChange ℝ).equivFun
      (S.baseChange ℝ (φ.baseChange ℝ (coefficients p α) - coefficients q α)) ∈
      realDenominatorGrid (E * D * l) := by
    simpa only [mul_assoc] using realified_linear_coordinate_grid c b S (D * l) _ hinner
  rw [sectionCorrectedPolynomial_coefficients, map_sub]
  exact realDenominatorGrid_sub (E * D * l) _ _
    (realDenominatorGrid_subset_of_dvd hl (dvd_mul_left l (E * D)) hp) hcorr

end Modules

section LieModules

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sectionCorrectedPolynomial_coefficientBound
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K : ℕ} (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : CoefficientBound (b.baseChange ℝ) T A p)
    (hq : CoefficientBound (c.baseChange ℝ) T B q) :
    CoefficientBound (b.baseChange ℝ) T
      (A + (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
        ((((Fintype.card ι : ℝ) + 1) * (H + 1)) * A + B))
      (sectionCorrectedPolynomial φ S p q) := by
  apply (coefficientBound_iff_norm _ T hT (by positivity) _).mpr
  intro α
  exact sectionCorrectedPolynomial_coefficient_norm b c φ S hφ hS p q T A B α
    ((coefficientBound_iff_norm _ T hT hA p).mp hp α)
    ((coefficientBound_iff_norm _ T hT hB q).mp hq α)

theorem sectionCorrectedPolynomial_coefficientGrid
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) {l : ℕ} (hl : 0 < l)
    (hp : CoefficientGrid (b.baseChange ℝ) l p)
    (hq : CoefficientGrid (c.baseChange ℝ) l q) :
    CoefficientGrid (b.baseChange ℝ)
      (matrixDenominator (LinearMap.toMatrix c b S) *
        matrixDenominator (LinearMap.toMatrix b c φ) * l)
      (sectionCorrectedPolynomial φ S p q) := by
  intro α
  exact sectionCorrectedPolynomial_coefficient_grid b c φ S p q hl α (hp α) (hq α)

end LieModules

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {s : ℕ}

noncomputable def positiveUnivariate (v : Fin s → V) : VectorPolynomial Unit ℚ V :=
  ∑ d, monomial (Finsupp.single () (d.val + 1)) (v d)

theorem positiveUnivariate_coefficient (v : Fin s → V) (d : Fin s) :
    coefficients (positiveUnivariate v) (Finsupp.single () (d.val + 1)) = v d := by
  classical
  simp only [positiveUnivariate, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  rw [Finset.sum_eq_single d]
  · simp only [Finsupp.single_eq_same]
  · intro j _ hj
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hj
    apply Fin.ext
    have h := congrArg (fun α : Unit →₀ ℕ => α ()) heq
    simp only [Finsupp.single_eq_same] at h
    omega
  · simp

theorem positiveUnivariate_coefficient_eq_zero (v : Fin s → V) (α : Unit →₀ ℕ)
    (hα : ∀ d : Fin s, Finsupp.single () (d.val + 1) ≠ α) :
    coefficients (positiveUnivariate v) α = 0 := by
  classical
  simp only [positiveUnivariate, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  exact Finset.sum_eq_zero (fun d _ => Finsupp.single_eq_of_ne (hα d).symm)

theorem positiveUnivariate_zero (v : Fin s → V) : coefficients (positiveUnivariate v) 0 = 0 := by
  apply positiveUnivariate_coefficient_eq_zero
  intro d h
  have h' := congrArg (fun α : Unit →₀ ℕ => α ()) h
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at h'
  omega

theorem positiveUnivariate_coefficients_mem (v : Fin s → V) (U : (Unit →₀ ℕ) → Submodule ℚ V)
    (hv : ∀ d, v d ∈ U (Finsupp.single () (d.val + 1))) :
    ∀ α, coefficients (positiveUnivariate v) α ∈ U α := by
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    exact hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα)]
    exact (U α).zero_mem

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem positiveUnivariate_coefficientBound (b : Basis ι ℝ L) (v : Fin s → L)
    (T : Unit → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ d, ‖b.equivFun (v d)‖ ≤ M / monomialScale T (Finsupp.single () (d.val + 1))) :
    CoefficientBound b T M (positiveUnivariate v) := by
  apply (coefficientBound_iff_norm b T hT hM _).mpr
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    exact hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα),
      map_zero, norm_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem positiveUnivariate_coefficientGrid (b : Basis ι ℝ L) (v : Fin s → L) (l : ℕ)
    (hv : ∀ d, b.equivFun (v d) ∈ realDenominatorGrid l) :
    CoefficientGrid b l (positiveUnivariate v) := by
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    simpa only [Basis.equivFun_apply] using hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα)]
    refine ⟨0, ?_⟩
    ext i
    simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ ι V : Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_outer_polynomial_product_bounds (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ qs rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
        qs.length ≤ k → rs.length ≤ k →
        (∀ q ∈ qs, q.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ q ∈ qs, CoefficientBound (b.baseChange ℝ) (fun _ => 1)
          (Real.exp ((p + 2) ^ a)) q.coord) →
        (∀ r ∈ rs, CoefficientGrid (b.baseChange ℝ) l r.coord) →
        CoefficientBound (b.baseChange ℝ) (fun _ => 1)
          (Real.exp ((p + C) ^ C)) qs.prod.coord ∧
        CoefficientGrid (b.baseChange ℝ) m rs.reverse.prod.coord := by
  obtain ⟨Cs, hCs, hslow⟩ := exists_formal_polynomial_product_bound s a k
  obtain ⟨Cr, hCr, hrat⟩ := exists_formal_polynomial_product_grid s k
  refine ⟨max Cs Cr, hCs.trans (le_max_left _ _), ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  have hbs : (p + Cs) ^ Cs ≤ (p + (max Cs Cr : ℕ)) ^ max Cs Cr :=
    shifted_power_self_mono hp (by omega) (le_max_left _ _)
  have hbr : (p + Cr) ^ Cr ≤ (p + (max Cs Cr : ℕ)) ^ max Cs Cr :=
    shifted_power_self_mono hp (by omega) (le_max_right _ _)
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ := hrat F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hbr), hlm, ?_⟩
  intro qs rs hqs hrs hqa hra hqb hrb
  constructor
  · have h := hslow F b ω hF H p hH hp hι hσ hHp hstructure
      (fun _ => 1) (fun _ => zero_lt_one) qs hqs hqa hqb
    intro α i
    exact (h α i).trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr hbs) (monomialScale_pos (fun _ => 1) (fun _ => zero_lt_one) α).le)
  · exact hgrid rs.reverse (by simpa only [List.length_reverse] using hrs)
      (fun r hr => hra r (List.mem_reverse.mp hr))
      (fun r hr => hrb r (List.mem_reverse.mp hr))

end Erdos3.NilpotentLieFiltration

end

end OAI

end


