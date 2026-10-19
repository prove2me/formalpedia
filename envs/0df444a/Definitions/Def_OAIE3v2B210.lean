-- Prove2me | Definitions.Def_OAIE3v2B210
-- name    : OAIE3v2B210
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:15:19.174656+00:00
-- url     : https://prove2.me/theorems/da77c159-96ba-469d-bdbb-78b6bfc8dc15
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 214 of 311
-- statement:
--   Definitions bundle 214 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B299`, `OAIE3v2B186`, `OAIE3v2B188`, `OAIE3v2B189`, `OAIE3v2B190`, `OAIE3v2B191` of this split.
--
--   Modules: `Estimates/CommonRefilteredMappedOrbitFactors.lean`, `Estimates/ControlledFixedMarkedNativeFactorization.lean`, `Estimates/ControlledPrescribedMarkedNativeFactorization.lean`, `Estimates/FrozenMarkedLeftOrbitBound.lean`, `Estimates/NativeDetectorContradictionSpec.lean`, `Estimates/NativeFrozenMarkedLocalMark.lean`, `Estimates/PositiveShiftRefilteredExpansionSpec.lean`, `Lattices/PrimeStabilityTree.lean`, `Lattices/UniformExternalMarkedAffineSliceFreezingDictionary.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Polynomial/NativeMarkedPolynomialFreezing.lean`, `Polynomial/PolynomialSymbolBasisIndependence.lean`, `Polynomial/RealPolynomialGroupMapChart.lean`, `Sampling/FrozenMarkedRightOrbitGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B186
import Definitions.Def_OAIE3v2B188
import Definitions.Def_OAIE3v2B189
import Definitions.Def_OAIE3v2B190
import Definitions.Def_OAIE3v2B191

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

omit [Fintype ι] [Fintype κ] in

theorem realPolynomialGroupMap_middle_mem (w : σ → ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : ∀ z : σ → ℝ, eval₂ z (F.realGradedSymbolPolynomial b ω hF w
      (F.realPolynomialSymbolHom b ω hF w g).coord) ∈ realificationLieSubalgebra W) :
    ∀ z : σ → ℝ, eval₂ z (G.realGradedSymbolPolynomial c ν hG w
      (G.realPolynomialSymbolHom c ν hG w
        (F.realPolynomialGroupMap G φ hφ w g)).coord) ∈
      realificationLieSubalgebra (W.map (F.associatedGradedMap G φ hφ)) := by
  have hmem := (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mpr hg
  have hmap := F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ w W
    (F.realPolynomialSymbolHom b ω hF w g).coord hmem
  have hsymbol : realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w)
      (F.realPolynomialSymbolHom b ω hF w g).coord =
      (G.realPolynomialSymbolHom c ν hG w
        (F.realPolynomialGroupMap G φ hφ w g)).coord :=
    F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c ν hG w g.coord
  rw [hsymbol] at hmap
  exact (G.mem_real_symbolPointwiseSubalgebra_iff_values c ν hG w _ _).mp hmap

theorem exists_common_refiltered_mapped_orbit_factors
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hsource : (Fintype.card ι : ℝ) ≤ p)
    (htarget : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (side : σ → ℝ), (∀ i, 0 < side i) →
      ∀ (q : ℝ) (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
      G.HasCommonRefilteredOrbitFactors c ν hG side ((p + 2) ^ 3 + q) m
        (W.map (F.associatedGradedMap G φ hφ))
        (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) := by
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    F.exists_realPolynomialGroupMap_grid G b c φ hφ (fun _ : σ => 1)
      hentries hp hsource htarget hHp l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro side hside q W g hfactor
  obtain ⟨e, middle, r, hprod, hmid, he, hr, he0, hr0, hmiddle0⟩ := hfactor
  let π := F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1)
  refine ⟨π e, π middle, π r, ?_, ?_, ?_, hgrid r hr, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hprod]
  · exact F.realPolynomialGroupMap_middle_mem G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) W middle hmid
  · have hslow := F.realPolynomialGroupMap_slow_exp G b c φ hφ
      (fun _ : σ => 1) hentries hp hsource hHp side hside (Real.exp_nonneg q) e he
    simpa only [Real.exp_add] using hslow
  · change coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) e).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 = 0
    rw [F.realPolynomialGroupMap_coefficient, he0, map_zero]
  · change coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) r).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 = 0
    rw [F.realPolynomialGroupMap_coefficient, hr0, map_zero]
  · change coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) middle).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 =
      coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0
    rw [F.realPolynomialGroupMap_coefficient, F.realPolynomialGroupMap_coefficient, hmiddle0]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeMarkedPolynomialFreezing
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module NilpotentLieBCHGroup
open scoped TensorProduct
variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

variable (w : σ → ℕ)

theorem frozenMarked_factors_mark
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kE kR : F.realification.Group)
    (hkE : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1) :
    F.realPolynomialGroupMap G φ hφ w (F.frozenMarkedLeft G w S hS EF kE) = EF ∧
    F.realPolynomialGroupMap G φ hφ w (F.frozenMarkedRight G w S hS RF kR) = RF := by
  simp only [frozenMarkedLeft, frozenMarkedRight, map_mul,
    realPolynomialGroupMap_constant, hkE, hkR, map_one, one_mul, mul_one,
    realPolynomialGroupMap_filteredSection, hsection, and_self]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenMarkedLeftOrbitBound
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)

noncomputable def frozenMarkedRightOrbit
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group) :
    F.realification.PolynomialOrbit w :=
  (F.realification.polynomialOrbitCoordinates w).symm
    (F.frozenMarkedRight G w S hS
      (G.realification.polynomialOrbitCoordinates w marked) center)

theorem frozenMarkedLeftOrbit_realEval
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      (F.frozenMarkedLeftOrbit G w S hS marked center) =
      center * ⟨S.baseChange ℝ (G.realification.polynomialOrbitRealEval w x marked).coord⟩ := by
  rw [frozenMarkedLeftOrbit, F.nativeFrozenMarkedOrbitCoordinates_symm_realEval,
    frozenMarkedLeft, map_mul, F.adaptedPolynomialRealValueHom_constant,
    F.filteredRealPolynomialSection_value, G.nativeFrozenMarkedOrbitCoordinates_realValue]

theorem frozenMarkedRightOrbit_realEval
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      (F.frozenMarkedRightOrbit G w S hS marked center) =
      ⟨S.baseChange ℝ (G.realification.polynomialOrbitRealEval w x marked).coord⟩ * center := by
  rw [frozenMarkedRightOrbit, F.nativeFrozenMarkedOrbitCoordinates_symm_realEval,
    frozenMarkedRight, map_mul, F.adaptedPolynomialRealValueHom_constant,
    F.filteredRealPolynomialSection_value, G.nativeFrozenMarkedOrbitCoordinates_realValue]

theorem frozenMarkedLeftOrbit_realEval_eq_local
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (v : η → ℕ) (localMarked : (G.realification.adaptedPolynomialFiltration v).Group)
    (x : η → ℝ) (y : σ → ℝ)
    (hmarked : G.adaptedPolynomialRealValueHom v x localMarked =
      G.realification.polynomialOrbitRealEval w y marked) :
    F.realification.polynomialOrbitRealEval w y
      (F.frozenMarkedLeftOrbit G w S hS marked center) =
      F.adaptedPolynomialRealValueHom v x (F.frozenMarkedLeft G v S hS localMarked center) := by
  rw [F.frozenMarkedLeftOrbit_realEval, frozenMarkedLeft, map_mul,
    F.adaptedPolynomialRealValueHom_constant, F.filteredRealPolynomialSection_value, hmarked]

theorem frozenMarkedRightOrbit_realEval_eq_local
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (v : η → ℕ) (localMarked : (G.realification.adaptedPolynomialFiltration v).Group)
    (x : η → ℝ) (y : σ → ℝ)
    (hmarked : G.adaptedPolynomialRealValueHom v x localMarked =
      G.realification.polynomialOrbitRealEval w y marked) :
    F.realification.polynomialOrbitRealEval w y
      (F.frozenMarkedRightOrbit G w S hS marked center) =
      F.adaptedPolynomialRealValueHom v x (F.frozenMarkedRight G v S hS localMarked center) := by
  rw [F.frozenMarkedRightOrbit_realEval, frozenMarkedRight, map_mul,
    F.adaptedPolynomialRealValueHom_constant, F.filteredRealPolynomialSection_value, hmarked]

variable (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (hsection : Function.RightInverse S φ)

include hφ hsection

theorem frozenMarkedLeftOrbit_formal_mark
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (hcenter : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ center = 1) :
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      (F.frozenMarkedLeftOrbit G w S hS marked center).log = marked.log := by
  have h := (F.frozenMarked_factors_mark G w φ hφ S hS hsection
    (G.realification.polynomialOrbitCoordinates w marked)
    (G.realification.polynomialOrbitCoordinates w marked) center center hcenter hcenter).1
  exact congrArg (fun q : (G.realification.adaptedPolynomialFiltration w).Group =>
    (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) h

theorem frozenMarkedRightOrbit_formal_mark
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (hcenter : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ center = 1) :
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      (F.frozenMarkedRightOrbit G w S hS marked center).log = marked.log := by
  have h := (F.frozenMarked_factors_mark G w φ hφ S hS hsection
    (G.realification.polynomialOrbitCoordinates w marked)
    (G.realification.polynomialOrbitCoordinates w marked) center center hcenter hcenter).2
  exact congrArg (fun q : (G.realification.adaptedPolynomialFiltration w).Group =>
    (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_frozenMarkedLeftOrbit_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
        [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
        (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
        (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H HS : ℕ) (p : ℝ),
        0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
        (H : ℝ) ≤ Real.exp p → (HS : ℝ) ≤ Real.exp p →
        (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
        (∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) HS) →
        ∀ (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
          (x : σ → ℤ),
          (∀ i, |(c.baseChange ℝ).repr
            (G.realification.polynomialOrbitEval w x marked).coord i| ≤ Real.exp p) →
          (∀ i, |(b.baseChange ℝ).repr center.coord i| ≤ Real.exp p) →
          ∀ i, |(b.baseChange ℝ).repr
            (F.realification.polynomialOrbitEval w x
              (F.frozenMarkedLeftOrbit G w S hS marked center)).coord i| ≤
                Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hproduct⟩ := exists_bch_fixed_product_exp_bound s 2 2
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G b c w S hS H HS p hp hd hdmark hH hHS hb hSheight
    marked center x hmarked hcenter i
  have hmarkedNorm :
      ‖(c.baseChange ℝ).equivFun
        (G.realification.polynomialOrbitEval w x marked).coord‖ ≤ Real.exp p := by
    apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg p)).mpr
    intro j
    simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using hmarked j
  have hdim : (Fintype.card κ : ℝ) + 1 ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hheight : (HS : ℝ) + 1 ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp p * 2 := by linarith [Real.one_le_exp hp]
      _ ≤ Real.exp p * Real.exp 1 :=
        mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg p)
      _ = _ := (Real.exp_add _ _).symm
  have hsectionNorm :
      ‖(b.baseChange ℝ).equivFun
        (S.baseChange ℝ (G.realification.polynomialOrbitEval w x marked).coord)‖ ≤
          Real.exp ((p + 2) ^ 2) := by
    apply (realified_linear_coordinate_norm c b S hSheight _).trans
    calc
      _ ≤ (Real.exp p * Real.exp (p + 1)) * Real.exp p :=
        mul_le_mul (mul_le_mul hdim hheight (by positivity) (Real.exp_nonneg p))
          hmarkedNorm (norm_nonneg _) (by positivity)
      _ = Real.exp (3 * p + 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  let sectionValue : F.realification.Group :=
    ⟨S.baseChange ℝ (G.realification.polynomialOrbitEval w x marked).coord⟩
  have hsection (j : ι) :
      |(b.baseChange ℝ).repr sectionValue.coord j| ≤ Real.exp ((p + 2) ^ 2) := by
    have hj := norm_le_pi_norm ((b.baseChange ℝ).equivFun sectionValue.coord) j
    have hj' : |(b.baseChange ℝ).repr sectionValue.coord j| ≤
        ‖(b.baseChange ℝ).equivFun sectionValue.coord‖ := by
      simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using hj
    exact hj'.trans hsectionNorm
  have hcenter' (j : ι) :
      |(b.baseChange ℝ).repr center.coord j| ≤ Real.exp ((p + 2) ^ 2) :=
    (hcenter j).trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p]))
  have hbound := hproduct (b.baseChange ℝ) (lieStructureConstants b) H p
    F.realification.lowerCentralSeries_eq_bot [center, sectionValue]
    (fun j k z => (realLieBasis_structure b j k z).symm) hp hd (by simp) hH hb
    (by
      intro a ha j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hcenter' j
      · exact hsection j) i
  rw [← polynomialOrbitRealEval_integer, frozenMarkedLeftOrbit_realEval,
    polynomialOrbitRealEval_integer]
  simpa only [List.prod_cons, List.prod_nil, mul_one] using hbound

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)

include hsection

theorem frozenMarkedOuter_product_mark_eq
    (v : η → ℕ)
    (g E P R : (F.realification.adaptedPolynomialFiltration v).Group)
    (hfactor : E * P * R = g)
    (EF RF : (G.realification.adaptedPolynomialFiltration v).Group)
    (hE : F.realPolynomialGroupMap G φ hφ v E = EF)
    (hR : F.realPolynomialGroupMap G φ hφ v R = RF)
    (w : σ → ℕ) (leftMark rightMark : G.realification.PolynomialOrbit w)
    (kE kR : F.realification.Group)
    (hkE : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1)
    (x : η → ℝ) (y : σ → ℝ)
    (hleft : G.adaptedPolynomialRealValueHom v x EF =
      G.realification.polynomialOrbitRealEval w y leftMark)
    (hright : G.adaptedPolynomialRealValueHom v x RF =
      G.realification.polynomialOrbitRealEval w y rightMark) :
    realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ
      (F.realification.polynomialOrbitRealEval w y
          (F.frozenMarkedLeftOrbit G w S hS leftMark kE) *
        F.adaptedPolynomialRealValueHom v x P *
        F.realification.polynomialOrbitRealEval w y
          (F.frozenMarkedRightOrbit G w S hS rightMark kR)) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
        (F.adaptedPolynomialRealValueHom v x g) := by
  have hl := F.formal_mark_realEval G φ w
    (F.frozenMarkedLeftOrbit G w S hS leftMark kE) leftMark
    (F.frozenMarkedLeftOrbit_formal_mark G w S hS φ hφ hsection leftMark kE hkE) y
  have hr := F.formal_mark_realEval G φ w
    (F.frozenMarkedRightOrbit G w S hS rightMark kR) rightMark
    (F.frozenMarkedRightOrbit_formal_mark G w S hS φ hφ hsection rightMark kR hkR) y
  rw [← hfactor]
  simp only [map_mul, hl, hr]
  rw [← F.realPolynomialGroupMap_value G φ hφ v E x,
    ← F.realPolynomialGroupMap_value G φ hφ v R x, hE, hR, hleft, hright]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledFixedMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_marked_native_factorization (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype ξ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (τ : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card ξ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((markedNativeLiftInput p + C) ^ C) ∧ l ∣ m ∧
    ∀ (U : LieSubalgebra ℚ F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule →
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
    ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
      (E P R : F.RealPolynomialSymbolGroup w),
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) →
    ∀ EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ E.coord =
        (G.realPolynomialSymbolHom c τ hG w EF).coord →
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ R.coord =
        (G.realPolynomialSymbolHom c τ hG w RF).coord →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      CoefficientBound (c.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) EF.coord.val →
      F.SymbolRationalGrid b ω hF w l R →
      CoefficientGrid (c.baseChange ℝ) l RF.coord.val →
      coefficients ((EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
        G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      e * middle * r = g ∧
      F.realPolynomialSymbolHom b ω hF w e = E ∧
      F.realPolynomialSymbolHom b ω hF w middle = P ∧
      F.realPolynomialSymbolHom b ω hF w r = R ∧
      F.realPolynomialGroupMap G φ hφ w e = EF ∧
      F.realPolynomialGroupMap G φ hφ w r = RF ∧
      F.realPolynomialGroupMap G φ hφ w middle =
        EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹ ∧
      F.PolynomialSlowBound b w T (Real.exp ((markedNativeLiftInput p + C) ^ C)) e ∧
      F.PolynomialRationalGrid b w m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w z q) =
          F.adaptedPolynomialRealValueHom w z middle := by
  obtain ⟨C, hC, hnormalize⟩ := exists_controlled_marked_kernel_normalization s (a + 12)
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ξ L M _ _ _ _ _ _ _ _ F G φ hφ b ω hF c τ hG w hw hsurj
    bk H l p hH hl hp hι hκ hξ hσ hHp hlp hbracket hkernel hentries
  obtain ⟨m₀, hm₀, hm₀p, hlm₀, hlift⟩ := F.exists_controlled_marked_polynomial_factorization
    G φ hφ b ω hF c τ hG w hsurj hH hl hentries hp hι hκ hHp hlp
  let B := markedNativeLiftInput p
  have hpB : p ≤ B := by
    dsimp [B, markedNativeLiftInput]
    exact le_add_of_nonneg_left (by positivity)
  have hB : 0 ≤ B := hp.trans hpB
  have hm₀B : (m₀ : ℝ) ≤ Real.exp B := hm₀p.trans (Real.exp_le_exp.mpr
    (by dsimp [B, markedNativeLiftInput]; exact le_add_of_nonneg_right hp))
  obtain ⟨m, hm, hmp, hm₀m, hnorm⟩ := hnormalize F G φ hφ b ω hF w hw bk H m₀ B
    hH hm₀ hB (hι.trans hpB) (hξ.trans hpB) (hσ.trans hpB)
    (hHp.trans (Real.exp_le_exp.mpr hpB)) hm₀B hbracket hkernel
  refine ⟨m, hm, hmp, hlm₀.trans hm₀m, ?_⟩
  intro U hU T hT g E P R hprod hP EF RF hE hR hEslow hEF hRgrid hRF hconstant
  obtain ⟨e₀, middle₀, r₀, hprod₀, he₀, hp₀, hr₀, heF₀, hrF₀, hpF₀,
    hebound₀, hrgrid₀⟩ := hlift a T hT g E P R hprod EF RF hE hR hEslow hEF hRgrid hRF
  have hebound : F.PolynomialSlowBound b w T (Real.exp ((B + 2) ^ (a + 12))) e₀ :=
    F.polynomialSlowBound_mono b w T hT
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) _)) e₀ hebound₀
  have hrgrid : F.PolynomialRationalGrid b w m₀ r₀ := by
    choose v hv using hrgrid₀
    exact ⟨fun z => v z.1 z.2, funext (fun z => congrFun (hv z.1) z.2)⟩
  have hpc : realificationLieHom φ
      (coefficients (middle₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
      ((F.gradedRefiltrationLayer U 1).map φ.toLinearMap).baseChange ℝ := by
    rw [F.gradedRefiltrationLayer_map G b ω hF c τ hG φ hφ U hU hsurj]
    have hlog := congrArg (fun z => coefficients
      (z.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0) hpF₀
    rw [F.realPolynomialGroupMap_log, coefficients_map] at hlog
    change realificationLieHom φ (coefficients
      (middle₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) = _ at hlog
    rwa [hlog]
  obtain ⟨u, v, e, middle, r, _, _, _, _, hproduct, hEs, hPs, hRs,
    hEm, hPm, hRm, hconst, heslow, hrgrid⟩ := hnorm (F.gradedRefiltrationLayer U 1)
      (F.layer_succ_le_gradedRefiltrationLayer U 1) T hT e₀ middle₀ r₀ hebound hrgrid hpc
  have hmiddle : F.realPolynomialSymbolHom b ω hF w middle = P := hPs.trans hp₀
  have hvalues := (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w U
    (F.realPolynomialSymbolHom b ω hF w middle).coord).mp
      (by rw [hmiddle]; exact hP)
  obtain ⟨q, hq, hqvalues⟩ := F.exists_native_pointwise_refiltered_orbit_of_constant U
    b ω hF w hw middle.coord hconst hvalues
  exact ⟨e, middle, r, q, hproduct.trans hprod₀, hEs.trans he₀, hmiddle, hRs.trans hr₀,
    hEm.trans heF₀, hRm.trans hrF₀, hPm.trans hpF₀, heslow, hrgrid, hq, hqvalues⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct NNReal

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)
  [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w ν)]

theorem realFilteredSymbolGroupMap_grid (l : ℕ) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolRationalGrid b ω hF w l g) :
    G.SymbolRationalGrid c ν hG w
      (F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w * l)
      (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  classical
  have h := realified_linear_coordinate_grid
    (F.polynomialSymbolBasis b ω hF w) (G.polynomialSymbolBasis c ν hG w)
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap l g.coord hg
  have hm : LinearMap.toMatrix (F.polynomialSymbolBasis b ω hF w)
      (G.polynomialSymbolBasis c ν hG w)
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap =
      fun i j => (G.polynomialSymbolBasis c ν hG w).repr
        (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis b ω hF w j)) i := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [hm] at h
  exact h

theorem filteredSymbolMapDenominator_le_exp {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    (F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w : ℝ) ≤
      Real.exp ((p + 2) ^ 3) := by
  apply matrixDenominator_le_exp_power _ hp 1 htarget hsource
  intro i j
  have h := (F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w
    hH hentries j i).2
  exact (Nat.cast_le.mpr h).trans (hHp.trans (Real.exp_le_exp.mpr (by simp)))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansionSpec
namespace OAI

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  (B : PositiveShiftBasis.{u} s N q a J) {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))
  (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
  (R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1))
  (anchor : ZMod N) (H : Finset (ZMod N)) (p : ℝ)

variable {B D E A R anchor H p}

def CommonFactorization.mono (F : B.CommonFactorization D E A R anchor H p) {p' : ℝ} (hpp' : p ≤ p') :
    B.CommonFactorization D E A R anchor H p' where
  weight := F.weight
  adapted := F.adapted
  subalgebra := F.subalgebra
  spanning := F.spanning
  span_eq := F.span_eq
  graded := F.graded
  height := fun i k => (F.height i k).trans hpp'
  denominator := F.denominator
  denominator_pos := F.denominator_pos
  denominator_bound := F.denominator_bound.trans (Real.exp_le_exp.mpr hpp')
  shifts := F.shifts
  shifts_sub := F.shifts_sub
  shifts_nonempty := F.shifts_nonempty
  shifts_large := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpp'))
    (Nat.cast_nonneg N)).trans F.shifts_large
  factors := fun h hh => (F.factors h hh).mono (B.anchoredFactors D E) none hpp'
    (fun _ => by exact_mod_cast NeZero.pos N)
  frequency := F.frequency
  frequency_zero := F.frequency_zero
  invariant := F.invariant

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDetectorContradictionSpec
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure SquareModelData (D : RationalFilteredNilmanifold L (s + 1) d) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  layers : ∀ i, D.filtration.layer i = Submodule.span ℚ (basis '' {j | i ≤ weight j})
  grid : ℕ
  grid_pos : 0 < grid
  inner : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates
    (D.filtration.squareFinBasis basis weight (layers 2)) (D.filtration.squareLattice D.lattice)
  outer : bchSubgroupCoordinates (D.filtration.squareFinBasis basis weight (layers 2))
    (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid grid

namespace SquareModelData

variable {D : RationalFilteredNilmanifold L (s + 1) d}

noncomputable def fullModel (F : D.SquareModelData) :=
  D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis F.basis F.weight (F.layers 2)) (squareFinWeight F.weight)
    (D.filtration.squareFinBasis_layers F.basis F.weight F.layers)
    (D.filtration.squareLattice D.lattice) F.grid F.grid_pos F.inner F.outer

noncomputable def quotientModel (F : D.SquareModelData) :=
  D.filtration.squareFiltration.topQuotientModel
    (D.filtration.squareFinBasis F.basis F.weight (F.layers 2)) (squareFinWeight F.weight)
    (D.filtration.squareFinBasis_layers F.basis F.weight F.layers)
    (D.filtration.squareLattice D.lattice) F.grid F.grid_pos F.inner F.outer

end SquareModelData
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeStabilityTree
namespace OAI

section

namespace Erdos3

open PhysicalEpochStack
open scoped BigOperators

universe u v w

structure PrimeStabilityContext (ι : Type w) (σ : Type u) [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (s bound : ℕ) where
  parameters : PhysicalStabilityParameters.{u, v} s
  base : PhysicalEpochSource.{u, v} σ s bound
  baseline : base.model.Niltest (fun _ : σ => 1)
  orbit : baseline.orbit = base.fixedMap.orbit
  positive : baseline.UnitIntervalValued
  complexity : baseline.ComplexityLE base.incomingBudget
  recordCap : ℝ
  recordCap_nonneg : 0 ≤ recordCap
  record_le_cap : base.recordBudget ≤ recordCap
  inflation : (base.incomingBudget + 2) ^ parameters.A ≤ base.recordBudget
  record_two : 2 ≤ base.recordBudget
  gap : ℝ
  gap_pos : 0 < gap
  gap_le_one : gap ≤ 1
  gap_inverse : gap⁻¹ ≤ Real.exp base.incomingBudget
  prime : ι → ℕ
  power : ι → ℕ
  prime_prime : ∀ i, (prime i).Prime
  prime_injective : Function.Injective prime
  primeBudget : ℝ
  primeBudget_nonneg : 0 ≤ primeBudget
  prime_bound : ∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp primeBudget
  witnessSize : ℕ
  mandatory : Finset ι

namespace PrimeStabilityContext

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ}

def moduli (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (i : ι) : ℕ :=
  ctx.prime i ^ ctx.power i

def workBudget (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : ℝ :=
  physicalEpochBudget ctx.parameters.A ctx.parameters.C ctx.recordCap s

noncomputable def periodCap (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : ℕ :=
  ⌈2 * ((s : ℝ) * ctx.workBudget)⌉₊

noncomputable def stepCost (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : ℕ :=
  ctx.periodCap + ctx.witnessSize

noncomputable def allowance (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : ℕ :=
  ctx.mandatory.card + ctx.stepCost * (bound + 1) ^ s

noncomputable def HasLargeSides (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : Prop :=
  ∀ i, Real.exp (ctx.primeBudget * ctx.allowance + 5 * ctx.workBudget +
    2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) ≤ (ctx.base.sides i : ℝ)

noncomputable def Good (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound)
    (I : Finset ι) (x : ∀ i, σ → ZMod (ctx.moduli i)) : Prop :=
  PrimeCoordinateStable ctx.baseline.eval ctx.base.lower ctx.base.sides ctx.moduli ctx.witnessSize ctx.gap I x

structure State (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound)
    (I : Finset ι) (x : ∀ i, σ → ZMod (ctx.moduli i)) where
  anchor : σ → ℤ
  anchor_mem : anchor ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli I x
  stack : PhysicalEpochStack ctx.base
  scheduled : ScheduledAt ctx.parameters.A ctx.parameters.C ctx.recordCap 0 stack
  aligned : AlignedAt (∏ i ∈ I, ctx.moduli i) anchor stack
  room : I.card + ctx.stepCost * (epochStackRank bound stack.dimensions + 1) ≤ ctx.allowance

end PrimeStabilityContext

end Erdos3

end

section

namespace Erdos3.PrimeStabilityContext

open PhysicalEpochStack
open scoped BigOperators

universe u v w

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ}

variable {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
  {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)}

noncomputable def State.periodBatch (state : ctx.State I x) : Finset ι :=
  periodPrimeCoordinates ctx.prime state.stack.periods.prod \ I

end Erdos3.PrimeStabilityContext

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

noncomputable def Niltest.markedFrozenValue
    {σ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d} {v : σ → ℕ}
    (test : D.Niltest v) (F : NilpotentLieFiltration T t) (w : σ → ℕ)
    (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (EF RF : (F.realification.adaptedPolynomialFiltration w).Group)
    (P : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (kE kR : D.RealGroup) (x : σ → ℤ) : ℂ :=
  test.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
    (fun i => (x i : ℝ)) (D.filtration.frozenMarkedLeft F w S hS EF kE * P *
      D.filtration.frozenMarkedRight F w S hS RF kR)))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

namespace ExternalMarkedAffineSliceFreezing

structure Dictionary
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) where
  grid : ℕ
  Q : ℕ
  modulus : ℕ
  denominator : ℕ
  rightCount : ℕ
  grid_pos : 0 < grid
  Q_pos : 0 < Q
  modulus_pos : 0 < modulus
  denominator_pos : 0 < denominator
  rightCount_pos : 0 < rightCount
  Q_bound : (Q : ℝ) ≤ max 1 B
  gridCard_bound : (Fintype.card (Fin d → Fin (grid + 1)) : ℝ) ≤ B
  cellCard_bound : (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B
  modulus_bound : (modulus : ℝ) ≤ B
  denominator_bound : (denominator : ℝ) ≤ B
  rightCount_bound : (rightCount : ℝ) ≤ B
  pairCard_bound : (Fintype.card ((Fin d → Fin (grid + 1)) × Fin rightCount) : ℝ) ≤ B ^ 2
  left : (Fin d → Fin (grid + 1)) → D.RealGroup
  right : Fin rightCount → D.RealGroup
  left_bounds : ∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
    ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B
  right_bounds : ∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
    (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
    (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid denominator
  select : ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (EF : (F.realification.adaptedPolynomialFiltration w).Group)
    (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (RF : (F.realification.adaptedPolynomialFiltration w).Group),
    D.filtration.PolynomialSlowBound D.basis w Tbox A E →
    F.PolynomialSlowBound c w Tbox A EF →
    D.filtration.PolynomialRationalGrid D.basis w l R →
    F.PolynomialRationalGrid c w l RF →
    D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
    D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
    (∀ i j,
      D.filtration.realPolynomialGroupMap F φ hφ w
        (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
      D.filtration.realPolynomialGroupMap F φ hφ w
        (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
    ∀ (tests : X → D.Niltest w) (physical : (σ → ℤ) → X)
      (weight : (σ → ℤ) → ℂ) (Bweight Bobs Lip : ℝ),
      0 ≤ Bweight → 0 ≤ Bobs → 0 ≤ Lip →
      (∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ Tbox i) → ‖weight x‖ ≤ Bweight) →
      (∀ z, ((tests z).normBound : ℝ) ≤ Bobs) →
      (∀ z, ((tests z).lipBound : ℝ) ≤ Lip) →
      ∀ (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
      E * P * R = g →
      ∀ Nparent : σ → ℕ, (∀ i, 0 < Nparent i) →
      ∀ (origin : σ → ℤ) (step : ℕ),
      (∀ i v, v < Nparent i → |(origin i : ℝ) + step * v| ≤ Tbox i) →
      (∀ i, (step : ℝ) * Nparent i ≤ 2 * Tbox i) →
      (∀ i, 2 * (modulus : ℝ) ≤ (1 / (Q : ℝ)) * Nparent i) →
      ∀ τ θ Sscore : ℝ, 0 ≤ τ → 0 < θ →
      (Sscore ≤ 𝔼 x : (∀ i, Fin (Nparent i)),
        (weight (affineParentIntegerPoint Nparent origin step x) *
          (tests (physical (affineParentIntegerPoint Nparent origin step x))).observable
            (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
              (fun i => (affineParentIntegerPoint Nparent origin step x i : ℝ)) g))).re) →
      τ + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < Sscore →
      ∃ A : ResidueBoxSlice Nparent modulus, (∀ i, 0 < A.length i) ∧
        (∀ i, θ * Nparent i / (4 * modulus * Q * (Fintype.card σ + 1 : ℝ)) ≤ A.length i) ∧
        ∃ i j,
          (∀ x : ∀ i, Fin (A.length i),
            ‖(tests (physical (A.affineIntegerPoint origin step x))).observable
                (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                  (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
              (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                F w S hS EF RF P (left i) (right j)
                (A.affineIntegerPoint origin step x)‖ ≤ Lip * ε) ∧
          (∀ x : ∀ i, Fin (A.length i),
            ‖weight (A.affineIntegerPoint origin step x) *
                (tests (physical (A.affineIntegerPoint origin step x))).observable
                  (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                    (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
              weight (A.affineIntegerPoint origin step x) *
                (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                  F w S hS EF RF P (left i) (right j)
                  (A.affineIntegerPoint origin step x)‖ ≤ Bweight * (Lip * ε)) ∧
          τ < 𝔼 x : (∀ i, Fin (A.length i)),
            (weight (A.affineIntegerPoint origin step x) *
              (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                F w S hS EF RF P (left i) (right j)
                (A.affineIntegerPoint origin step x)).re

end ExternalMarkedAffineSliceFreezing

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary

open Module
open scoped TensorProduct

variable {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A A' ε B : ℝ}
    (dictionary : Dictionary (X := X) D F c φ hφ w S hS l Tbox A ε B)

def mono_slow (hT : ∀ i, 0 < Tbox i) (hslow : A' ≤ A) :
    Dictionary (X := X) D F c φ hφ w S hS l Tbox A' ε B where
  grid := dictionary.grid
  Q := dictionary.Q
  modulus := dictionary.modulus
  denominator := dictionary.denominator
  rightCount := dictionary.rightCount
  grid_pos := dictionary.grid_pos
  Q_pos := dictionary.Q_pos
  modulus_pos := dictionary.modulus_pos
  denominator_pos := dictionary.denominator_pos
  rightCount_pos := dictionary.rightCount_pos
  Q_bound := dictionary.Q_bound
  gridCard_bound := dictionary.gridCard_bound
  cellCard_bound := dictionary.cellCard_bound
  modulus_bound := dictionary.modulus_bound
  denominator_bound := dictionary.denominator_bound
  rightCount_bound := dictionary.rightCount_bound
  pairCard_bound := dictionary.pairCard_bound
  left := dictionary.left
  right := dictionary.right
  left_bounds := dictionary.left_bounds
  right_bounds := dictionary.right_bounds
  select := by
    intro E EF R RF hE hEF
    exact dictionary.select E EF R RF
      (D.filtration.polynomialSlowBound_mono D.basis w Tbox hT hslow E hE)
      (F.polynomialSlowBound_mono c w Tbox hT hslow EF hEF)

variable (hT : ∀ i, 0 < Tbox i) (hslow : A' ≤ A)

@[simp] theorem mono_slow_grid :
    (dictionary.mono_slow hT hslow).grid = dictionary.grid := rfl

@[simp] theorem mono_slow_Q :
    (dictionary.mono_slow hT hslow).Q = dictionary.Q := rfl

@[simp] theorem mono_slow_modulus :
    (dictionary.mono_slow hT hslow).modulus = dictionary.modulus := rfl

@[simp] theorem mono_slow_denominator :
    (dictionary.mono_slow hT hslow).denominator = dictionary.denominator := rfl

@[simp] theorem mono_slow_rightCount :
    (dictionary.mono_slow hT hslow).rightCount = dictionary.rightCount := rfl

@[simp] theorem mono_slow_left :
    (dictionary.mono_slow hT hslow).left = dictionary.left := rfl

@[simp] theorem mono_slow_right :
    (dictionary.mono_slow hT hslow).right = dictionary.right := rfl

end Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedSmoothRankCoefficientIndex (X : Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, (SpatialDegreeOutput X j ⊕ AllocatedCongruenceIntegerAxis inactive j) × Fin L

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

universe v

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

def optionPairProjection (j : ι) :
    (∀ i : Option ι, optionLieSpace L₀ L i) →ₗ⁅ℚ⁆ PairAlgebra L₀ (L j) :=
  liePiMap (fun b => by
    cases b
    · exact liePiEval (some j)
    · exact liePiEval none)

@[simp] theorem optionPairProjection_true (j : ι)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    optionPairProjection j x true = x none := rfl

@[simp] theorem optionPairProjection_false (j : ι)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    optionPairProjection j x false = x (some j) := rfl

@[simp] theorem pairFrequency_optionPairProjection (j : ι)
    (η : L₀ →ₗ[ℚ] ℚ) (θ : L j →ₗ[ℚ] ℚ)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    pairFrequency η θ (optionPairProjection j x) = η (x none) + θ (x (some j)) := by
  rw [pairFrequency_apply, optionPairProjection_true, optionPairProjection_false]

@[simp] theorem realification_optionPairProjection_true (j : ι)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) :
    realificationLieHom (liePiEval true) (realificationLieHom (optionPairProjection j) x) =
      realificationLieHom (liePiEval none) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

@[simp] theorem realification_optionPairProjection_false (j : ι)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) :
    realificationLieHom (liePiEval false) (realificationLieHom (optionPairProjection j) x) =
      realificationLieHom (liePiEval (some j)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolBasisIndependence
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ L) (ν : κ → ℕ)
  (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (w : σ → ℕ)

theorem realPolynomialSymbolMap_basis_independent
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hF w p = F.realPolynomialSymbolMap c ν hC w p := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  change F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x) =
    F.realSymbolOfPolynomial c ν hC w (F.realAdaptedPolynomialMap w x)
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap,
    F.realSymbolOfPolynomial_realAdaptedPolynomialMap]

theorem realPolynomialSymbolHom_basis_independent
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF w g = F.realPolynomialSymbolHom c ν hC w g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realPolynomialSymbolMap_basis_independent b ω hF c ν hC w g.coord

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialGroupMapChart
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial _root_.MvPolynomial

variable {σ τ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartHom

theorem realPolynomialGroupMap_weightedAdaptedRealChartHom
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialGroupMap G φ hφ v (F.weightedAdaptedRealChartHom w v β hβ g) =
      G.weightedAdaptedRealChartHom w v β hβ (F.realPolynomialGroupMap G φ hφ w g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [realPolynomialGroupMap_log, weightedAdaptedRealChartHom_coord]
  exact (realChartSubstitute_map β (realificationLieHom φ).toLinearMap _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FrozenMarkedRightOrbitGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_frozenMarkedRightOrbit_grid_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [DecidableEq κ]
        [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
        (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
        (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H : ℕ) (p : ℝ),
        0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
        (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
        ∀ q r : ℕ, 0 < q → 0 < r →
          ((matrixDenominator (LinearMap.toMatrix c b S) * q * r : ℕ) : ℝ) ≤ Real.exp p →
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            matrixDenominator (LinearMap.toMatrix c b S) * q * r ∣ m ∧
            ∀ marked : G.realification.PolynomialOrbit w,
              CoefficientGrid (c.baseChange ℝ) q marked.log →
              ∀ center : F.realification.Group,
                (b.baseChange ℝ).equivFun center.coord ∈ realDenominatorGrid r →
                ∀ x : σ → ℤ,
                  (b.baseChange ℝ).equivFun
                    (F.realification.polynomialOrbitEval w x
                      (F.frozenMarkedRightOrbit G w S hS marked center)).coord ∈
                    realDenominatorGrid m := by
  obtain ⟨C, hC, hclosure⟩ := exists_real_bch_rational_closure s
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ _ t F G b c w S hS H p hp hd hH hb q r hq hr hlp
  have hDq : 0 < matrixDenominator (LinearMap.toMatrix c b S) * q :=
    Nat.mul_pos (matrixDenominator_pos _) hq
  obtain ⟨m, hm, hmp, hlm, hmul, _⟩ :=
    hclosure b H p F.lowerCentralSeries_eq_bot hp hd hH hb
      (matrixDenominator (LinearMap.toMatrix c b S) * q * r)
      (Nat.mul_pos hDq hr) hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro marked hmarked center hcenter x
  rw [← polynomialOrbitRealEval_integer, frozenMarkedRightOrbit_realEval,
    polynomialOrbitRealEval_integer]
  apply hmul
  · exact realDenominatorGrid_subset_of_dvd hDq (dvd_mul_right _ _)
      (realified_linear_coordinate_grid c b S q _
        (G.polynomialOrbit_coefficient_grid_value c w q marked hmarked x))
  · exact realDenominatorGrid_subset_of_dvd hr (dvd_mul_left _ _) hcenter

end Erdos3.NilpotentLieFiltration

end

end OAI
end


