-- Prove2me | Definitions.Def_OAIErdos3B168
-- name    : OAIErdos3B168
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T06:16:50.673624+00:00
-- url     : https://prove2.me/theorems/51e25e81-14ad-4fdc-b4f4-3248ed497967
-- title:
--   OpenAI Erdős-3 split, definitions bundle 169 of 185
-- statement:
--   Definitions bundle 169 of 185 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B167`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 169 available.
--
--   Modules: `OAI.Erdos3.AnchoredChildResidueComparison`, `OAI.Erdos3.BooleanCubeKernel.exists_fixed_kernel_euclidean_ambient_density_multiple`, `OAI.Erdos3.BooleanCubeKernel.exists_physical_jet_covered_l1_perturbation`, `OAI.Erdos3.BooleanCubeKernel.exists_physical_jet_covered_l1_sampling`, `OAI.Erdos3.BooleanCubeKernel.physicalSpatialAnalyticContinuous`, `OAI.Erdos3.BooleanCubeKernel.physicalSpatialAnalyticContinuous_bounds`, `OAI.Erdos3.BooleanCubeKernel.physicalSpatialAnalytic_normalized`, `OAI.Erdos3.FixedAffineEpochTransition`, `OAI.Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors.chart_middle_log`, `OAI.Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors.fixed_chart_native_conditions`, `OAI.Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors.fixed_chart_residual_eq`, `OAI.Erdos3.NilpotentLieFiltration.HasCommonRefilteredOrbitFactors.freeze`, `OAI.Erdos3.NilpotentLieFiltration.HasCommonRefilteredOrbitFactors.nested_freeze`, `OAI.Erdos3.NilpotentLieFiltration.HasCommonRefilteredOrbitFactors.of_dvd`, `OAI.Erdos3.NilpotentLieFiltration.HasCommonRefilteredOrbitFactors.of_symbol_eq`, `OAI.Erdos3.NilpotentLieFiltration.HasCommonRefilteredOrbitFactors.reindex`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_refiltered_globalMarked_family_reset`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_refiltered_globalMarked_native_reset`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_refiltered_terminal_native_reset`, `OAI.Erdos3.NilpotentLieFiltration.polynomialCoordinateFreezeZeroHom`, `OAI.Erdos3.NilpotentLieFiltration.polynomialCoordinateFreezeZeroHom_coeff_zero`, `OAI.Erdos3.NilpotentLieFiltration.polynomialCoordinateFreezeZeroHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.polynomialCoordinateFreezeZeroHom_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.polynomialCoordinateFreezeZeroHom_zero_constant`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_freeze_zero`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_integerChart`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_freeze_zero`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_reindex`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_frozenChart_independent`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_nested_frozenCoordinate_independent`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_nested_nested_frozenCoordinate`, `OAI.Erdos3.NilpotentLieFiltration.scalarAffineAdaptedHom`, `OAI.Erdos3.NilpotentLieFiltration.scalarAffineOrbitHom`, `OAI.Erdos3.NilpotentLieFiltration.weightedAdaptedRealChartHom_eq_of_fixed_chart`, `OAI.Erdos3.NilpotentLieFiltration.weightedAdaptedRealChartHom_nested_nested_zero`, `OAI.Erdos3.RationalFilteredNilmanifold.FixedAffineResidueDescent`, `OAI.Erdos3.RationalFilteredNilmanifold.FixedResidueDescent`, `OAI.Erdos3.RationalFilteredNilmanifold.HasFixedAffineResidueChild`, `OAI.Erdos3.RetainedAffineResidueEpoch`, `OAI.Erdos3.VectorPolynomial.exists_allocated_ambient_projected_density_multiple`, `OAI.Erdos3.nestedFrozenCoordinate`, `OAI.Erdos3.nestedFrozenCoordinate_eq_freeze_reindex`, `OAI.Erdos3.nestedFrozenCoordinate_support`, `OAI.Erdos3.nestedFrozenCoordinate_top_independent`, `OAI.Erdos3.nestedFrozenCoordinate_zero_comp`, `OAI.Erdos3.nestedFrozenVariableEquiv`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B166

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GlobalMarkedNativeChartResetConditions
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartHom polynomialOrbitRealChart

variable {m s : ℕ} {X τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s)
  (J : Fin m → Type*) [∀ j, Fintype (J j)]
  (Ktag : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)


namespace GlobalMarkedNativeFactors

variable {F J Ktag c}
  {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {W : LieSubalgebra ℚ F.AssociatedGraded}

variable {σ : Type*} {w : σ → ℕ}
  {g : (F.realification.adaptedPolynomialFiltration w).Group}
  {E R : F.RealPolynomialSymbolGroup w}

theorem chart_middle_log
    (A : GlobalMarkedNativeFactors F b ω hF w W g E R)
    (v : τ → ℕ) (γ : σ → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i)) :
    VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      ((F.gradedRefiltration W).polynomialOrbitRealChart w v γ hγ A.markedMiddle).log =
      (F.weightedAdaptedRealChartHom w v γ hγ A.middle).coord.val := by
  rw [polynomialOrbitRealChart_log, F.weightedAdaptedRealChartHom_coord, ← A.middle_log]
  exact (realChartSubstitute_map γ
    (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl).toLinearMap A.markedMiddle.log).symm

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute realPolynomialSymbolHom polynomialOrbitRealChart

variable {α σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem weightedAdaptedRealChartHom_eq_of_fixed_chart
    (w : α → ℕ) (v : σ → ℕ) (β : α → MvPolynomial α ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
    (γ : α → MvPolynomial σ ℝ) (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
    (hfixed : ∀ t : σ → ℝ,
      (fun i => MvPolynomial.eval (fun j => MvPolynomial.eval t (γ j)) (β i)) =
        (fun i => MvPolynomial.eval t (γ i)))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w v γ hγ
      (F.weightedAdaptedRealChartHom w w β hβ g) =
      F.weightedAdaptedRealChartHom w v γ hγ g := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [F.weightedAdaptedRealChartHom_coord]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  rw [map_sub, eval₂_realChartSubstitute, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute, hfixed t, sub_self]

namespace GlobalMarkedNativeFactors

variable {F} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {w : α → ℕ} {v : σ → ℕ}
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {β : α → MvPolynomial α ℝ}
  {hβ : ∀ i, β i ∈ weightedSupportLE w (w i)}
  {g : (F.realification.adaptedPolynomialFiltration w).Group}
  {E R : F.RealPolynomialSymbolGroup w}
  (A : GlobalMarkedNativeFactors F b ω hF w W
    (F.weightedAdaptedRealChartHom w w β hβ g) E R)
  (γ : α → MvPolynomial σ ℝ) (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
  (hfixed : ∀ t : σ → ℝ,
    (fun i => MvPolynomial.eval (fun j => MvPolynomial.eval t (γ j)) (β i)) =
      (fun i => MvPolynomial.eval t (γ i)))

include hfixed

theorem fixed_chart_residual_eq :
    (F.weightedAdaptedRealChartHom w v γ hγ A.left)⁻¹ *
      F.weightedAdaptedRealChartHom w v γ hγ g *
      (F.weightedAdaptedRealChartHom w v γ hγ A.right)⁻¹ =
        F.weightedAdaptedRealChartHom w v γ hγ A.middle := by
  have hprod : F.weightedAdaptedRealChartHom w v γ hγ A.left *
      F.weightedAdaptedRealChartHom w v γ hγ A.middle *
      F.weightedAdaptedRealChartHom w v γ hγ A.right =
        F.weightedAdaptedRealChartHom w v γ hγ g := by
    rw [← map_mul, ← map_mul, A.product,
      F.weightedAdaptedRealChartHom_eq_of_fixed_chart w v β hβ γ hγ hfixed]
  rw [← hprod]
  group

theorem fixed_chart_native_conditions :
    let residual := (F.weightedAdaptedRealChartHom w v γ hγ A.left)⁻¹ *
      F.weightedAdaptedRealChartHom w v γ hγ g *
      (F.weightedAdaptedRealChartHom w v γ hγ A.right)⁻¹
    (F.realPolynomialSymbolHom b ω hF v residual).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v W) ∧
    coefficients (residual.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1 := by
  dsimp only
  rw [A.fixed_chart_residual_eq γ hγ hfixed]
  exact F.native_refiltered_symbol_conditions W b ω hF v
    ((F.gradedRefiltration W).polynomialOrbitRealChart w v γ hγ A.markedMiddle)
    (F.weightedAdaptedRealChartHom w v γ hγ A.middle) (A.chart_middle_log v γ hγ)

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinateFreezeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

theorem polynomialRationalGrid_integerChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, MvPolynomial.map (Int.castRingHom ℝ) (β i) ∈ weightedSupportLE v (w i))
    (q : ℕ) (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) :
    F.PolynomialRationalGrid b v q
      (F.weightedAdaptedRealChartHom w v
        (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)) hβ g) := by
  classical
  obtain ⟨z, hz⟩ := hg
  have hc : CoefficientGrid (b.baseChange ℝ) q g.coord.val := by
    intro α
    exact ⟨fun i => z (α, i), funext (fun i => congrFun hz (α, i))⟩
  have ho : CoefficientGrid (b.baseChange ℝ) q
      (F.weightedAdaptedRealChartHom w v
        (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)) hβ g).coord.val := by
    rw [F.weightedAdaptedRealChartHom_coord]
    exact CoefficientGrid.realChartSubstitute_integral (b.baseChange ℝ) q g.coord.val hc
      (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i))
      (fun i => realPolynomialCoefficientGrid_intCast (β i))
  choose a ha using ho
  exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

noncomputable def polynomialCoordinateFreezeZeroHom (keep : σ → Prop) :
    (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group →*
      (F.realification.adaptedPolynomialFiltration (fun _ : {i // keep i} => 1)).Group :=
  F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : {i // keep i} => 1)
    (frozenCoordinate keep (0 : {i // ¬keep i} → ℝ))
    (frozenCoordinate_support keep 0)

@[simp] theorem polynomialCoordinateFreezeZeroHom_coord (keep : σ → Prop)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
        VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute (frozenCoordinate keep 0)
        (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  exact F.weightedAdaptedRealChartHom_coord _ _ _ _ g

theorem polynomialCoordinateFreezeZeroHom_coordinate (keep : σ → Prop) (b : Basis ι ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (α : {i // keep i} →₀ ℕ) (i : ι) :
    (b.baseChange ℝ).repr
        (coefficients ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
          VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) α) i =
      (b.baseChange ℝ).repr
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
          (α.mapDomain Subtype.val)) i := by
  rw [F.polynomialCoordinateFreezeZeroHom_coord]
  exact coordinate_coeff_realChartSubstitute_freeze_zero keep (b.baseChange ℝ) _ α i

theorem polynomialSlowBound_freeze_zero (keep : σ → Prop) (b : Basis ι ℚ L)
    (T : σ → ℝ) {M : ℝ}
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialSlowBound b (fun _ : σ => 1) T M g) :
    F.PolynomialSlowBound b (fun _ : {i // keep i} => 1)
      (fun i => T i.val) M (F.polynomialCoordinateFreezeZeroHom keep g) := by
  intro α i
  rw [F.polynomialCoordinateFreezeZeroHom_coordinate]
  have hscale : monomialScale T (α.mapDomain Subtype.val) =
      monomialScale (fun i : {i // keep i} => T i.val) α :=
    Finsupp.prod_mapDomain_index_inj Subtype.val_injective
  simpa only [hscale] using hg (α.mapDomain Subtype.val) i

theorem polynomialCoordinateFreezeZeroHom_coeff_zero (keep : σ → Prop) (b : Basis ι ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    coefficients ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
        VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) 0 =
      coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  simpa only [Finsupp.mapDomain_zero] using
    F.polynomialCoordinateFreezeZeroHom_coordinate keep b g 0 i

theorem polynomialCoordinateFreezeZeroHom_zero_constant (keep : σ → Prop) (b : Basis ι ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0) :
    coefficients ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
        VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  rw [F.polynomialCoordinateFreezeZeroHom_coeff_zero keep b g, hg]

theorem polynomialRationalGrid_freeze_zero (keep : σ → Prop) (b : Basis ι ℚ L)
    (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialRationalGrid b (fun _ : σ => 1) q g) :
    F.PolynomialRationalGrid b (fun _ : {i // keep i} => 1) q
      (F.polynomialCoordinateFreezeZeroHom keep g) := by
  classical
  have hcast : (fun i => MvPolynomial.map (Int.castRingHom ℝ)
      (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i)) =
      frozenCoordinate keep (0 : {i // ¬keep i} → ℝ) := by
    funext i
    by_cases hi : keep i <;> simp [frozenCoordinate, hi]
  have hsupport : ∀ i, MvPolynomial.map (Int.castRingHom ℝ)
      (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i) ∈
        weightedSupportLE (fun _ : {i // keep i} => 1) 1 := by
    intro i
    rw [congrFun hcast i]
    exact frozenCoordinate_support keep 0 i
  simpa only [polynomialCoordinateFreezeZeroHom, hcast] using
    F.polynomialRationalGrid_integerChart b (fun _ : σ => 1)
      (fun _ : {i // keep i} => 1) (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ))
      hsupport q g hg

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonRefilteredGlobalMarkedFamilyReset
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

theorem exists_common_refiltered_terminal_native_reset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
      Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (H l : ℕ) (pMap pNative : ℝ), 1 ≤ H → 0 < l → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → (l : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (Fintype.card ι : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card σ : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) H) →
    ∃ mMap m : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l ∣ mMap ∧ 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ m ∧
    ∀ (side : σ → ℝ), (∀ i, Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ side i) →
    ∀ (q : ℝ), Real.exp q ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ a) →
    ∀ X EF RF : (G.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      G.PolynomialSlowBound c (fun _ : σ => 1) side (Real.exp ((pNative + 2) ^ a)) EF →
      G.PolynomialRationalGrid c (fun _ : σ => 1) mMap RF →
      (G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1) (EF⁻¹ * X * RF⁻¹)).coord ∈
        realificationLieSubalgebra (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))) →
      coefficients ((EF⁻¹ * X * RF⁻¹).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
        G.realGradedRefiltrationLayer (W.map (F.associatedGradedMap G φ hφ)) 1 →
    ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g = X →
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (native : (F.gradedRefiltration W).realification.PolynomialOrbit (fun _ : σ => 1)),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) e = EF ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) r = RF ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) middle = EF⁻¹ * X * RF⁻¹ ∧
      F.PolynomialSlowBound b (fun _ : σ => 1) side
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative)) e ∧
      F.PolynomialRationalGrid b (fun _ : σ => 1) m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        native.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval (fun _ : σ => 1) t native) =
          F.adaptedPolynomialRealValueHom (fun _ : σ => 1) t middle := by
  obtain ⟨Ccompare, hCcompare, hcompare⟩ := exists_common_refiltered_terminal_discrepancies s a
  obtain ⟨Cf, Cnative, hCf, hCnative, hnative⟩ :=
    exists_controlled_prescribed_marked_native_factorizations s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ χ L M _ _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c ν hG hsurj
    bk W v hW hvspan vg hvgspan _ _ H l pMap pNative hH hl hpMap hpNative
    hsrc htgt hHmap hlmap hmabsorb hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  obtain ⟨mMap, hmMap, hmMapBound, hlmMap, hdiscrepancy⟩ :=
    hcompare (χ := χ) F G b ω hF c ν hG φ hφ H l pMap hH hl hpMap hentries hsrc htgt hHmap hlmap
  obtain ⟨m, hm, hmp, hmMapm, hreset⟩ := hnative F G φ hφ b ω hF c ν hG
    (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) hsurj bk W v hW hvspan H mMap pNative
    hH hmMap hpNative hι hκ hξ hμ hσ hHp (hmMapBound.trans hmabsorb)
    hb hc hkernel hentries hv
  refine ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, ?_⟩
  intro side hside q hq hmapslow X EF RF hEF hRF hterminal hconstant g hg hfactor
  have hsidePos : ∀ i, 0 < side i := fun i => (Real.exp_pos _).trans_le (hside i)
  obtain ⟨E, P, R, hprod, hP, hE, hR, hdiff⟩ :=
    hdiscrepancy H pNative hH hpNative hκ hσ hχ hHp hmabsorb hc
      side hside q hmapslow W vg hvgspan hvg g hfactor
  have hterminal' :
      ((G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1) EF)⁻¹ *
        G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
          (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) *
        (G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1) RF)⁻¹).coord ∈
        realificationLieSubalgebra (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))) := by
    simpa only [map_mul, map_inv, hg] using hterminal
  obtain ⟨hleft, hright⟩ := hdiff _ _ hterminal'
    (G.polynomialSlowBound_symbol c ν hG (fun _ : σ => 1) side _ EF hEF)
    (G.polynomialRationalGrid_symbol c ν hG (fun _ : σ => 1) mMap RF hRF)
  exact hreset side hsidePos X EF RF hEF hRF hconstant g hg E P R hprod hP
    (F.symbolSlowBound_mono b ω hF (fun _ : σ => 1) side hsidePos hq E hE)
    (F.symbolRationalGrid_mono b ω hF (fun _ : σ => 1) hl hlmMap R hR) hleft hright

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom symbolPointwiseSubalgebra realificationLieSubalgebra

theorem exists_common_refiltered_globalMarked_native_reset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
      Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (H l : ℕ) (pMap pNative : ℝ), 1 ≤ H → 0 < l → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → (l : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (Fintype.card ι : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card σ : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) H) →
    ∃ mMap m : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l ∣ mMap ∧ 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ m ∧
    ∀ (side : σ → ℝ), (∀ i, Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ side i) →
    ∀ (q : ℝ), Real.exp q ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ a) →
    ∀ {α : Type*} (w : α → ℕ) (β : α → MvPolynomial α ℝ)
      (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
      (marked : (G.realification.adaptedPolynomialFiltration w).Group)
      (E R : G.RealPolynomialSymbolGroup w)
      (A : GlobalMarkedNativeFactors G c ν hG w
        (W.map (F.associatedGradedMap G φ hφ))
        (G.weightedAdaptedRealChartHom w w β hβ marked) E R)
      (γ : α → MvPolynomial σ ℤ)
      (hγ : ∀ i, MvPolynomial.map (Int.castRingHom ℝ) (γ i) ∈
        weightedSupportLE (fun _ : σ => 1) (w i)),
      (∀ t : σ → ℝ,
        (fun i => MvPolynomial.eval
          (fun j => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ j))) (β i)) =
        (fun i => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ i)))) →
      G.PolynomialSlowBound c (fun _ : σ => 1) side (Real.exp ((pNative + 2) ^ a))
        (G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.left) →
      G.PolynomialRationalGrid c w l A.right →
    ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ marked →
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (native : (F.gradedRefiltration W).realification.PolynomialOrbit (fun _ : σ => 1)),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) e =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.left ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) r =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.right ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) middle =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.middle ∧
      F.PolynomialSlowBound b (fun _ : σ => 1) side
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative)) e ∧
      F.PolynomialRationalGrid b (fun _ : σ => 1) m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        native.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval (fun _ : σ => 1) t native) =
          F.adaptedPolynomialRealValueHom (fun _ : σ => 1) t middle := by
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_common_refiltered_terminal_native_reset s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ χ L M _ _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c ν hG hsurj
    bk W v hW hvspan vg hvgspan _ _ H l pMap pNative hH hl hpMap hpNative
    hsrc htgt hHmap hlmap hmabsorb hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  obtain ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, hrun⟩ :=
    hreset F G φ hφ b ω hF c ν hG hsurj bk W v hW hvspan vg hvgspan
      H l pMap pNative hH hl hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
      hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  refine ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, ?_⟩
  intro side hside q hq hmapslow α w β hβ marked E R A γ hγ hfixed hslow hgrid g hg hcommon
  let γR := fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)
  let pull := G.weightedAdaptedRealChartHom w (fun _ : σ => 1) γR hγ
  have hlocalGrid : G.PolynomialRationalGrid c (fun _ : σ => 1) mMap (pull A.right) :=
    G.polynomialRationalGrid_of_dvd c (fun _ : σ => 1) hl hlmMap _
      (G.polynomialRationalGrid_integerChart c w (fun _ : σ => 1) γ hγ l A.right hgrid)
  have hconditions := A.fixed_chart_native_conditions γR hγ hfixed
  have hresidual := A.fixed_chart_residual_eq γR hγ hfixed
  obtain ⟨e, middle, r, native, hprod, he, hr, hmid, heSlow, hrGrid, hlog, hvalues⟩ :=
    hrun side hside q hq hmapslow (pull marked) (pull A.left) (pull A.right)
      hslow hlocalGrid hconditions.1 hconditions.2 g hg hcommon
  exact ⟨e, middle, r, native, hprod, he, hr, hmid.trans hresidual,
    heSlow, hrGrid, hlog, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound

theorem HasCommonRefilteredOrbitFactors.of_dvd
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (side : σ → ℝ) (q : ℝ) {l n : ℕ} (hl : 0 < l) (hln : l ∣ n)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF side q n W g := by
  obtain ⟨e, middle, r, hprod, hfast, he, hr, he0, hr0, hmiddle0⟩ := h
  exact ⟨e, middle, r, hprod, hfast, he,
    F.polynomialRationalGrid_of_dvd b (fun _ : σ => 1) hl hln r hr,
    he0, hr0, hmiddle0⟩

theorem exists_common_refiltered_globalMarked_family_reset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
      Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (H l nFinal : ℕ) (pMap pNative : ℝ),
      1 ≤ H → 0 < l → 0 < nFinal → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → ((l * nFinal : ℕ) : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (Fintype.card ι : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card σ : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) H) →
    ∃ mMap m : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l * nFinal ∣ mMap ∧ 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ m ∧
    ∀ {Ω α : Type*} (w : α → ℕ) (β : α → MvPolynomial α ℝ)
      (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
      (marked : (G.realification.adaptedPolynomialFiltration w).Group)
      (E R : G.RealPolynomialSymbolGroup w)
      (A : GlobalMarkedNativeFactors G c ν hG w
        (W.map (F.associatedGradedMap G φ hφ))
        (G.weightedAdaptedRealChartHom w w β hβ marked) E R),
      G.PolynomialRationalGrid c w nFinal A.right →
    ∀ (side : Ω → σ → ℝ) (q : Ω → ℝ)
      (γ : Ω → α → MvPolynomial σ ℤ)
      (hγ : ∀ z i, MvPolynomial.map (Int.castRingHom ℝ) (γ z i) ∈
        weightedSupportLE (fun _ : σ => 1) (w i)),
      (∀ z i, Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ side z i) →
      (∀ z, Real.exp (q z) ≤ Real.exp ((pNative + 2) ^ a)) →
      (∀ z, Real.exp ((pMap + 2) ^ 3 + q z) ≤ Real.exp ((pNative + 2) ^ a)) →
      (∀ z, ∀ t : σ → ℝ,
        (fun i => MvPolynomial.eval
          (fun j => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ z j))) (β i)) =
        (fun i => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ z i)))) →
      (∀ z, G.PolynomialSlowBound c (fun _ : σ => 1) (side z) (Real.exp ((pNative + 2) ^ a))
        (G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.left)) →
    ∀ g : Ω → (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ z, F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (g z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) marked) →
      (∀ z, F.HasCommonRefilteredOrbitFactors b ω hF (side z) (q z) l W (g z)) →
    ∃ (e middle r : Ω → (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (native : Ω → (F.gradedRefiltration W).realification.PolynomialOrbit (fun _ : σ => 1)),
      ∀ z,
      e z * middle z * r z = g z ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (e z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.left ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (r z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.right ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (middle z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.middle ∧
      F.PolynomialSlowBound b (fun _ : σ => 1) (side z)
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative)) (e z) ∧
      F.PolynomialRationalGrid b (fun _ : σ => 1) m (r z) ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        (native z).log = ((middle z).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval (fun _ : σ => 1) t (native z)) =
          F.adaptedPolynomialRealValueHom (fun _ : σ => 1) t (middle z) := by
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_common_refiltered_globalMarked_native_reset s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ χ L M _ _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c ν hG hsurj
    bk W v hW hvspan vg hvgspan _ _ H l nFinal pMap pNative hH hl hnFinal hpMap hpNative
    hsrc htgt hHmap hlmap hmabsorb hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  have hwide : 0 < l * nFinal := Nat.mul_pos hl hnFinal
  obtain ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, hrun⟩ :=
    hreset F G φ hφ b ω hF c ν hG hsurj bk W v hW hvspan vg hvgspan
      H (l * nFinal) pMap pNative hH hwide hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
      hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  refine ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, ?_⟩
  intro Ω α w β hβ marked E R A hgrid side q γ hγ hside hq hmapslow hfixed hslow g hg hcommon
  have hglobalGrid : G.PolynomialRationalGrid c w (l * nFinal) A.right :=
    G.polynomialRationalGrid_of_dvd c w hnFinal (dvd_mul_left nFinal l) A.right hgrid
  have hfamily (z : Ω) := hrun (side z) (hside z) (q z) (hq z) (hmapslow z)
    w β hβ marked E R A (γ z) (hγ z) (hfixed z) (hslow z) hglobalGrid (g z) (hg z)
    (HasCommonRefilteredOrbitFactors.of_dvd F b ω hF (side z) (q z) hl
      (dvd_mul_right l nFinal) W (g z) (hcommon z))
  classical
  choose e middle r native hproperties using hfamily
  exact ⟨e, middle, r, native, hproperties⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

noncomputable def scalarAffineAdaptedHom {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ) :
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group →*
      (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
  (F.polynomialOrbitCoordinates (fun _ => 1)).toMonoidHom.comp
    ((F.polynomialOrbitSubstitute (scalarAffinePolynomial r h) (scalarAffinePolynomial_support r h)).comp
      (F.polynomialOrbitCoordinates (fun _ => 1)).symm.toMonoidHom)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct BigOperators

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped TensorProduct

namespace NilpotentLieFiltration

noncomputable def scalarAffineOrbitHom {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ) :
    F.PolynomialOrbit (fun _ : σ => 1) →* F.PolynomialOrbit (fun _ : σ => 1) :=
  F.polynomialOrbitSubstitute (scalarAffinePolynomial r h) (scalarAffinePolynomial_support r h)

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

end RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3

namespace NilpotentLieFiltration

end NilpotentLieFiltration

namespace NilpotentLieFiltration

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def FixedResidueDescent {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (V : RationalFilteredNilmanifold K t e) (w : σ → ℕ)
    (b : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (child : V.filtration.realification.PolynomialOrbit w)
    (p : ℝ) (q P : ℕ) (hP : 0 < P) (C a : ℕ) (cost : ℝ) : Prop :=
  ∀ S : D.Niltest w, S.ComplexityLE p → S.UnitIntervalValued →
    (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W s →
      ∀ x, S.observable (z • x) = S.observable x) →
    ∀ (E R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
      (κ : D.RealGroup), κ ∈ D.realLattice →
      E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
        ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
      D.filtration.PolynomialRationalGrid D.basis w q R →
      ∀ A : σ → ℝ, (∀ i, 0 < A i) →
        D.filtration.PolynomialSlowBound D.basis w A (Real.exp ((p + 2) ^ a)) E →
        ∀ (M : ℕ) (hM : 0 < M) (lo : σ → ℤ) (N H : σ → ℕ)
          (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (u v : σ → ℤ) (J : σ → ℕ),
          (∀ i, 0 < J i) → ∀ (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]),
          (∀ i, (M * (M * P)).Coprime (J i)) →
          ∀ (δ ε : ℝ), 0 ≤ δ → ε < 1 / 2 →
          (∀ i, 2 * (H i : ℝ) ≤ (M : ℝ) * A i * δ) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (H i : ℝ)) ≤ ε →
          let Q := comparableBoxPartitions N H hH hHN
          let c₀ := baseAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P)
            (fun _ => Nat.mul_pos hM hP) u
          let c₁ := refinedAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P) J
            (fun _ => Nat.mul_pos hM hP) u v hv
          let F : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u → ℂ :=
            residueBoxStrideValue S.eval u M
          let G : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v → ℂ :=
            residueBoxStrideValue S.eval u M
          ∃ k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * P) u,
            0 < (partitionCell c₀ k).card ∧ 0 < (partitionCell c₁ k).card ∧
            ∃ U : V.Niltest w, U.orbit = child ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
              ‖(𝔼 x, F x) - (𝔼 x, G x)‖ - 8 * ε - 2 * (Real.exp ((p + 2) ^ C) * δ) ≤
                ‖(𝔼 x ∈ partitionCell c₀ k, residueBoxStrideValue U.eval u M x) -
                  (𝔼 x ∈ partitionCell c₁ k, residueBoxStrideValue U.eval u M x)‖

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

noncomputable def FixedAffineResidueDescent {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (V : RationalFilteredNilmanifold K t e)
    (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (p : ℝ) (q P : ℕ) (hP : 0 < P) (C a : ℕ) (cost : ℝ) : Prop :=
  ∀ (scale : ℤ) (shift : σ → ℤ),
    FixedResidueDescent D W V (fun _ : σ => 1)
      (D.filtration.realification.scalarAffineAdaptedHom (scale : ℚ) (fun i => (shift i : ℚ)) b)
      (V.filtration.realification.scalarAffineOrbitHom (scale : ℚ) (fun i => (shift i : ℚ)) child)
      p q P hP C a cost

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedAnchoredComparison
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def AnchoredChildResidueComparison {σ K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing K] [LieAlgebra ℚ K] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (cost η δ : ℝ) (lo : σ → ℤ) (N : σ → ℕ) (M P : ℕ) (u v : σ → ℤ) (J : σ → ℕ) : Prop :=
  let Q := Nat.lcm M (M * P)
  ∃ (lo' : σ → ℤ) (N' : σ → ℕ) (w z : σ → ℤ) (U : V.Niltest (fun _ : σ => 1)),
    (∀ i, lo i ≤ lo' i ∧ lo' i + N' i ≤ lo i + N i) ∧
    (∀ i, 0 < N' i) ∧
    (∀ i, δ * (N i : ℝ) / 8 ≤ (N' i : ℝ) ∧ (N' i : ℝ) ≤ δ * (N i : ℝ) / 2) ∧
    (∀ i, lo' i ≤ w i ∧ w i < lo' i + N' i) ∧
    (∀ i, lo' i ≤ z i ∧ z i < lo' i + N' i) ∧
    (∀ i, w i ≡ u i [ZMOD (M : ℤ)]) ∧
    (∀ i, z i ≡ v i [ZMOD (M * J i : ℕ)]) ∧
    (∀ i, z i ≡ w i [ZMOD (Q : ℤ)]) ∧
    Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun _ => (Q : ℤ)) w) ∧
    Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun i => (Q * J i : ℕ)) z) ∧
    U.orbit = V.filtration.realification.scalarAffineOrbitHom (Q / M : ℕ)
      (fun i => (commonStrideIndex u M w i : ℚ)) child ∧
    U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
    η ≤ ‖residuePairMean U.eval lo' N' Q w z J false - residuePairMean U.eval lo' N' Q w z J true‖

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

theorem realPolynomialSymbolHom_frozenChart_independent
    (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (keep : τ → Prop) (fixed fixed' : {i // ¬keep i} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (fun i => freezePolynomial keep fixed (β i))
        (fun i => freezePolynomial_support keep fixed (hβ i)) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (fun i => freezePolynomial keep fixed' (β i))
        (fun i => freezePolynomial_support keep fixed' (hβ i)) g) := by
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart,
    F.realPolynomialSymbolHom_weightedAdaptedRealChart]
  have htop : (fun i => weightedHomogeneousComponent (fun _ : {i // keep i} => 1) (w i)
      (freezePolynomial keep fixed (β i))) =
      (fun i => weightedHomogeneousComponent (fun _ : {i // keep i} => 1) (w i)
        (freezePolynomial keep fixed' (β i))) := by
    funext i
    exact freezePolynomial_top_independent keep fixed fixed'
      ((mem_weightedSupportLE_one_iff _ _).mp (hβ i))
  congr 1
  congr 1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {σ R : Type*} [CommRing R]

noncomputable def nestedFrozenCoordinate
    (keepLong keepLater : σ → Prop)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → R)
    (i : {i // keepLong i}) : MvPolynomial {i // keepLater i} R :=
  if hi : keepLater i.val then X ⟨i.val, hi⟩ else C (fixed ⟨i, hi⟩)

theorem nestedFrozenCoordinate_support
    (keepLong keepLater : σ → Prop)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → R)
    (i : {i // keepLong i}) :
    nestedFrozenCoordinate keepLong keepLater fixed i ∈ weightedSupportLE (fun _ : {i : σ // keepLater i} => 1) 1 := by
  by_cases hi : keepLater i.val
  · simp only [nestedFrozenCoordinate, dif_pos hi]
    exact weightedSupportLE_X (R := R) (fun _ : {i : σ // keepLater i} => 1) ⟨i.val, hi⟩
  · simp only [nestedFrozenCoordinate, dif_neg hi]
    exact weightedSupportLE_C (fun _ : {i : σ // keepLater i} => 1) 1 (fixed ⟨i, hi⟩)

def nestedFrozenVariableEquiv
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i) :
    {i // keepLater i} ≃ {i : {i // keepLong i} // keepLater i.val} where
  toFun i := ⟨⟨i.val, hsub i.val i.property⟩, i.property⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nestedFrozenCoordinate_eq_freeze_reindex
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → R) :
    (fun i => aeval
      (fun j => X ((nestedFrozenVariableEquiv keepLong keepLater hsub).symm j))
      (frozenCoordinate (fun i : {i // keepLong i} => keepLater i.val) fixed i)) =
      nestedFrozenCoordinate keepLong keepLater fixed := by
  funext i
  by_cases hi : keepLater i.val <;>
    simp [frozenCoordinate, nestedFrozenCoordinate, nestedFrozenVariableEquiv, hi]

theorem nestedFrozenCoordinate_top_independent
    (keepOriginal keepLater : σ → Prop)
    (fixed fixed' : {i : {i // keepOriginal i} // ¬keepLater i.val} → R)
    (i : {i // keepOriginal i}) :
    weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
      (nestedFrozenCoordinate keepOriginal keepLater fixed i) =
    weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
      (nestedFrozenCoordinate keepOriginal keepLater fixed' i) := by
  by_cases hi : keepLater i.val
  · simp only [nestedFrozenCoordinate, dif_pos hi]
  · simp only [nestedFrozenCoordinate, dif_neg hi]
    rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := R) _ _),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := R) _ _)]
    norm_num

theorem nestedFrozenCoordinate_zero_comp
    (keepOriginal keepLong keepLater : σ → Prop)
    (hsub : ∀ i, keepLater i → keepLong i) :
    (fun i => aeval
      (nestedFrozenCoordinate keepLong keepLater
        (0 : {i : {i // keepLong i} // ¬keepLater i.val} → R))
      (nestedFrozenCoordinate keepOriginal keepLong
        (0 : {i : {i // keepOriginal i} // ¬keepLong i.val} → R) i)) =
    nestedFrozenCoordinate keepOriginal keepLater
      (0 : {i : {i // keepOriginal i} // ¬keepLater i.val} → R) := by
  funext i
  by_cases hlater : keepLater i.val
  · have hlong := hsub i.val hlater
    simp [nestedFrozenCoordinate, hlater, hlong]
  · by_cases hlong : keepLong i.val <;>
      simp [nestedFrozenCoordinate, hlater, hlong]

namespace NilpotentLieFiltration

open Module VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

theorem weightedAdaptedRealChartHom_nested_nested_zero
    (keepOriginal keepLong keepLater : σ → Prop)
    (hsub : ∀ i, keepLater i → keepLong i)
    (g : (F.realification.adaptedPolynomialFiltration
      (fun _ : {i // keepOriginal i} => 1)).Group) :
    F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
      (fun _ : {i // keepLater i} => 1)
      (nestedFrozenCoordinate keepOriginal keepLater 0)
      (nestedFrozenCoordinate_support keepOriginal keepLater 0) g =
    F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
      (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater 0)
      (nestedFrozenCoordinate_support keepLong keepLater 0)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLong i} => 1) (nestedFrozenCoordinate keepOriginal keepLong 0)
        (nestedFrozenCoordinate_support keepOriginal keepLong 0) g) := by
  have hcomp := F.weightedAdaptedRealChartHom_comp
    (fun _ : {i // keepOriginal i} => 1) (fun _ : {i // keepLong i} => 1)
    (fun _ : {i // keepLater i} => 1)
    (nestedFrozenCoordinate keepOriginal keepLong 0)
    (nestedFrozenCoordinate keepLong keepLater 0)
    (nestedFrozenCoordinate_support keepOriginal keepLong 0)
    (nestedFrozenCoordinate_support keepLong keepLater 0)
    (weightedRealChart_comp_support _ _ _ _ _
      (nestedFrozenCoordinate_support keepOriginal keepLong 0)
      (nestedFrozenCoordinate_support keepLong keepLater 0)) g
  simpa only [nestedFrozenCoordinate_zero_comp keepOriginal keepLong keepLater hsub] using hcomp

theorem realPolynomialSymbolHom_nested_frozenCoordinate_independent
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (keepOriginal keepLater : σ → Prop)
    (fixed fixed' : {i : {i // keepOriginal i} // ¬keepLater i.val} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fun _ : {i // keepOriginal i} => 1)).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLater i} => 1)
        (nestedFrozenCoordinate keepOriginal keepLater fixed)
        (nestedFrozenCoordinate_support keepOriginal keepLater fixed) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLater i} => 1)
        (nestedFrozenCoordinate keepOriginal keepLater fixed')
        (nestedFrozenCoordinate_support keepOriginal keepLater fixed') g) := by
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart,
    F.realPolynomialSymbolHom_weightedAdaptedRealChart]
  have htop :
      (fun i => weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
        (nestedFrozenCoordinate keepOriginal keepLater fixed i)) =
      (fun i => weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
        (nestedFrozenCoordinate keepOriginal keepLater fixed' i)) := by
    funext i
    exact nestedFrozenCoordinate_top_independent keepOriginal keepLater fixed fixed' i
  congr 1
  congr 1

theorem realPolynomialSymbolHom_nested_nested_frozenCoordinate
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (keepOriginal keepLong keepLater : σ → Prop)
    (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i : {i // keepOriginal i} // ¬keepLater i.val} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fun _ : {i // keepOriginal i} => 1)).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLater i} => 1)
        (nestedFrozenCoordinate keepOriginal keepLater fixed)
        (nestedFrozenCoordinate_support keepOriginal keepLater fixed) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
        (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater 0)
        (nestedFrozenCoordinate_support keepLong keepLater 0)
        (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
          (fun _ : {i // keepLong i} => 1) (nestedFrozenCoordinate keepOriginal keepLong 0)
          (nestedFrozenCoordinate_support keepOriginal keepLong 0) g)) := by
  rw [← F.weightedAdaptedRealChartHom_nested_nested_zero keepOriginal keepLong keepLater hsub g]
  exact F.realPolynomialSymbolHom_nested_frozenCoordinate_independent
    b ω hF keepOriginal keepLater fixed 0 g

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

theorem HasCommonRefilteredOrbitFactors.freeze
    (keep : σ → Prop) [DecidablePred keep]
    (fixed : {i // ¬keep i} → ℝ) (side : σ → ℝ) (q : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF (fun i : {i // keep i} => side i.val)
      q l W (F.weightedAdaptedRealChartHom (fun _ : σ => 1)
        (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed)
        (frozenCoordinate_support keep fixed) g) := by
  classical
  obtain ⟨left, middle, right, hprod, hmid, hleft, hright, hleft0, hright0, _⟩ := h
  let pull := F.polynomialCoordinateFreezeZeroHom keep
  let actual := F.weightedAdaptedRealChartHom (fun _ : σ => 1)
    (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed)
    (frozenCoordinate_support keep fixed) g
  let adjusted := (pull left)⁻¹ * actual * (pull right)⁻¹
  let symbol := F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
  have hfiber : symbol actual = symbol (pull g) := by
    symm
    simpa only [symbol, actual, pull, polynomialCoordinateFreezeZeroHom,
      freezePolynomial, aeval_X] using
      F.realPolynomialSymbolHom_frozenChart_independent b ω hF (fun _ : σ => 1)
        (fun i => X i) (fun i => weightedSupportLE_X (R := ℝ) (fun _ : σ => 1) i)
        keep 0 fixed g
  have hcancel : (pull left)⁻¹ * pull g * (pull right)⁻¹ = pull middle := by
    rw [← hprod, map_mul, map_mul]
    group
  have hadjusted : symbol adjusted = symbol (pull middle) := by
    calc
      _ = symbol ((pull left)⁻¹ * pull g * (pull right)⁻¹) := by
        simp only [adjusted, map_mul, map_inv, hfiber]
      _ = _ := congrArg symbol hcancel
  have hactual : pull left * adjusted * pull right = actual := by
    dsimp only [adjusted]
    group
  have he0 := F.polynomialCoordinateFreezeZeroHom_zero_constant keep b left hleft0
  have hr0 := F.polynomialCoordinateFreezeZeroHom_zero_constant keep b right hright0
  refine ⟨pull left, adjusted, pull right, hactual, ?_,
    F.polynomialSlowBound_freeze_zero keep b side left hleft,
    F.polynomialRationalGrid_freeze_zero keep b l right hright, he0, hr0, ?_⟩
  · change ∀ t, VectorPolynomial.eval₂ t (F.realGradedSymbolPolynomial b ω hF
      (fun _ : {i // keep i} => 1) (symbol adjusted).coord) ∈ _
    rw [hadjusted]
    apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : {i // keep i} => 1) W _).mp
    have hsymbol := F.realPolynomialSymbolHom_homogeneousChart b ω hF
      (fun _ : σ => 1) (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
      (frozenCoordinate_zero_homogeneous keep) middle (pull middle)
      (F.polynomialCoordinateFreezeZeroHom_coord keep middle)
    change (F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (pull middle)).coord ∈ _
    rw [hsymbol]
    apply F.realSymbolHomogeneousPullback_mem_pointwise b ω hF
    exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : σ => 1) W _).mpr hmid
  · exact F.realification.polynomial_factor_middle_constant
      (fun _ : {i // keep i} => 1) actual (pull left) adjusted (pull right)
      hactual he0 hr0

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] realPolynomialSymbolHom

theorem HasCommonRefilteredOrbitFactors.of_symbol_eq
    (side : σ → ℝ) (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g actual : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g)
    (hsymbol : F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1) actual =
      F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1) g) :
    F.HasCommonRefilteredOrbitFactors b ω hF side q l W actual := by
  obtain ⟨left, middle, right, hprod, hmid, hleft, hright, hleft0, hright0, _⟩ := h
  let adjusted := left⁻¹ * actual * right⁻¹
  let symbol := F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1)
  have hcancel : left⁻¹ * g * right⁻¹ = middle := by
    rw [← hprod]
    group
  have hadjusted : symbol adjusted = symbol middle := by
    calc
      _ = symbol (left⁻¹ * g * right⁻¹) := by
        simp only [adjusted, map_mul, map_inv, show symbol actual = symbol g from hsymbol]
      _ = _ := congrArg symbol hcancel
  have hactual : left * adjusted * right = actual := by
    dsimp only [adjusted]
    group
  refine ⟨left, adjusted, right, hactual, ?_, hleft, hright, hleft0, hright0, ?_⟩
  · change ∀ t, eval₂ t (F.realGradedSymbolPolynomial b ω hF
      (fun _ : σ => 1) (symbol adjusted).coord) ∈ _
    rw [hadjusted]
    exact hmid
  · exact F.realification.polynomial_factor_middle_constant
      (fun _ : σ => 1) actual left adjusted right hactual hleft0 hright0

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorsNestedFreeze
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute realPolynomialSymbolHom

theorem polynomialSlowBound_reindex
    (e : τ ≃ σ) (side : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialSlowBound b (fun _ : σ => 1) side M g) :
    F.PolynomialSlowBound b (fun _ : τ => 1) (fun i => side (e i)) M
      (F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : τ => 1)
        (fun i => MvPolynomial.X (e.symm i))
        (fun i => weightedSupportLE_X (fun _ : τ => 1) (e.symm i)) g) := by
  intro α i
  rw [F.weightedAdaptedRealChartHom_coord,
    coefficients_realChartSubstitute_reindex]
  have hscale : monomialScale side (α.mapDomain e) =
      monomialScale (fun i => side (e i)) α :=
    Finsupp.prod_mapDomain_index_inj e.injective
  simpa only [hscale] using hg (α.mapDomain e) i

theorem HasCommonRefilteredOrbitFactors.reindex [Fintype σ] [Fintype τ] [Fintype ι]
    (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (e : τ ≃ σ) (side : σ → ℝ) (q : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF (fun i => side (e i)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : τ => 1)
        (fun i => MvPolynomial.X (e.symm i))
        (fun i => weightedSupportLE_X (fun _ : τ => 1) (e.symm i)) g) := by
  classical
  obtain ⟨left, middle, right, hprod, hmid, hleft, hright, hleft0, hright0, hmiddle0⟩ := h
  let pull := F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : τ => 1)
    (fun i => MvPolynomial.X (e.symm i))
    (fun i => weightedSupportLE_X (fun _ : τ => 1) (e.symm i))
  have hzero (a : (F.realification.adaptedPolynomialFiltration
      (fun _ : σ => 1)).Group) :
      coefficients ((pull a).coord : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) 0 =
        coefficients (a.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
    dsimp only [pull]
    rw [F.weightedAdaptedRealChartHom_coord, coefficients_realChartSubstitute_reindex]
    simp only [Finsupp.mapDomain_zero]
  refine ⟨pull left, pull middle, pull right, ?_, ?_, ?_, ?_,
    (hzero left).trans hleft0, (hzero right).trans hright0, ?_⟩
  · rw [← map_mul, ← map_mul, hprod]
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : τ => 1) W _).mp
    dsimp only [pull]
    rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart]
    apply F.realSymbolHomogeneousPullback_mem_pointwise b ω hF
    exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : σ => 1) W _).mpr hmid
  · exact F.polynomialSlowBound_reindex b e side (Real.exp q) left hleft
  · have hgrid := F.polynomialRationalGrid_integerChart b
      (fun _ : σ => 1) (fun _ : τ => 1)
      (fun i => (MvPolynomial.X (e.symm i) : MvPolynomial τ ℤ))
      (fun i => by simpa only [MvPolynomial.map_X] using
        weightedSupportLE_X (R := ℝ) (fun _ : τ => 1) (e.symm i)) l right hright
    simpa only [MvPolynomial.map_X] using hgrid
  · exact (hzero middle).trans (hmiddle0.trans (hzero g).symm)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom

theorem HasCommonRefilteredOrbitFactors.nested_freeze
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → ℝ)
    (side : σ → ℝ) (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : {i // keepLong i} => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF
      (fun i : {i // keepLong i} => side i.val) q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF
      (fun i : {i // keepLater i} => side i.val) q l W
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
        (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater fixed)
        (nestedFrozenCoordinate_support keepLong keepLater fixed) g) := by
  classical
  let localKeep : {i // keepLong i} → Prop := fun i => keepLater i.val
  let β := frozenCoordinate localKeep fixed
  let e := nestedFrozenVariableEquiv keepLong keepLater hsub
  let γ : {i : {i // keepLong i} // localKeep i} → MvPolynomial {i // keepLater i} ℝ :=
    fun i => X (e.symm i)
  have hβ := frozenCoordinate_support localKeep fixed
  have hγ : ∀ i, γ i ∈ weightedSupportLE (fun _ : {i // keepLater i} => 1) 1 :=
    fun i => weightedSupportLE_X (fun _ : {i // keepLater i} => 1) (e.symm i)
  have hf := HasCommonRefilteredOrbitFactors.freeze F b ω hF localKeep fixed
    (fun i : {i // keepLong i} => side i.val) q l W g h
  have hr := HasCommonRefilteredOrbitFactors.reindex F b ω hF e
    (fun i : {i : {i // keepLong i} // localKeep i} => side i.val.val) q l W
    (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
      (fun _ : {i : {i // keepLong i} // localKeep i} => 1) β hβ g) hf
  have hcomp : (fun i => aeval γ (β i)) = nestedFrozenCoordinate keepLong keepLater fixed :=
    nestedFrozenCoordinate_eq_freeze_reindex keepLong keepLater hsub fixed
  have hcompose := F.weightedAdaptedRealChartHom_comp
    (fun _ : {i // keepLong i} => 1)
    (fun _ : {i : {i // keepLong i} // localKeep i} => 1)
    (fun _ : {i // keepLater i} => 1) β γ hβ hγ
    (weightedRealChart_comp_support _ _ _ β γ hβ hγ) g
  rw [← hcompose] at hr
  simpa only [hcomp, e, nestedFrozenVariableEquiv, Equiv.coe_fn_mk] using hr

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalRowsCoveredL1Sampling
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_physical_jet_covered_l1_sampling (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Q)
    (_hLQ : (((Lf + Lg) * ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) -
      g (coveredJetAmbientTorus U 1 y)‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))) -
          g (coveredJetAmbientTorus U 1
            (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z)))‖) ≤ E + 2 * η + ε := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_l1_sampling m
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows P hP hn hd U _ _ _ μ _ _ ν _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP E hmass
  let jet := coefficientAmbientRowsJet (J := J) rows
  let Ljet : ℝ≥0 := ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0)
  have hjet : LipschitzWith Ljet jet := coefficientAmbientRowsJet_lipschitz rows
  have hhaar : (∫ x, ‖f (jet (coefficientAmbientTorus U x)) -
      g (jet (coefficientAmbientTorus U x))‖ ∂μ) ≤ E := by
    let error := fun y => ‖f (coveredJetAmbientTorus U 1 y) - g (coveredJetAmbientTorus U 1 y)‖
    let rowJet := euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin dim) (Fin dim) ℤ) rows
    have hperiod : integerScalarLattice (Fin dim) (1 : ℤ) ≤
        (1 : Matrix (Fin dim) (Fin dim) ℤ).mulVecLin.range := by
      intro v _
      exact ⟨v, by simp⟩
    have hp := euclideanCoefficientJetMap_measurePreserving U (fun _ => 0)
      (1 : Matrix (Fin dim) (Fin dim) ℤ) 1 one_ne_zero hperiod rows hinj hrows μ ν
    have he : AEStronglyMeasurable error (Measure.map rowJet μ) := by
      rw [hp.map_eq]
      exact (((hf.continuous.comp (coveredJetAmbientTorus_continuous U 1)).sub
        (hg.continuous.comp (coveredJetAmbientTorus_continuous U 1))).norm).aestronglyMeasurable
    have hi := (integral_map hp.measurable.aemeasurable he).symm
    rw [hp.map_eq] at hi
    simp only [jet, coefficientAmbientRowsJet_eq]
    exact hi.trans_le hmass
  have hLip : (((Lf * Ljet + Lg * Ljet : ℝ≥0) : ℝ)) ≤ Real.exp Q := by
    simpa only [add_mul] using hLQ
  obtain ⟨hZ, he⟩ := hsample hP hn hd U μ p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun z => f (jet z)) (fun z => g (jet z)) (Lf * Ljet) (Lg * Ljet) Cf Cg
    (hf.comp hjet) (hg.comp hjet) (fun z => hfb _) (fun z => hgb _)
    hη hQ hdim hLip hηQ hfreqP hcoeffP hhaar
  refine ⟨hZ, ?_⟩
  have hid (z : Option (Fin dim) × I → ℤ) :
      jet (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm q
        (fun k j => (z (k,j) : ℝ)))) =
      coveredJetAmbientTorus U 1
        (physicalCubeRowSample U q rows p hm (standardPhysicalCubeOutput z)) :=
    (coefficientAmbientRowsJet_eq rows U _).trans
      (congrArg (coveredJetAmbientTorus U 1) (by
        have he : standardPhysicalCubeFrame (standardPhysicalCubeOutput z) = z := by
          funext t
          rcases t with ⟨k, x⟩
          cases k <;> rfl
        simpa only [he] using
          coefficientCoverSample_physicalRows U q p hp hm rows (standardPhysicalCubeOutput z)))
  simpa only [hid] using he

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsCoveredL1Perturbation
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_physical_jet_covered_l1_perturbation (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Q)
    (_hLQ : (((Lf + Lg) * ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    (ideal : EuclideanJetLayers U O → ℂ) (_hi : Measurable ideal)
    {δ : ℝ} (_happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δ)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))) -
          ideal (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))‖) ≤ E + 2 * δ + (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_physical_jet_covered_l1_sampling m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows P hP hn hd U _ _ _ μ _ _ ν _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP ideal hi δ happ E hmass
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
  let actual := fun y => f (coveredJetAmbientTorus U 1 y)
  let surrogate := fun y => g (coveredJetAmbientTorus U 1 y)
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hP hn hd U μ ν p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb hη hQ hdim hLQ hηQ hfreqP hcoeffP
    (E := ∫ y, ‖actual y - surrogate y‖ ∂ξ) le_rfl
  refine ⟨hZ, ?_⟩
  exact selectedResidueDensityMass_l1_surrogate ξ stride G V hV hZ
    (fun z => physicalCubeRowSample U q rows p hm (standardPhysicalCubeOutput z))
    actual ideal surrogate
    (hf.continuous.comp (coveredJetAmbientTorus_continuous U 1)).measurable hi
    (hg.continuous.comp (coveredJetAmbientTorus_continuous U 1)).measurable
    (fun y => hfb _) (fun y => hgb _) happ hmass
    (he.trans_eq (by ring))

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialAnalyticFactor
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (stride N : X → ℕ)
variable {τ : ℝ} (mesh : ℝ≥0) {modulus period : ℕ}
variable (t : X → SpatialSiteLabel α modulus 4 mesh) (site : Finset α)
variable {Y : Type*} (F : Y → ℂ)

local notation "smooth" => physicalResidueSpatialSmooth root D base residue stride 4 mesh
  (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site

noncomputable def physicalSpatialAnalyticContinuous (v : (X → ℝ) × Y) : ℂ :=
  smooth v.1 * F v.2

theorem physicalSpatialAnalytic_normalized [PseudoMetricSpace Y]
    (hN : ∀ x, 0 < N x) (hperiod : ∀ x, stride x * modulus ∣ period)
    (u : X → ℤ) (y : Y) :
    physicalResidueSpatialSiteFactor root D base residue stride 4 mesh
      (trimmedSpatialRootScale τ N stride) t site u * F y =
    physicalResidueSpatialMaskMod root D base residue stride 4 mesh hperiod t site
      (fun x => (u x : ZMod period)) *
    physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N mesh t site F
      (fun x => (u x : ℝ) / N x, y) := by
  rw [physicalResidueSpatialMaskMod_eval,
    physicalResidueSpatialSiteFactor_normalized root D base residue stride 4 mesh
      (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site
      (fun x => Nat.cast_ne_zero.mpr (hN x).ne')]
  exact mul_assoc _ _ _

theorem physicalSpatialAnalyticContinuous_bounds [PseudoMetricSpace Y]
    (hN : ∀ x, 0 < N x) (hstride : ∀ x, 0 < stride x) (hτ : 0 < τ) (hmesh : 0 < mesh)
    {L : ℝ≥0} (hF : LipschitzWith L F) (hFb : ∀ y, ‖F y‖ ≤ 1)
    {P EX ES Eτ : ℝ} (hP : 0 ≤ P)
    (hbox : (4 : ℝ) ≤ Real.exp P) (hinv : 1 / (mesh : ℝ) ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp EX)
    (hα : (Fintype.card (Unit ⊕ α) : ℝ) ≤ Real.exp ES)
    (hτexp : 1 / τ ≤ Real.exp Eτ) :
    (∀ v, ‖physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N mesh t site F v‖ ≤ 1) ∧
      LipschitzWith (⟨Real.exp (ES + EX + (3 * P + 6) + (Eτ + 8)), Real.exp_nonneg _⟩ + L)
        (physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N mesh t site F) := by
  let Lscale : ℝ≥0 := ⟨8 / τ, div_nonneg (by norm_num) hτ.le⟩
  have hscale (x : X) : |(N x : ℝ) / ((stride x : ℝ) * trimmedSpatialRootScale τ N stride x)| ≤ Lscale := by
    rw [trimmedSpatialRootScale_normalized_ratio N stride hτ hN hstride x]
    exact (abs_of_nonneg (div_nonneg (by norm_num) hτ.le)).le
  have hscaleExp : (Lscale : ℝ) ≤ Real.exp (Eτ + 8) := by
    calc
      _ = 8 * (1 / τ) := by change 8 / τ = 8 * (1 / τ); ring
      _ ≤ Real.exp 8 * Real.exp Eτ := mul_le_mul
        (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8)
        hτexp (div_nonneg zero_le_one hτ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hsp := physicalResidueSpatialSmooth_bounds root D base residue stride 4 mesh
    (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site hmesh hscale
  have hspLip := physicalResidueSpatialSmooth_pre_lipschitz root D base residue stride 4 mesh
    (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site hmesh hscale hP
    (by norm_num) hbox hinv hX hα hscaleExp
  exact VectorPolynomial.normalizedSiteTwistProduct_bounds smooth F hspLip hF hsp.1 hFb

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineResidueEpoch
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct

noncomputable def HasFixedAffineResidueChild {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (p : ℝ) (q P : ℕ) (hP : 0 < P) (C a : ℕ) (cost : ℝ) : Prop :=
  ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
      (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
    E.filtration = D.filtration.gradedRefiltration W ∧
    ∃ (n : ℕ) (_hn : n ≤ d)
      (Q : RationalFilteredNilmanifold
        ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n),
      Q.filtration = E.filtration.quotientTop ∧
      let H := D.filtration.gradedRefiltrationSubalgebra W
      let N := H ⧸ E.filtration.layerIdeal (s + 1)
      let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
      let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
      let := realification_moduleTopology_t2 Q.basis
      ∃ V : RationalFilteredNilmanifold N s n,
        V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
        ∃ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
          DegreeLE (fun _ => 1) s child.log ∧
          FixedAffineResidueDescent D W V b child p q P hP C a cost

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

noncomputable def RetainedAffineResidueEpoch {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ) (p cost : ℝ) (C : ℕ) : Prop :=
  ∃ (v : Fin d → D.filtration.AssociatedGraded) (q P : ℕ) (hP : 0 < P)
      (κ : D.RealGroup)
      (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω W.toSubmodule ∧
    (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp p ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ κ ∈ D.realLattice ∧
    E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩ ∧
    D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A (Real.exp (p + 2)) E ∧
    (∀ B : σ → ℝ, (∀ i, 0 < B i) → ∀ (r : ℚ) (h : σ → ℚ),
      (∀ i, |(h i : ℝ)| ≤ A i) → (∀ i, |(r : ℝ)| * B i ≤ A i) →
      D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) B (Real.exp (p + 2))
        (D.filtration.realification.scalarAffineAdaptedHom r h E)) ∧
    D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q R ∧
    coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
    HasFixedAffineResidueChild D W b p q P hP C 1 cost

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineEpochTransition
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

noncomputable def FixedAffineEpochTransition
    {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ)
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (work cost : ℝ) (P C B : ℕ) : Prop :=
  ∀ p : ℝ, 0 ≤ p → p ≤ work → ∀ (r : ℤ) (h : σ → ℤ) (A' : σ → ℝ),
    (∀ i, 0 < A' i) → (∀ i, |(h i : ℝ)| ≤ A i) →
    (∀ i, |(r : ℝ)| * A' i ≤ A i) →
    ∀ S : D.Niltest (fun _ : σ => 1),
      S.orbit = D.filtration.realification.scalarAffineOrbitHom (r : ℚ)
        (fun i => (h i : ℚ)) T.orbit →
      S.UnitIntervalValued → S.ComplexityLE p →
      ∀ q rho : ℝ, p ≤ q → (Fintype.card σ : ℝ) ≤ q →
        verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
        ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ), 0 < M →
          ∀ (u v : σ → ℤ) (J : σ → ℕ), (∀ i, 0 < J i) →
          (∀ i, v i ≡ u i [ZMOD (M : ℤ)]) →
          (∀ i, (M * (M * P)).Coprime (J i)) →
          (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ)) →
          ∀ Δ ε δ : ℝ, 0 < δ → δ ≤ 1 → ε < 1 / 2 →
          2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤ Δ / 2 →
          8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) ≤ Δ / 4 →
          (∀ i, 8 ≤ δ * (N i : ℝ)) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A' i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A' i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 →
          Δ ≤ ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖ →
          ResiduePairDimensionDrop D ω hF S W lo N M u v J ((q + B) ^ B) ∨
          AnchoredChildResidueComparison V
            (V.filtration.realification.scalarAffineOrbitHom (r : ℚ) (fun i => (h i : ℚ)) child)
            cost (Δ / 4) δ lo N M P u v J

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedAmbientProjectedDensityMultiple
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_fixed_kernel_euclidean_ambient_density_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L C : ℝ≥0}
    (_hf : LipschitzWith L f) (_hcap : ∀ z, f z ∈ Set.Icc (0 : ℝ) C)
    (_hmass : (∫ x, f (coefficientAmbientTorus U x) ∂μ) = 1),
    let rows := fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    ∃ (g : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
      (F : (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) C) ∧
      Integrable g ξ ∧ (∫ y, g y ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x)))).map
        (euclideanCoefficientJetMap U root (Matrix.of difference) rows) = realDensityMeasure ξ g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith ((L * (Fintype.card (Finset (Fin q)) *
        Real.toNNReal (Real.exp ((P + A) ^ A)))) *
        ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)) F ∧
      (∀ y, g y = F (coveredJetAmbientTorus U 1 y)) ∧
      physicalDensityProjection U root difference d
        (fun x => f (coefficientAmbientTorus U x)) g := by
  obtain ⟨A, hA, hsource⟩ := exists_fixed_kernel_ambient_density_multiple m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hsource⟩ := hsource root₀ difference₀ a ha hperiod hP hK hsite period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ ν _ _ f L C hf hcap hmass rows cover ξ
  have hfull := hperiod.trans (integerPeriod_range_le_of_columns
    (Matrix.of difference₀) (Matrix.of difference) e hdifference)
  obtain ⟨g, F, hgc, hgb, _, hgm, hglaw, hFb, hFl, heq, hprojection⟩ :=
    hsource root difference e hroot hdifference U μ f hf hcap hmass
  obtain ⟨hfc, hfb, hfi, hfm, hvalue, hflaw⟩ :=
    siteImage_density_euclideanJet U root (Matrix.of difference) a ha hfull μ ν
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x))))
      g hgc hgb hgm hglaw
  refine ⟨_, fun z => F (lowJetAmbientSites z), hfc, hfb, hfi, hfm, hflaw,
    fun z => hFb _, hFl.comp lowJetAmbientSites_lipschitz, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := euclideanCoefficientJetMap_surjective U root (Matrix.of difference) a ha hfull
      rows (fun _ => Subtype.val_injective) (fun _ o => o.property) y
    exact (hvalue (Set.rangeFactorization
      (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference))) x)).trans
      ((heq x).trans (congrArg F (lowJetAmbientSites_coefficient U root (Matrix.of difference) x).symm))
  · intro X Index _ frequency coeff η happrox p hp hm z
    have he := hvalue (Set.rangeFactorization
      (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference)))
      (affineCoefficientCoverSample U p hm d z))
    exact (congrArg (fun r : ℝ =>
      ‖affineCubeFourierProjection U root difference frequency p coeff z - (r : ℂ)‖) he).trans_le
      (hprojection frequency coeff happrox p hp hm z)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_ambient_projected_density_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let root := allocatedPhysicalCubeRoot B U b S c x y
    let dirs := allocatedPhysicalCubeDirections B U b S x y
    let _ := euclideanCoefficientJetMap U root dirs
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    ∃ (g : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
      (F : (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ z, g z ∈ Set.Icc (0 : ℝ) cap) ∧ Integrable g ξ ∧
      (∫ z, g z ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U root dirs
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))) =
        realDensityMeasure ξ g ∧
      physicalDensityProjection U root dirs d density g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) cap) ∧
      LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
      ∀ z, g z = F (coveredJetAmbientTorus U 1 z) := by
  obtain ⟨A, hA, hcover⟩ := exists_fixed_kernel_euclidean_ambient_density_multiple m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod period hp hpP
  let Q := P + (q + 2 : ℕ)
  have hPQ : P ≤ Q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  obtain ⟨d, hdiv, hd, hdb, hcover⟩ := hcover (fun g => c (.inl g) + (x g none : ℤ))
    (fun i g => (x g (some i) : ℤ)) (a : ℤ) (by exact_mod_cast ha.ne') hperiod
    (hP.trans hPQ) (hG.trans hPQ) (kernelCubeBox_site_le_exp (fun g => c (.inl g)) x hc hL)
    period hp (hpP.trans (Real.exp_le_exp.mpr hPQ))
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    density cap root dirs unusedJetMap cover ξ densityLip sectionLip reconstructionLip
  have hs := allocatedCoefficientDensity_positive_spec B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hambient := allocatedCoefficientAmbientDensity_bounds B U b o S C V hC hV hR hσ
  have heq (z) := allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall z
  have hm : (∫ z, allocatedCoefficientAmbientDensity B U b o S (coefficientAmbientTorus U z) ∂μ) = 1 := by
    simp_rw [heq]
    exact hs.2.2.2.1
  obtain ⟨g, F, hgc, hgb, hgi, hgm, hglaw, hFb, hFl, hvalue, hprojection⟩ :=
    hcover root dirs Sum.inl (fun _ => rfl) (fun _ _ => rfl) U μ ν
      (allocatedCoefficientAmbientDensity B U b o S) hambient.2
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      (fun z => by simpa only [Set.mem_Icc, NNReal.coe_pow] using hambient.1 z) hm
  refine ⟨g, F, hgc, hgb, hgi, hgm, ?_, ?_, hFb, hFl, hvalue⟩
  · simp_rw [heq] at hglaw
    convert hglaw using 1
    rfl
  · intro X Index _ frequency coeff η happ p hp hm v
    apply hprojection frequency coeff ?_ p hp hm v
    intro z
    simpa only [heq] using happ z

end Erdos3.VectorPolynomial

end

end OAI

end


