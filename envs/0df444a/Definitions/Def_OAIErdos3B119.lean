-- Prove2me | Definitions.Def_OAIErdos3B119
-- name    : OAIErdos3B119
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T04:14:54.945388+00:00
-- url     : https://prove2.me/theorems/8d8bc92a-eab9-4f48-afc1-661c377a8185
-- title:
--   OpenAI Erdős-3 split, definitions bundle 120 of 132
-- statement:
--   Definitions bundle 120 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B118`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 120 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.exists_real_normalized_dilationPair_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonLog`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonLog_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonLog_coefficient`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonLog_eval`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonLog_first`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonLog_first_eval`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonLog_second_ambient`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonLog_second_eval`, `OAI.Erdos3.MultidegreeLieFiltration.realDilationPairProjection_mem`, `OAI.Erdos3.MultidegreeLieFiltration.realDilationPair_top_group_relation`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedLog_diagonal`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedDilationPairOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedDilationPairOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedDilationPairOrbit_zero`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedDilationPairPolynomial_adapted`, `OAI.Erdos3.NativeIntegerVectorEquivalence.of_dilation_family`, `OAI.Erdos3.NativeVectorCorrelation.exists_fixed_coordinate`, `OAI.Erdos3.NativeVectorCorrelation.exists_half_signal`, `OAI.Erdos3.NativeVectorCorrelation.mapCoordinates`, `OAI.Erdos3.NativeVectorCorrelation.scaleSignal`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairProjection`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairProjection_one`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairProjection_zero`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_marked_native_factorization`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_marked_polynomial_factorization`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_prescribed_real_polynomial_lift`, `OAI.Erdos3.NilpotentLieFiltration.markedNativeLiftInput`, `OAI.Erdos3.NilpotentLieFiltration.realDilationPairProjection`, `OAI.Erdos3.NilpotentLieFiltration.realDilationPairProjection_coord`, `OAI.Erdos3.NilpotentLieFiltration.realDilationPairProjection_mem`, `OAI.Erdos3.NilpotentLieFiltration.realDilationPair_top_group_relation`, `OAI.Erdos3.NilpotentLieFiltration.realifiedDilationPairEquiv_projection`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.additiveTripleProjection_lattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationObservable`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationObservable_component_top`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationObservable_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationObservable_norm_le`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationObservable_top_invariant`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationPairProjection_lattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationSpaceProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationSpaceProjection_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationSpaceProjection_smul`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationSpaceProjection_top_smul`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleSpaceProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleSpaceProjection_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleSpaceProjection_smul`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_nativeTopMarkKernel_spanning_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_marked_kernel_representatives`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_topLayer_basis_logHeight`, `OAI.Erdos3.basisMatrixKernelEquiv`, `OAI.Erdos3.basisMatrixKernelEquiv_repr`, `OAI.Erdos3.dilationTensorCrossProduct`, `OAI.Erdos3.exists_bounded_lie_kernel_basis`, `OAI.Erdos3.exists_bounded_linearMap_kernel_basis`, `OAI.Erdos3.exists_lie_kernel_basis_exp_height`, `OAI.Erdos3.exists_lie_kernel_subalgebra_basis_logHeight`, `OAI.Erdos3.exists_marked_kernel_basis_commonHeight`, `OAI.Erdos3.exists_marked_kernel_basis_commonHeight_of_dim`, `OAI.Erdos3.integerDilationVector`, `OAI.Erdos3.markedKernelCommonHeight`, `OAI.Erdos3.signedTensorProduct`, `OAI.Erdos3.signedTensorProduct_lipschitz`, `OAI.Erdos3.signedTensorProduct_norm`, `OAI.Erdos3.signedTensorProduct_norm_le`, `OAI.Erdos3.signedTensorProduct_phase`, `OAI.Erdos3.signedTensorVector`, `OAI.Erdos3.signed_power_phase_cancellation`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B039

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledMarkedPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_prescribed_real_polynomial_lift
    {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧ l ∣ m ∧
      ∀ (x : F.RealPolynomialSymbolGroup w)
        (q : (G.realification.adaptedPolynomialFiltration w).Group),
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ x.coord =
        (G.realPolynomialSymbolHom c τ hG w q).coord →
      ∃ z : (F.realification.adaptedPolynomialFiltration w).Group,
        F.realPolynomialSymbolHom b ω hF w z = x ∧
        F.realPolynomialGroupMap G φ hφ w z = q ∧
        (∀ (a : ℕ) (T : σ → ℝ), (∀ i, 0 < T i) →
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) x →
          CoefficientBound (c.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) q.coord.val →
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ (a + 12))) z.coord.val) ∧
        (F.SymbolRationalGrid b ω hF w l x → CoefficientGrid (c.baseChange ℝ) l q.coord.val →
          CoefficientGrid (b.baseChange ℝ) m z.coord.val) := by
  classical
  obtain ⟨S, hS, hSlayer, hheight⟩ := F.exists_bounded_filtered_section G b ω hF c τ hG
    φ.toLinearMap hsurj hH hentries
  have hφm : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact hentries i j
  have hSm : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j)
      (rationalKernelHeight (Fintype.card κ) H) := by
    intro i j
    simpa only [LinearMap.toMatrix_apply] using hheight i j
  let m := matrixDenominator (LinearMap.toMatrix c b S) *
    matrixDenominator (LinearMap.toMatrix b c φ.toLinearMap) * l
  obtain ⟨hm, hlm, _⟩ := sectionCorrectedPolynomial_denominator_bounds b c φ.toLinearMap S hφm hSm hl
  refine ⟨m, hm, filtered_section_pair_denominator_le_exp
    (LinearMap.toMatrix b c φ.toLinearMap) (LinearMap.toMatrix c b S) l hp hι hκ hHp hφm hSm hlp,
    hlm, ?_⟩
  intro x q hcompat
  obtain ⟨z, hz, hsymbol, hmarked⟩ := F.sectionCorrectedPolynomial_prescribed_symbol G φ hφ
    b ω hF c τ hG w S hS hSlayer x.coord q.coord hcompat
  refine ⟨⟨z⟩, NilpotentLieBCHGroup.ext hsymbol, NilpotentLieBCHGroup.ext hmarked, ?_, ?_⟩
  · intro a T hT hx hq
    change CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ (a + 12))) z.val
    rw [hz]
    have hx' : CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a))
        (F.realSymbolRepresentative b ω hF w x.coord) :=
      F.realSymbolRepresentative_slow_coefficients b ω hF w T hT (Real.exp_nonneg _) x hx
    have hout := sectionCorrectedPolynomial_coefficientBound b c φ.toLinearMap S hφm hSm
      (F.realSymbolRepresentative b ω hF w x.coord) q.coord.val T hT
      (Real.exp_nonneg _) (Real.exp_nonneg _) hx' hq
    exact hout.mono _ T hT
      (filtered_section_coefficient_loss_le_exp (Fintype.card ι) (Fintype.card κ) H a hp hι hκ hHp)
  · intro hx hq
    change CoefficientGrid (b.baseChange ℝ) m z.val
    rw [hz]
    have hx' : CoefficientGrid (b.baseChange ℝ) l
        (F.realSymbolRepresentative b ω hF w x.coord) := by
      obtain ⟨v, hv⟩ := F.realSymbolRepresentative_rational_coefficients b ω hF w l x hx
      intro α
      exact ⟨fun i => v (α, i), funext (fun i => congrFun hv (α, i))⟩
    exact sectionCorrectedPolynomial_coefficientGrid b c φ.toLinearMap S
      (F.realSymbolRepresentative b ω hF w x.coord) q.coord.val hl hx' hq

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_marked_polynomial_factorization
    {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧ l ∣ m ∧
      ∀ (a : ℕ) (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : F.RealPolynomialSymbolGroup w),
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      ∀ EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ E.coord =
        (G.realPolynomialSymbolHom c τ hG w EF).coord →
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ R.coord =
        (G.realPolynomialSymbolHom c τ hG w RF).coord →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      CoefficientBound (c.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) EF.coord.val →
      F.SymbolRationalGrid b ω hF w l R →
      CoefficientGrid (c.baseChange ℝ) l RF.coord.val →
      ∃ e middle r : (F.realification.adaptedPolynomialFiltration w).Group,
        e * middle * r = g ∧
        F.realPolynomialSymbolHom b ω hF w e = E ∧
        F.realPolynomialSymbolHom b ω hF w middle = P ∧
        F.realPolynomialSymbolHom b ω hF w r = R ∧
        F.realPolynomialGroupMap G φ hφ w e = EF ∧
        F.realPolynomialGroupMap G φ hφ w r = RF ∧
        F.realPolynomialGroupMap G φ hφ w middle =
          EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹ ∧
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ (a + 12))) e.coord.val ∧
        CoefficientGrid (b.baseChange ℝ) m r.coord.val := by
  obtain ⟨m, hm, hmp, hlm, hlift⟩ := F.exists_controlled_prescribed_real_polynomial_lift
    G φ hφ b ω hF c τ hG w hsurj hH hl hentries hp hι hκ hHp hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro a T hT g E P R hprod EF RF hE hR hEslow hEFbound hRgrid hRFgrid
  obtain ⟨e, he, heF, hebound, _⟩ := hlift E EF hE
  obtain ⟨r, hr, hrF, _, hrgrid⟩ := hlift R RF hR
  refine ⟨e, e⁻¹ * g * r⁻¹, r, by group, he, ?_, hr, heF, hrF, ?_,
    hebound a T hT hEslow hEFbound, hrgrid hRgrid hRFgrid⟩
  · rw [map_mul, map_mul, map_inv, map_inv, he, hr, ← hprod]
    group
  · rw [map_mul, map_mul, map_inv, map_inv, heF, hrF]

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

def markedNativeLiftInput (p : ℝ) : ℝ := (p + 2) ^ 11 + p

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

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeDilationPairProjections
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairProjection (q : ℚ) (j : Fin 2) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ L :=
  (liePiEval j).comp (F.dilationPairToPi q)

@[simp] theorem dilationPairProjection_zero (q : ℚ) :
    F.dilationPairProjection q 0 = F.dilationPairFirst q := rfl

@[simp] theorem dilationPairProjection_one (q : ℚ) :
    F.dilationPairProjection q 1 = F.dilationPairSecond q := rfl

noncomputable def realDilationPairProjection (q : ℚ) (j : Fin 2) :
    (F.dilationPairFiltration q).realification.Group →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.dilationPairFiltration q).lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) (F.dilationPairProjection q j)

theorem realifiedDilationPairEquiv_projection (q : ℚ) (j : Fin 2)
    (x : ℝ ⊗[ℚ] F.dilationPairSubalgebra q) :
    pairToPi (F.realifiedDilationPairEquiv q x).val j =
      realificationLieHom (F.dilationPairProjection q j) x := by
  rw [F.realifiedDilationPairEquiv_coe]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul scalar vector =>
    rw [realificationLieHom_tmul, realPairEquiv_tmul, realificationLieHom_tmul]
    fin_cases j <;> rfl
  | add first second hfirst hsecond =>
    simp only [map_add, Pi.add_apply, hfirst, hsecond]

theorem realDilationPairProjection_coord (q : ℚ) (j : Fin 2)
    (g : (F.dilationPairFiltration q).realification.Group) :
    (F.realDilationPairProjection q j g).coord =
      pairToPi (F.realifiedDilationPairEquiv q g.coord).val j :=
  (F.realifiedDilationPairEquiv_projection q j g.coord).symm

theorem realDilationPairProjection_mem (q : ℚ) (j : Fin 2) {n : ℕ}
    {g : (F.dilationPairFiltration q).realification.Group}
    (hg : g ∈ (F.dilationPairFiltration q).realification.subgroup n) :
    F.realDilationPairProjection q j g ∈ F.realification.subgroup n := by
  have hm := (F.realifiedDilationPairEquiv_mem_layer q n g.coord).mp hg
  change (F.realDilationPairProjection q j g).coord ∈ F.realification.layer n
  rw [F.realDilationPairProjection_coord]
  fin_cases j
  · exact hm.1
  · exact hm.2.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem dilationPairProjection_lattice (q : ℚ) (j : Fin 2) :
    M.dilationPairLattice q ≤ D.lattice.comap
      (mapOfSteps (M.filtration.ordinary.dilationPairProjection q j)) := by
  intro x hx
  have h := (M.dilationPairLattice_mem q x).mp hx
  fin_cases j
  · exact h.1
  · exact h.2

noncomputable def dilationSpaceProjection (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hE : E.lattice = M.dilationPairLattice q) (j : Fin 2) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (M.filtration.ordinary.realDilationPairProjection q j)
    (realificationMap_subgroup (M.filtration.ordinary.dilationPairProjection q j) _ _
      (by rw [hE]; exact M.dilationPairProjection_lattice q j))

theorem dilationSpaceProjection_smul (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hE : E.lattice = M.dilationPairLattice q) (j : Fin 2) (g : E.RealGroup) (x : E.Space) :
    M.dilationSpaceProjection q E hE j (g • x) =
      M.filtration.ordinary.realDilationPairProjection q j g •
        M.dilationSpaceProjection q E hE j x := cosetMap_smul _ _ _ _ _ _

theorem dilationSpaceProjection_lipschitz (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hEL : E.lattice = M.dilationPairLattice q) (j : Fin 2)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ a k, rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection q j (E.basis a)) k) ≤ p) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.dilationSpaceProjection q E hEL j) := by
  let := E.metricSpace
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E D (M.filtration.ordinary.dilationPairProjection q j)
        (by rw [hEL]; exact M.dilationPairProjection_lattice q j)
        hp hE hD (fun k a => hheight a k) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationObservable
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators NNReal

noncomputable def signedTensorProduct (m : ℤ) (v : Fin m.natAbs → ℂ) : ℂ :=
  if m < 0 then star (∏ i, v i) else ∏ i, v i

theorem signedTensorProduct_norm (m : ℤ) (v : Fin m.natAbs → ℂ) :
    ‖signedTensorProduct m v‖ = ∏ i, ‖v i‖ := by
  unfold signedTensorProduct
  split_ifs <;> simp only [norm_star, norm_prod]

theorem signedTensorProduct_norm_le (m : ℤ) (v : Fin m.natAbs → ℂ)
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖signedTensorProduct m v‖ ≤ 1 := by
  rw [signedTensorProduct_norm]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hv i)

theorem signedTensorProduct_phase (m : ℤ) (v : Fin m.natAbs → ℂ)
    (θ : CircleFourier.Circle) :
    signedTensorProduct m (fun i => character θ * v i) =
      character (m • θ) * signedTensorProduct m v := by
  cases m with
  | ofNat n =>
    have hn : ¬Int.ofNat n < 0 := not_lt.mpr (Int.natCast_nonneg n)
    simp only [signedTensorProduct, if_neg hn, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change character θ ^ n * (∏ i, v i) = character ((n : ℤ) • θ) * (∏ i, v i)
    rw [natCast_zsmul, character_nsmul]
  | negSucc n =>
    have hn : Int.negSucc n < 0 := by omega
    simp only [signedTensorProduct, if_pos hn, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change star (character θ ^ (n + 1) * (∏ i, v i)) =
      character (-((n + 1 : ℕ) : ℤ) • θ) * star (∏ i, v i)
    rw [neg_smul, character_neg, natCast_zsmul, character_nsmul, star_mul]
    exact mul_comm _ _

theorem signed_power_phase_cancellation (m : ℤ) (v : ℂ) (w : Fin m.natAbs → ℂ)
    (θ₀ θ₁ : CircleFourier.Circle) (hθ : θ₀ = m • θ₁) :
    (character θ₀ * v) * star (signedTensorProduct m (fun i => character θ₁ * w i)) =
      v * star (signedTensorProduct m w) := by
  rw [signedTensorProduct_phase, hθ, star_mul]
  calc
    _ = (character (m • θ₁) * star (character (m • θ₁))) *
        (v * star (signedTensorProduct m w)) := by ring
    _ = _ := by rw [circle_character_mul_star, one_mul]

theorem signedTensorProduct_lipschitz {X : Type*} [PseudoMetricSpace X]
    (m : ℤ) (f : Fin m.natAbs → X → ℂ) {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, ‖f i x‖ ≤ 1) :
    LipschitzWith (m.natAbs * K) (fun x => signedTensorProduct m (fun i => f i x)) := by
  have h := bounded_lipschitz_fintype_prod f (B := 1) le_rfl hf hn
  have hp : LipschitzWith (m.natAbs * K) (fun x => ∏ i, f i x) := by
    simpa only [Fintype.card_fin, one_pow, mul_one] using h.2
  unfold signedTensorProduct
  split_ifs
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using hp.dist_le_mul x y
  · exact hp

end Erdos3

end

section

namespace Erdos3

variable {σ I : Type*}

noncomputable def integerDilationVector (f : I → (σ → ℤ) → ℂ)
    (q : ℤ) (a : I) (x : σ → ℤ) : ℂ := f a (fun i => q * x i)

noncomputable def signedTensorVector (f : I → (σ → ℤ) → ℂ)
    (m : ℤ) (a : Fin m.natAbs → I) (x : σ → ℤ) : ℂ :=
  signedTensorProduct m (fun j => f (a j) x)

noncomputable def dilationTensorCrossProduct (f : I → (σ → ℤ) → ℂ)
    (q : ℤ) (t : ℕ) (a : I × (Fin (q ^ t).natAbs → I)) (x : σ → ℤ) : ℂ :=
  integerDilationVector f q a.1 x * star (signedTensorVector f (q ^ t) a.2 x)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realDilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairFiltration (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).realification.subgroup s) :
    F.realDilationPairProjection (q : ℚ) 0 g =
      (F.realDilationPairProjection (q : ℚ) 1 g) ^ (q ^ s) := by
  let h : (F.realification.dilationPairFiltration (q : ℚ)).Group :=
    ⟨F.realifiedDilationPairEquiv (q : ℚ) g.coord⟩
  have hh : h ∈ (F.realification.dilationPairFiltration (q : ℚ)).subgroup s :=
    (F.realifiedDilationPairEquiv_mem_layer (q : ℚ) s g.coord).mp hg
  have he (j : Fin 2) : F.realDilationPairProjection (q : ℚ) j g =
      (NilpotentLieBCHGroup.map (F.realification.dilationPairProjection (q : ℚ) j) h :
        F.realification.Group) := by
    apply NilpotentLieBCHGroup.ext
    exact F.realDilationPairProjection_coord (q : ℚ) j g
  rw [he 0, he 1]
  exact F.realification.dilationPair_top_group_relation q h hh

end NilpotentLieFiltration

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realDilationPairProjection_mem (q : ℚ) (j : Fin 2) (a : σ → ℕ)
    {g : (F.dilationPairMultidegree q).realification.Group}
    (hg : g ∈ (F.dilationPairMultidegree q).realification.subgroup a) :
    F.ordinary.realDilationPairProjection q j g ∈ F.realification.subgroup a := by
  have hm := (F.realifiedDilationPairEquiv_mem_multidegree q a g.coord).mp hg
  change (F.ordinary.realDilationPairProjection q j g).coord ∈ F.realification.layer a
  rw [F.ordinary.realDilationPairProjection_coord]
  fin_cases j
  · exact hm.1
  · exact hm.2.1

theorem realDilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairMultidegree (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairMultidegree (q : ℚ)).realification.subgroup bound) :
    F.ordinary.realDilationPairProjection (q : ℚ) 0 g =
      (F.ordinary.realDilationPairProjection (q : ℚ) 1 g) ^ (q ^ ∑ i, bound i) := by
  let h : (F.realification.dilationPairMultidegree (q : ℚ)).Group :=
    ⟨F.ordinary.realifiedDilationPairEquiv (q : ℚ) g.coord⟩
  have hh : h ∈ (F.realification.dilationPairMultidegree (q : ℚ)).subgroup bound :=
    (F.realifiedDilationPairEquiv_mem_multidegree (q : ℚ) bound g.coord).mp hg
  have he (j : Fin 2) : F.ordinary.realDilationPairProjection (q : ℚ) j g =
      (NilpotentLieBCHGroup.map (F.ordinary.realification.dilationPairProjection (q : ℚ) j) h :
        F.realification.Group) := by
    apply NilpotentLieBCHGroup.ext
    exact F.ordinary.realDilationPairProjection_coord (q : ℚ) j g
  rw [he 0, he 1]
  exact F.realification.dilationPair_top_group_relation q h hh

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem of_dilation_family {σ I : Type*} [Fintype I]
    {s : ℕ} {p b r : ℝ} (f : I → (σ → ℤ) → ℂ) (q : ℤ) (t : ℕ)
    (R : NativeIntegerModelFamily (fun _ : σ => 1) s b (dilationTensorCrossProduct f q t))
    (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hpr : p ≤ r) (htr : ((q ^ t).natAbs : ℝ) * p ≤ r) (hbr : b ≤ r) :
    NativeIntegerVectorEquivalence s r (integerDilationVector f q) (signedTensorVector f (q ^ t)) := by
  refine {
    left_dimension := hcard.trans (Real.exp_le_exp.mpr hpr)
    right_dimension := ?_
    expansion := ?_ }
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp p ^ (q ^ t).natAbs := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _
      _ = Real.exp (((q ^ t).natAbs : ℝ) * p) := (Real.exp_nat_mul p _).symm
      _ ≤ Real.exp r := Real.exp_le_exp.mpr htr
  · intro a b
    exact ⟨(NativeIntegerExpansion.ofModelFamily R (a, b)).mono hbr⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (q : ℚ)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
  (hEL : E.lattice = M.dilationPairLattice q)

noncomputable def dilationObservable (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ) (x : E.Space) : ℂ :=
  u₀ (ε • M.dilationSpaceProjection q E hEL 0 x) *
    star (signedTensorProduct m (fun a => u a (ε • M.dilationSpaceProjection q E hEL 1 x)))

theorem dilationObservable_mk (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ) (g : E.RealGroup) :
    M.dilationObservable q E hEL m ε u₀ u (QuotientGroup.mk g) =
      u₀ (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection q 0 g)) *
        star (signedTensorProduct m (fun a => u a
          (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection q 1 g)))) := rfl

theorem dilationObservable_norm_le (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ)
    (h₀ : ∀ x, ‖u₀ x‖ ≤ 1) (hu : ∀ a x, ‖u a x‖ ≤ 1) (x : E.Space) :
    ‖M.dilationObservable q E hEL m ε u₀ u x‖ ≤ 1 := by
  simp only [dilationObservable, norm_mul, norm_star]
  simpa only [mul_one] using mul_le_mul (h₀ _)
    (signedTensorProduct_norm_le m _ (fun a => hu a _))
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem dilationSpaceProjection_top_smul (ε : D.RealGroup) (j : Fin 2) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration q).realification.subgroup s)
    (x : E.Space) :
    ε • M.dilationSpaceProjection q E hEL j (k • x) =
      M.filtration.ordinary.realDilationPairProjection q j k •
        (ε • M.dilationSpaceProjection q E hEL j x) := by
  have hz := M.filtration.ordinary.realDilationPairProjection_mem q j hk
  rw [M.dilationSpaceProjection_smul, ← mul_smul, ← mul_smul,
    (M.filtration.realification.ordinary.top_commutes _ hz ε).eq]

theorem dilationObservable_component_top (ε : D.RealGroup) (u : D.Space → ℂ)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hu : ∀ z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u (z • x) = character (χ z) * u x)
    (j : Fin 2) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration q).realification.subgroup s)
    (x : E.Space) :
    u (ε • M.dilationSpaceProjection q E hEL j (k • x)) =
      character (χ (M.filtration.ordinary.realDilationPairProjection q j k)) *
        u (ε • M.dilationSpaceProjection q E hEL j x) := by
  rw [M.dilationSpaceProjection_top_smul q E hEL ε j k hk x]
  exact hu _ (M.filtration.ordinary.realDilationPairProjection_mem q j hk) _

theorem dilationObservable_top_invariant (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ)
    (χ : D.RealGroup → CircleFourier.Circle)
    (h₀ : ∀ z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u₀ (z • x) = character (χ z) * u₀ x)
    (hu : ∀ a z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u a (z • x) = character (χ z) * u a x)
    (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration q).realification.subgroup s)
    (hphase : χ (M.filtration.ordinary.realDilationPairProjection q 0 k) =
      m • χ (M.filtration.ordinary.realDilationPairProjection q 1 k))
    (x : E.Space) :
    M.dilationObservable q E hEL m ε u₀ u (k • x) =
      M.dilationObservable q E hEL m ε u₀ u x := by
  have hvalue₀ := M.dilationObservable_component_top q E hEL ε u₀ χ h₀ 0 k hk x
  have hvalue (a) := M.dilationObservable_component_top q E hEL ε (u a) χ (hu a) 1 k hk x
  unfold dilationObservable
  rw [hvalue₀]
  simp_rw [hvalue]
  exact signed_power_phase_cancellation m _ _ _ _ hphase

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realifiedDilationPairPolynomial_adapted (q : ℚ)
    (p : VectorPolynomial σ ℚ (F.ordinary.realification.dilationPairSubalgebra q))
    (hp : (F.realification.dilationPairMultidegree q).Adapted p) :
    (F.dilationPairMultidegree q).realification.Adapted
      (VectorPolynomial.map (F.ordinary.realifiedDilationPairEquiv q).symm.toLinearMap p) := by
  intro a
  rw [coefficients_map]
  exact (F.realifiedDilationPairEquiv_symm_mem_multidegree q _ _).mpr (hp a)

noncomputable def realifiedDilationPairOrbit (q : ℚ)
    (p : (F.realification.dilationPairMultidegree q).PolynomialOrbit) :
    (F.dilationPairMultidegree q).realification.PolynomialOrbit :=
  (F.dilationPairMultidegree q).realification.polynomialOrbitOfLog
    (VectorPolynomial.map (F.ordinary.realifiedDilationPairEquiv q).symm.toLinearMap
      (p.log (F.realification.dilationPairMultidegree q)))
    (F.realifiedDilationPairPolynomial_adapted q _ (p.adapted _))

theorem realifiedDilationPairOrbit_eval (q : ℚ)
    (p : (F.realification.dilationPairMultidegree q).PolynomialOrbit) (x : σ → ℤ) :
    F.ordinary.realifiedDilationPairEquiv q
      (((F.dilationPairMultidegree q).realification.polynomialOrbitEval x
        (F.realifiedDilationPairOrbit q p)).coord) =
      ((F.realification.dilationPairMultidegree q).polynomialOrbitEval x p).coord := by
  change F.ordinary.realifiedDilationPairEquiv q
    (eval (fun j => (x j : ℚ)) (VectorPolynomial.map
      (F.ordinary.realifiedDilationPairEquiv q).symm.toLinearMap
        (p.log (F.realification.dilationPairMultidegree q)))) = _
  rw [eval_map]
  exact (F.ordinary.realifiedDilationPairEquiv q).apply_symm_apply _

theorem realifiedDilationPairOrbit_zero (q : ℚ)
    (p : (F.realification.dilationPairMultidegree q).PolynomialOrbit)
    (hp : (F.realification.dilationPairMultidegree q).polynomialOrbitEval 0 p = 1) :
    (F.dilationPairMultidegree q).realification.polynomialOrbitEval 0
      (F.realifiedDilationPairOrbit q p) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply (F.ordinary.realifiedDilationPairEquiv q).injective
  rw [F.realifiedDilationPairOrbit_eval, hp]
  exact (map_zero _).symm

theorem exists_real_normalized_dilationPair_orbit (q : ℤ)
    (p : F.realification.PolynomialOrbit) (a b : F.realification.Group)
    (hp0 : F.realification.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.dilationPairMultidegree (q : ℚ)).realification.PolynomialOrbit,
      (F.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval 0 g = 1 ∧
      ∀ x : σ → ℤ,
        let h := (F.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval x g
        F.ordinary.realDilationPairProjection (q : ℚ) 0 h =
          a⁻¹ * F.realification.polynomialOrbitEval (fun i => q * x i) p * b⁻¹ ∧
        F.ordinary.realDilationPairProjection (q : ℚ) 1 h =
          a⁻¹ * F.realification.polynomialOrbitEval x p * b⁻¹ := by
  obtain ⟨g, hg0, hg⟩ := F.realification.exists_normalized_dilationPair_orbit q p a b hp0
  refine ⟨F.realifiedDilationPairOrbit (q : ℚ) g,
    F.realifiedDilationPairOrbit_zero (q : ℚ) g hg0, ?_⟩
  intro x
  dsimp only
  have he (j : Fin 2) := F.ordinary.realDilationPairProjection_coord (q : ℚ) j
    ((F.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval x
      (F.realifiedDilationPairOrbit (q : ℚ) g))
  simp only [F.realifiedDilationPairOrbit_eval, hg x] at he
  exact ⟨NilpotentLieBCHGroup.ext (he 0), NilpotentLieBCHGroup.ext (he 1)⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealPolarizedLogDiagonal
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedLog_diagonal (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    F.realSquarefreeInclusion π (eval (fun j => x (π j)) (F.realPolarizedLog π p)) =
      realBlockPolynomialEval π p.val x := by
  apply realSquarefreePolynomialEquiv.injective
  ext c
  rw [F.realPolarizedLog_eval_coefficient, realBlockPolynomialEval_coefficient,
    blockExponent_weight π c.val x]
  by_cases hc : c.val = 0
  · rw [F.realPolarizedCoefficient_zero π p c hc, map_zero, map_zero, Pi.zero_apply]
    simp only [smul_zero, hc, blockExponent_zero, hp]
  · rw [F.realPolarizedCoefficient_self π p c hc]

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateFiber
namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

theorem exists_fixed_coordinate {G I : Type*} [Fintype I]
    {degree N : ℕ} [NeZero N] {p q : ℝ}
    (H : Finset G) (hH : H.Nonempty) (f : G → I → ZMod N → ℂ)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation degree N p (f h))) :
    ∃ i : I, ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
      Real.exp (-q) * H.card ≤ (H'.card : ℝ) ∧
      ∀ h ∈ H', Nonempty (NativeVectorCorrelation degree N p (fun _ : Unit => f h i)) := by
  classical
  let W (h : {h // h ∈ H}) := Classical.choice (hcorr h.val h.property)
  obtain ⟨h₀, hh₀⟩ := hH
  let code (h : G) := if hh : h ∈ H then (W ⟨h, hh⟩).coordinate else (W ⟨h₀, hh₀⟩).coordinate
  obtain ⟨i, _, H', hsub, hH', hfixed, hdense⟩ := exists_exponential_constant_fiber
    H ⟨h₀, hh₀⟩ code Set.univ (Set.toFinite _) (fun _ _ => Set.mem_univ _)
    (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hI)
  refine ⟨i, H', hsub, hH', hdense, ?_⟩
  intro h hh
  let Wh := W ⟨h, hsub hh⟩
  have hi : Wh.coordinate = i := by
    simpa only [code, dif_pos (hsub hh)] using hfixed h hh
  exact ⟨{ Wh with
    coordinate := ()
    correlation := by simpa only [hi] using Wh.correlation }⟩

end Erdos3.NativeVectorCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCorrelationCoordinates
namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

open scoped TensorProduct BigOperators

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

noncomputable def mapCoordinates {I J : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (g : J → ZMod N → ℂ) (e : I → J) (he : ∀ i x, g (e i) x = f i x) :
    NativeVectorCorrelation degree N p g :=
  { W with coordinate := e W.coordinate
           correlation := by simpa only [he] using W.correlation }

noncomputable def scaleSignal {I : Type*} {degree N : ℕ} [NeZero N] {p q : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (c : ℂ) (hq : 0 ≤ q) (hc : Real.exp (-q) ≤ ‖c‖) :
    NativeVectorCorrelation degree N (p + q) (fun i x => c * f i x) :=
  { W with
    complexity := W.complexity.mono (le_add_of_nonneg_right hq)
    correlation := by
      have he : (𝔼 x, (c * f W.coordinate x) * star (W.test.evalCyclic N (fun _ => x))) =
          c * (𝔼 x, f W.coordinate x * star (W.test.evalCyclic N (fun _ => x))) := by
        simp only [mul_assoc, Finset.mul_expect]
      rw [he, norm_mul, show -(p + q) = -q + -p by ring, Real.exp_add]
      exact mul_le_mul hc W.correlation (Real.exp_nonneg _) (norm_nonneg _) }

theorem exists_half_signal {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f) :
    Nonempty (NativeVectorCorrelation degree N (p + 1) (fun i x => f i x / 2)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hc : Real.exp (-1) ≤ ‖(1 / 2 : ℂ)‖ := by
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr htwo
  have h := W.scaleSignal (1 / 2) (by norm_num : (0 : ℝ) ≤ 1) hc
  refine ⟨h.mapCoordinates _ id ?_⟩
  intro i x
  simp only [id_eq, div_eq_mul_inv, one_mul, mul_comm]

end Erdos3.NativeVectorCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeMarkedKernelRepresentatives
namespace OAI

section

namespace Erdos3
open Module
open scoped Classical Matrix

section Linear
variable {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

noncomputable def basisMatrixKernelEquiv (b : Basis ι ℚ V) (c : Basis κ ℚ W)
    (T : V →ₗ[ℚ] W) :
    LinearMap.ker (LinearMap.toMatrix b c T).mulVecLin ≃ₗ[ℚ] LinearMap.ker T := by
  have hker : LinearMap.ker (LinearMap.toMatrix b c T).mulVecLin =
      (LinearMap.ker T).comap b.equivFun.symm.toLinearMap := by
    ext x
    have heq : LinearMap.toMatrix b c T *ᵥ x = c.equivFun (T (b.equivFun.symm x)) := by
      simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using
        LinearMap.toMatrix_mulVec_repr b c T (b.equivFun.symm x)
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [heq]
    exact c.equivFun.map_eq_zero_iff
  exact (LinearEquiv.ofEq _ _ hker).trans
    (b.equivFun.symm.ofSubmodule' (LinearMap.ker T))

@[simp] theorem basisMatrixKernelEquiv_repr (b : Basis ι ℚ V) (c : Basis κ ℚ W)
    (T : V →ₗ[ℚ] W) (x : LinearMap.ker (LinearMap.toMatrix b c T).mulVecLin) (i : ι) :
    b.repr (basisMatrixKernelEquiv b c T x : V) i = (x : ι → ℚ) i := by
  change b.repr (b.equivFun.symm (x : ι → ℚ)) i = (x : ι → ℚ) i
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem exists_bounded_linearMap_kernel_basis
    (b : Basis ι ℚ V) (c : Basis κ ℚ W) (T : V →ₗ[ℚ] W)
    {H : ℕ} (hH : 1 ≤ H)
    (hT : ∀ i j, RationalHeightLE (c.repr (T (b j)) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker T),
        ∀ j i, RationalHeightLE (b.repr (bk j : V) i)
          (rationalKernelHeight (Fintype.card κ) H) := by
  let A := LinearMap.toMatrix b c T
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    simpa only [A, LinearMap.toMatrix_apply] using hT
  obtain ⟨t, ht, bk, hbk⟩ := exists_bounded_rational_kernel_basis A hH hA
  refine ⟨Module.finrank ℚ (LinearMap.ker A.mulVecLin), ?_,
    bk.map (basisMatrixKernelEquiv b c T), ?_⟩
  · simpa only [Module.finrank_pi, Module.finrank_self, Nat.mul_one] using
      (LinearMap.ker A.mulVecLin).finrank_le
  · intro j i
    simp only [Basis.map_apply]
    rw [basisMatrixKernelEquiv_repr b c T (bk j) i]
    exact (hbk j i).mono (rationalKernelHeight_mono hH ht)

end Linear

section Lie
variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_bounded_lie_kernel_basis
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {H : ℕ} (hH : 1 ≤ H)
    (hφ : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap),
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (rationalKernelHeight (Fintype.card κ) H) :=
  exists_bounded_linearMap_kernel_basis b c φ.toLinearMap hH hφ

theorem exists_lie_kernel_basis_exp_height
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {H : ℕ} (hHpos : 1 ≤ H)
    (hφ : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap), ∀ j i,
        ((b.repr (bk j : L) i).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
        ((b.repr (bk j : L) i).den : ℝ) ≤ Real.exp ((p + 2) ^ 7) := by
  obtain ⟨r, hr, bk, hbk⟩ := exists_bounded_lie_kernel_basis b c φ hHpos hφ
  have hbudget := rationalKernelHeight_le_budget (Fintype.card κ) H hp hκ hH
  exact ⟨r, hr, bk, fun j i =>
    ⟨(Nat.cast_le.mpr (hbk j i).1).trans hbudget,
      (Nat.cast_le.mpr (hbk j i).2).trans hbudget⟩⟩

theorem exists_lie_kernel_subalgebra_basis_logHeight
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (c.repr (φ (b j)) i) ≤ p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ φ.ker.toLieSubalgebra, ∀ j i,
        ((b.repr (bk j : L) i).num.natAbs : ℝ) ≤ Real.exp ((p + 3) ^ 7) ∧
        ((b.repr (bk j : L) i).den : ℝ) ≤ Real.exp ((p + 3) ^ 7) := by
  obtain ⟨r, hr, bk, hbk⟩ := exists_lie_kernel_basis_exp_height b c φ (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hφ i j))
    (by linarith : 0 ≤ p + 1) (hκ.trans (by linarith))
    (ceil_exp_le_exp_add_one hp)
  refine ⟨r, hr, bk, fun j i => ?_⟩
  rw [show p + 1 + 2 = p + 3 by ring] at hbk
  exact hbk j i

end Lie
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)

theorem exists_topLayer_basis_logHeight (hs : 1 ≤ s) {p : ℝ}
    (hD : D.GeometryComplexityLE p) :
    ∃ r : ℕ, ∃ b : Basis (Fin r) ℚ ((D.filtration.layerIdeal s).toLieSubalgebra),
      ∀ a i, rationalLogHeight (D.basis.repr (b a : L) i) ≤ p := by
  obtain ⟨b, hb⟩ := D.exists_positive_layer_basis s hs hD
  exact ⟨finrank ℚ (D.filtration.layer s), b, hb⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module

noncomputable def markedKernelCommonHeight (p : ℝ) : ℕ :=
  ⌈Real.exp ((p + 3) ^ 7)⌉₊

section Lie

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_marked_kernel_basis_commonHeight
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (c.repr (φ (b j)) i) ≤ p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap),
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (markedKernelCommonHeight p) := by
  obtain ⟨r, hr, bk, hbk⟩ :=
    exists_lie_kernel_subalgebra_basis_logHeight b c φ hp hκ hφ
  exact ⟨r, hr, bk, fun j i => rationalHeightLE_ceil_exp_of_entries (hbk j i)⟩

theorem exists_marked_kernel_basis_commonHeight_of_dim
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (c.repr (φ (b j)) i) ≤ p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ (r : ℝ) ≤ p ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap),
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (markedKernelCommonHeight p) := by
  obtain ⟨r, hr, bk, hbk⟩ := exists_marked_kernel_basis_commonHeight b c φ hp hκ hφ
  exact ⟨r, hr, (Nat.cast_le.mpr hr).trans hι, bk, hbk⟩

end Lie
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

theorem exists_nativeTopMarkKernel_spanning_budget :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin e) ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ),
      1 ≤ s → 0 ≤ p → D.GeometryComplexityLE p → (e : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (b.repr (φ (D.basis j)) i) ≤ p) →
      ∃ vP : Fin d → L,
        Submodule.span ℚ (Set.range vP) =
          D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap ∧
        ∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ (p + 2) ^ C := by
  let P : Polynomial ℕ := ((((Polynomial.X + 3) ^ 7 + 4) ^ 2 + 2) ^ 63 + 3)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s d e D b φ p hs hp hD he hφ
  classical
  obtain ⟨r, btop, hbtop⟩ := D.exists_topLayer_basis_logHeight hs hD
  obtain ⟨rk, _, bk, hbk⟩ := exists_lie_kernel_subalgebra_basis_logHeight
    D.basis b φ hp (by simpa only [Fintype.card_fin] using he) hφ
  let q : ℝ := (p + 3) ^ 7
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ p + 3 by linarith)
      (show 1 ≤ (7 : ℕ) by decide)
    have h' : p + 3 ≤ q := by simpa only [pow_one] using h
    linarith
  have htop : ∀ a i, rationalLogHeight (D.basis.repr (btop a : L) i) ≤ q :=
    fun a i => (hbtop a i).trans hpq
  have hk : ∀ a i, rationalLogHeight (D.basis.repr (bk a : L) i) ≤ q :=
    fun a i => (rationalLogHeight_le_iff _ _).mpr (hbk a i)
  let U := (D.filtration.layerIdeal s).toLieSubalgebra
  let V := φ.ker.toLieSubalgebra
  obtain ⟨bP, hbP⟩ := exists_binary_intersection_basis_logHeight
    D.basis U V btop bk hq
    (by simpa only [Fintype.card_fin] using hD.1.trans hpq) htop hk
  let B : ℝ := ((q + 4) ^ 2 + 2) ^ 63 + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hspan := exists_bounded_ambient_spanning D.basis (U ⊓ V) bP bP.span_eq
    (one_le_ceil_exp B) (fun a i => rationalHeightLE_ceil_exp (hbP a i))
  obtain ⟨vP, hvP, hvPh⟩ := hspan
  let indexEquiv : Fin d ≃ Fin (Fintype.card (Fin d)) := finCongr (Fintype.card_fin d).symm
  refine ⟨fun i => vP (indexEquiv i), ?_, ?_⟩
  · have hrange : Set.range (fun i => vP (indexEquiv i)) = Set.range vP := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨indexEquiv i, rfl⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨j, rfl⟩ := indexEquiv.surjective i
        exact ⟨j, rfl⟩
    rw [hrange]
    exact hvP
  intro a i
  have hheight : rationalLogHeight (D.basis.repr (vP (indexEquiv a)) i) ≤ B + 1 :=
    rationalLogHeight_le_of_height (hvPh (indexEquiv a) i) (ceil_exp_le_exp_add_one hB)
  apply hheight.trans
  simpa [P, q, B, Polynomial.eval₂_pow, add_assoc,
    show (2 : ℝ) + 1 = 3 by norm_num] using hbudget p hp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_marked_kernel_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ L M : Type*} [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d)
      (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup,
          g ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
            φ.ker.toLieSubalgebra →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          ∃ r : D.RealGroup,
            r ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
              φ.ker.toLieSubalgebra ∧
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ := by
  obtain ⟨a, _, hrep⟩ := exists_native_bounded_subalgebra_representatives s
  let P : Polynomial ℕ := ((Polynomial.X + 3) ^ 7 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro κ L M _ _ _ _ _ _ _ _ _ d D c φ p hp hD hκ hφ q hq hqp
  obtain ⟨n, hn, bk, hbk⟩ :=
    exists_lie_kernel_subalgebra_basis_logHeight D.basis c φ hp hκ hφ
  let t := (p + 3) ^ 7
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    exact (le_power_budget hp (by decide : 1 ≤ 7)).trans
      (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2) (by linarith : p + 2 ≤ p + 3) 7)
  have hn' : (Fintype.card (Fin n) : ℝ) ≤ t := by
    have hnd : n ≤ d := by simpa only [Fintype.card_fin] using hn
    simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hnd).trans (hD.1.trans hpt)
  have hinc : ∀ i j, rationalLogHeight (D.basis.repr (bk j : L) i) ≤ t :=
    fun i j => (rationalLogHeight_le_iff _ t).mpr (hbk j i)
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D φ.ker.toLieSubalgebra bk t ht
    (GeometryComplexityLE.mono D hD hpt)
    hn' hinc q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  have hb : (t + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hb), ?_⟩
  intro g hgK hg
  obtain ⟨r, hrK, hr, hrgrid, γ, hγ, hfac⟩ := hreps g hgK hg
  exact ⟨r, hrK, fun i => (hr i).trans (Real.exp_le_exp.mpr hb), hrgrid, γ, hγ, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeTripleProjections
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem additiveTripleProjection_lattice (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) :
    M.additiveTripleLattice i hi c hc ≤ D.lattice.comap
      (mapOfSteps (M.filtration.additiveTripleProjection i hi c hc j)) := by
  intro x hx
  have h := (M.additiveTripleLattice_mem i hi c hc x).mp hx
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2

noncomputable def tripleSpaceProjection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hE : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (M.filtration.realAdditiveTripleProjection i hi c hc j)
    (realificationMap_subgroup (M.filtration.additiveTripleProjection i hi c hc j) _ _
      (by rw [hE]; exact M.additiveTripleProjection_lattice i hi c hc j))

theorem tripleSpaceProjection_smul (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hE : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3)
    (g : E.RealGroup) (x : E.Space) :
    M.tripleSpaceProjection i hi c hc E hE j (g • x) =
      M.filtration.realAdditiveTripleProjection i hi c hc j g •
        M.tripleSpaceProjection i hi c hc E hE j x := cosetMap_smul _ _ _ _ _ _

theorem tripleSpaceProjection_lipschitz (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ a k, rationalLogHeight
      (D.basis.repr (M.filtration.additiveTripleProjection i hi c hc j (E.basis a)) k) ≤ p) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.tripleSpaceProjection i hi c hc E hEL j) := by
  let := E.metricSpace
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E D (M.filtration.additiveTripleProjection i hi c hc j)
        (by rw [hEL]; exact M.additiveTripleProjection_lattice i hi c hc j)
        hp hE hD (fun k a => hheight a k) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealComparisonPolynomialProjections
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realComparisonLog (p : F.realification.adaptedLieSubalgebra) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.comparisonSubalgebra π) :=
  ∑ a ∈ (coefficients p.val).support, monomial a (F.realComparisonCoefficient π p a)

theorem realComparisonLog_coefficient (p : F.realification.adaptedLieSubalgebra) (a : σ →₀ ℕ) :
    coefficients (F.realComparisonLog π p) a = F.realComparisonCoefficient π p a := by
  classical
  simp only [realComparisonLog, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · rw [coefficients_monomial, Finsupp.single_eq_same]
  · intro b _ hba
    rw [coefficients_monomial]
    exact Finsupp.single_eq_of_ne (Ne.symm hba)
  · intro ha
    rw [coefficients_monomial, Finsupp.single_eq_same]
    exact F.realComparisonCoefficient_zero_value π p a (Finsupp.notMem_support_iff.mp ha)

theorem realComparisonLog_adapted (p : F.realification.adaptedLieSubalgebra) :
    (F.comparisonFiltration π).realification.Adapted (fun _ => 1) (F.realComparisonLog π p) := by
  apply ((F.comparisonFiltration π).realification.adapted_iff_coefficients _ _).mpr
  intro a
  rw [F.realComparisonLog_coefficient]
  exact F.realComparisonCoefficient_mem π p a

theorem realComparisonLog_eval (p : F.realification.adaptedLieSubalgebra) (x : σ → ℚ) :
    eval x (F.realComparisonLog π p) =
      ∑ a ∈ (coefficients p.val).support,
        (a.prod fun i n => x i ^ n) • F.realComparisonCoefficient π p a := by
  simp only [realComparisonLog, map_sum, eval_monomial]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realComparisonLog_first (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) :
    VectorPolynomial.map ((realificationLieHom (F.comparisonFirst π)).toLinearMap.restrictScalars ℚ)
      (F.realComparisonLog π p) = p.val := by
  apply coefficients.injective
  ext a
  rw [coefficients_map, F.realComparisonLog_coefficient]
  exact F.realComparisonCoefficient_first π p hp a

theorem realComparisonLog_first_eval (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    realificationLieHom (F.comparisonFirst π) (eval x (F.realComparisonLog π p)) = eval x p.val := by
  change ((realificationLieHom (F.comparisonFirst π)).toLinearMap.restrictScalars ℚ)
    (eval x (F.realComparisonLog π p)) = _
  rw [← eval_map, F.realComparisonLog_first π p hp]

theorem realComparisonLog_second_ambient (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (eval x (F.realComparisonLog π p))) =
      realBlockPolynomialEval π p.val x := by
  rw [F.realComparisonLog_eval]
  simp only [map_sum, map_rat_smul, F.realComparisonCoefficient_second π p hp]
  rfl

theorem realComparisonLog_second_eval (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    realificationLieHom (F.comparisonSecond π) (eval x (F.realComparisonLog π p)) =
      eval (fun j => x (π j)) (F.realPolarizedLog π p) := by
  apply F.realSquarefreeInclusion_injective π
  rw [F.realComparisonLog_second_ambient π p hp, F.realPolarizedLog_diagonal π p hp]

end Erdos3.MultidegreeLieFiltration

end

end OAI

end


