-- Prove2me | Definitions.Def_OAIErdos3B048
-- name    : OAIErdos3B048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T07:35:05.947279+00:00
-- url     : https://prove2.me/theorems/26e90751-1c4c-4944-905c-011297172540
-- title:
--   OpenAI Erdős-3 split, definitions bundle 49 of 132
-- statement:
--   Definitions bundle 49 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B047`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 49 available.
--
--   Modules: `OAI.Erdos3.CoordinateDerivativeSystem`, `OAI.Erdos3.NilpotentLieFiltration.adaptedReducedRealSymbolHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficientAdjoint_norm_bound`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficientDirection_norm_bound`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficient_coordinate_system`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedMap`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedMap_mk`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.layerOnePolynomialCorrection`, `OAI.Erdos3.NilpotentLieFiltration.layerOnePolynomialCorrection_grid`, `OAI.Erdos3.NilpotentLieFiltration.layerOnePolynomialCorrection_slow`, `OAI.Erdos3.NilpotentLieFiltration.mem_realLayerOneGradedSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.mem_realLayerOneGradedSubmodule_mk`, `OAI.Erdos3.NilpotentLieFiltration.mem_realPointwisePolynomialSubgroup`, `OAI.Erdos3.NilpotentLieFiltration.pointwise_horizontal_coefficient_mem`, `OAI.Erdos3.NilpotentLieFiltration.pointwise_horizontal_derivative_mem`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedCoefficientBound_inv`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedLogDerivative_constant_unit`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAction_symm`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientDirectionMap`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientDirectionMap_mul`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientDirectionMap_triple`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficient_remove_derivative`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficient_remove_horizontal_lifts`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficient_remove_lifts`, `OAI.Erdos3.NilpotentLieFiltration.realFastLayerOneCorrection`, `OAI.Erdos3.NilpotentLieFiltration.realFastLayerOneCorrection_horizontal`, `OAI.Erdos3.NilpotentLieFiltration.realFast_bounded_horizontal_normalization`, `OAI.Erdos3.NilpotentLieFiltration.realFast_controlled_horizontal_factorization`, `OAI.Erdos3.NilpotentLieFiltration.realFast_horizontal_normalization`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientDirectionMap_horizontal_unit`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneCorrection`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneCorrection_grid`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneCorrection_horizontal_derivative`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneCorrection_log`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneCorrection_mem_pointwise`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneCorrection_mem_pointwiseSubgroup`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneCorrection_realize`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneCorrection_slow`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneGradedMap_mk`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneGradedMap_section`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneLieSection`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneLieSection_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneLieSection_coordinate_zero`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneLieSection_norm`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneLieSection_rightInverse`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneProjection_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realPointwisePolynomialSubgroup`, `OAI.Erdos3.NilpotentLieFiltration.realPointwisePolynomialSubgroup_le_fast`, `OAI.Erdos3.basisWeightedCoordinates`, `OAI.Erdos3.basisWeightedCoordinates_apply`, `OAI.Erdos3.basisWeightedCoordinates_norm_le_euclidean`, `OAI.Erdos3.basisWeightedCoordinates_norm_le_iff`, `OAI.Erdos3.basisWeightedCoordinates_operator_bound`, `OAI.Erdos3.coordinateDerivativeSystem_of_lifts`, `OAI.Erdos3.exists_uniform_coordinate_derivative_system`, `OAI.Erdos3.transport_coordinate_derivative_system`, `OAI.Erdos3.transport_coordinate_derivatives_to_rational_span`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B127

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedCoordinateExtraction
namespace OAI

section

namespace Erdos3

structure CoordinateDerivativeSystem {σ : Type*} [Fintype σ] [DecidableEq σ] {m a : ℕ}
    (ha : a ≤ m)
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (scale : Fin m → ℝ) (bound : ℝ) where
  K : Submodule ℝ (Fin a → ℝ)
  k : ℕ
  heightBound : ℕ
  height_le : (heightBound : ℝ) ≤ bound
  basisMatrix : Matrix (Fin a) (Fin k) ℚ
  basis_height : ∀ i j, RationalHeightLE (basisMatrix i j) heightBound
  independent_rat : LinearIndependent ℚ basisMatrix.col
  independent_real : LinearIndependent ℝ (basisMatrix.map (Rat.castHom ℝ)).col
  span_eq : K = Submodule.span ℝ (Set.range (basisMatrix.map (Rat.castHom ℝ)).col)
  rationalLift : K →ₗ[ℝ] (Fin m → ℝ)
  geometricLift : K →ₗ[ℝ] (Fin m → ℝ)
  factorization : geometricLift = A.toLinearMap.comp rationalLift
  rational_horizontal : ∀ x i, rationalLift x (Fin.castLE ha i) = x.val i
  geometric_horizontal : ∀ x i, geometricLift x (Fin.castLE ha i) = x.val i
  norm_scaled : ∀ x,
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * geometricLift x j)‖ ≤ bound * ‖x‖
  liftDenominator : ℕ
  liftDenominator_pos : 0 < liftDenominator
  liftDenominator_le : (liftDenominator : ℝ) ≤ bound
  rational_on_basis : ∀ j, ∃ x : K,
    x.val = (basisMatrix.map (Rat.castHom ℝ)).col j ∧ rationalLift x ∈ realDenominatorGrid liftDenominator
  derivativeDenominator : ℕ
  derivativeDenominator_pos : 0 < derivativeDenominator
  derivativeDenominator_le : (derivativeDenominator : ℝ) ≤ bound
  slow : σ → Fin m → ℝ
  rational : σ → Fin m → ℝ
  horizontal : σ → K
  derivative_eq : ∀ i, Y (Pi.basisFun ℝ σ i) = slow i + A (rational i) + geometricLift (horizontal i)
  derivative_grid : ∀ i, rational i ∈ realDenominatorGrid derivativeDenominator
  slow_bound : ∀ i,
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * slow i j)‖ ≤ bound / T i

theorem coordinateDerivativeSystem_of_lifts
    {σ E : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup E] [Module ℝ E]
    {m a k H : ℕ} (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (scale : Fin m → ℝ)
    (P : E →ₗ[ℝ] (Fin a → ℝ)) (ha : a ≤ m) (N bound : ℝ)
    (lifts : RationalHorizontalLift k P ha A scale N H)
    (hN : N ≤ bound) (hH : (H : ℝ) ≤ bound)
    (D : ℕ) (hD : 0 < D) (hDb : (D : ℝ) ≤ bound)
    (hderiv : ∀ i, ∃ (s r : Fin m → ℝ) (q : LinearMap.range P),
      Y (Pi.basisFun ℝ σ i) = s + A r + lifts.geometricLift q ∧
      r ∈ realDenominatorGrid D ∧
      ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ bound / T i) :
    Nonempty (CoordinateDerivativeSystem ha T Y A scale bound) := by
  choose s r q heq hgrid hsmall using hderiv
  exact ⟨{
    K := LinearMap.range P
    k := k
    heightBound := H
    height_le := hH
    basisMatrix := lifts.basisMatrix
    basis_height := lifts.basis_height
    independent_rat := lifts.independent_rat
    independent_real := lifts.independent_real
    span_eq := lifts.span_eq
    rationalLift := lifts.rationalLift
    geometricLift := lifts.geometricLift
    factorization := lifts.factorization
    rational_horizontal := lifts.rational_horizontal
    geometric_horizontal := lifts.geometric_horizontal
    norm_scaled := fun x => (lifts.norm_scaled x).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg x))
    liftDenominator := lifts.denominator
    liftDenominator_pos := lifts.denominator_pos
    liftDenominator_le := (Nat.cast_le.mpr lifts.denominator_le).trans hH
    rational_on_basis := lifts.rational_on_basis
    derivativeDenominator := D
    derivativeDenominator_pos := hD
    derivativeDenominator_le := hDb
    slow := s
    rational := r
    horizontal := q
    derivative_eq := heq
    derivative_grid := hgrid
    slow_bound := hsmall
  }⟩

end Erdos3

end

section

namespace Erdos3

open Module

theorem transport_coordinate_derivative_system
    {σ E H : Type*} [Fintype σ] [DecidableEq σ]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]
    {a d : ℕ} (ha : a ≤ d) (b : Basis (Fin d) ℝ E)
    (η : (Fin a → ℝ) ≃ₗ[ℝ] H) (P : E →ₗ[ℝ] H)
    (hP : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = P x)
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] E) (f : E ≃ₗ[ℝ] E)
    (scale : Fin d → ℝ) (bound : ℝ)
    (D : CoordinateDerivativeSystem ha T (b.equivFun.toLinearMap.comp Y)
      (b.equivFun.symm.trans (f.trans b.equivFun)) scale bound) :
    let K := D.K.map η.toLinearMap
    K = Submodule.span ℝ (Set.range (fun j => η ((D.basisMatrix.map (Rat.castHom ℝ)).col j))) ∧
    ∃ R S : K →ₗ[ℝ] E,
      S = f.toLinearMap.comp R ∧
      (∀ x, P (R x) = x.val) ∧ (∀ x, P (S x) = x.val) ∧
      (∀ x, ‖(EuclideanSpace.equiv (Fin d) ℝ).symm
        (fun j => scale j * b.equivFun (S x) j)‖ ≤ bound * ‖η.symm x.val‖) ∧
      (∀ j, ∃ x : K, x.val = η ((D.basisMatrix.map (Rat.castHom ℝ)).col j) ∧
        b.equivFun (R x) ∈ realDenominatorGrid D.liftDenominator) ∧
      ∀ i, ∃ (s r : E) (k : K),
        Y (Pi.basisFun ℝ σ i) = s + f r + S k ∧
        b.equivFun r ∈ realDenominatorGrid D.derivativeDenominator ∧
        ‖(EuclideanSpace.equiv (Fin d) ℝ).symm
          (fun j => scale j * b.equivFun s j)‖ ≤ bound / T i := by
  let K := D.K.map η.toLinearMap
  let eK : D.K ≃ₗ[ℝ] K := η.submoduleMap D.K
  let R : K →ₗ[ℝ] E := b.equivFun.symm.toLinearMap.comp
    (D.rationalLift.comp eK.symm.toLinearMap)
  let S : K →ₗ[ℝ] E := b.equivFun.symm.toLinearMap.comp
    (D.geometricLift.comp eK.symm.toLinearMap)
  have hR (x : K) : b.equivFun (R x) = D.rationalLift (eK.symm x) :=
    b.equivFun.apply_symm_apply _
  have hS (x : K) : b.equivFun (S x) = D.geometricLift (eK.symm x) :=
    b.equivFun.apply_symm_apply _
  have heK (x : K) : (eK.symm x).val = η.symm x.val := rfl
  constructor
  · rw [D.span_eq, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨R, S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    apply b.equivFun.injective
    rw [hS, D.factorization]
    change b.equivFun (f (b.equivFun.symm (D.rationalLift (eK.symm x)))) =
      b.equivFun (f (R x))
    rfl
  · intro x
    rw [← hP, hR]
    have h : (fun i => D.rationalLift (eK.symm x) (Fin.castLE ha i)) =
        (eK.symm x).val := funext (D.rational_horizontal (eK.symm x))
    rw [h, heK, LinearEquiv.apply_symm_apply]
  · intro x
    rw [← hP, hS]
    have h : (fun i => D.geometricLift (eK.symm x) (Fin.castLE ha i)) =
        (eK.symm x).val := funext (D.geometric_horizontal (eK.symm x))
    rw [h, heK, LinearEquiv.apply_symm_apply]
  · intro x
    simp only [hS]
    exact D.norm_scaled (eK.symm x)
  · intro j
    obtain ⟨x, hx, hgrid⟩ := D.rational_on_basis j
    refine ⟨eK x, ?_, ?_⟩
    · change η x.val = _
      rw [hx]
    · rw [hR, LinearEquiv.symm_apply_apply]
      exact hgrid
  · intro i
    refine ⟨b.equivFun.symm (D.slow i), b.equivFun.symm (D.rational i),
      eK (D.horizontal i), ?_, ?_, ?_⟩
    · apply b.equivFun.injective
      simp only [map_add, LinearEquiv.apply_symm_apply, hS, LinearEquiv.symm_apply_apply]
      exact D.derivative_eq i
    · simpa only [LinearEquiv.apply_symm_apply] using D.derivative_grid i
    · simpa only [LinearEquiv.apply_symm_apply] using D.slow_bound i

end Erdos3

end

section

namespace Erdos3

theorem exists_uniform_coordinate_derivative_system
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (a : ℕ) (ha : a ≤ m) (Tmin : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i)
    (p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) ≤ p)
    (hlcap : (l : ℝ) ≤ Real.exp p) (hRcap : R ≤ Real.exp p)
    (hδcap : δ⁻¹ ≤ Real.exp p)
    (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    Nonempty (CoordinateDerivativeSystem ha T Y A scale (Real.exp ((p + 2) ^ 3))) := by
  obtain ⟨lifts, hN, hheight, I, hI, hIcap, hdecomp⟩ :=
    euclideanDerivative_uniform_lattice_extraction T hT scale hscale Y A hA hdiag
      l hl R δ hR hδ H r hr hnorm hdense a ha Tmin hscalehor hblock hfar
      p hp hdim hlcap hRcap hδcap hmin hside
  exact coordinateDerivativeSystem_of_lifts T Y A scale _ ha _ _ lifts hN hheight
    (l * I) (Nat.mul_pos hl hI) hIcap hdecomp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem firstCoefficient_coordinate_system
    {σ ι E : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup E] [Module ℝ E] {d : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (b : Basis (Fin d) ℝ E) (Y : (σ → ℝ) →ₗ[ℝ] E) (f : E ≃ₗ[ℝ] E)
    (hf : ∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
      LinearMap.toMatrix b b f.toLinearMap i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i) (l : ℕ) (hl : 0 < l)
    (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ) (H : Finset (σ → ℤ))
    (r : (σ → ℤ) → Fin d → ℝ) (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T (fun i => monomialScale T (rows i).val.1)
        (b.equivFun.toLinearMap.comp Y) (LinearMap.toMatrix b b f.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin d) : ℕ) : ℝ) ≤ p)
    (hlcap : (l : ℝ) ≤ Real.exp p) (hRcap : R ≤ Real.exp p) (hδcap : δ⁻¹ ≤ Real.exp p)
    (Tmin : ℝ) (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ) (ha : a ≤ d),
      (∀ i, i.val < a ↔ (rows (e i)).val.1 = 0) ∧
      let b' := b.reindex e.symm
      let Y' := b'.equivFun.toLinearMap.comp Y
      let A' := b'.equivFun.symm.trans (f.trans b'.equivFun)
      Nonempty (CoordinateDerivativeSystem ha T Y' A'
        (fun i => monomialScale T (rows (e i)).val.1) (Real.exp ((p + 2) ^ 3))) := by
  obtain ⟨e, a, ha, hzero, haction⟩ := exists_lattice_ready_firstCoefficient_basis ω rows b
  obtain ⟨htri, hdiag, hblock⟩ := haction f hf
  let b' := b.reindex e.symm
  let Y' := b'.equivFun.toLinearMap.comp Y
  let A' := b'.equivFun.symm.trans (f.trans b'.equivFun)
  let scale := fun i => monomialScale T (rows (e i)).val.1
  let r' := fun h => r h ∘ e
  have hY : Y' = (LinearMap.funLeft ℝ ℝ e).comp (b.equivFun.toLinearMap.comp Y) := by
    apply LinearMap.ext
    intro x
    funext i
    exact congrFun (basis_reindex_equivFun b e (Y x)) i
  have hA : LinearMap.toMatrix' A'.toLinearMap =
      (LinearMap.toMatrix b b f.toLinearMap).submatrix e e := by
    rw [basis_coordinate_linearEquiv_matrix]
    ext i j
    exact basis_reindex_toMatrix b e f.toLinearMap i j
  have hscale : ∀ i, 1 ≤ scale i := fun i => one_le_monomialScale T hT _
  have hTmin : 1 ≤ Tmin := (Real.one_le_exp (by positivity)).trans hmin.le
  obtain ⟨hhor, hfar⟩ := sorted_firstCoefficient_scale_bounds ω (rows ∘ e) hzero T Tmin hTmin hside
  have hr' : ∀ h ∈ H, r' h ∈ realDenominatorGrid l :=
    fun h hh => realDenominatorGrid_comp l (r h) (hr h hh) e
  have hnorm' : ∀ h ∈ H, ‖derivativeGridPoint T scale Y' (LinearMap.toMatrix' A'.toLinearMap)
      h (r' h)‖ ≤ R := by
    intro h hh
    rw [hY, hA]
    exact (derivativeGridPoint_reindex_norm T (fun i => monomialScale T (rows i).val.1)
      (b.equivFun.toLinearMap.comp Y) (LinearMap.toMatrix b b f.toLinearMap) e h (r h)).le.trans
        (hnorm h hh)
  refine ⟨e, a, ha, hzero, ?_⟩
  exact exists_uniform_coordinate_derivative_system T hT scale hscale Y' A' htri hdiag
    l hl R δ hR hδ H r' hr' hnorm' hdense a ha Tmin hhor hblock hfar
    p hp hdim hlcap hRcap hδcap hmin hside

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalSpanDerivativeSystem
namespace OAI

section

namespace Erdos3

open Module

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def basisWeightedCoordinates (b : Basis ι ℝ E) (scale : ι → ℝ) :
    E →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi (fun i => scale i • b.coord i)

@[simp] theorem basisWeightedCoordinates_apply (b : Basis ι ℝ E) (scale : ι → ℝ)
    (x : E) (i : ι) :
    basisWeightedCoordinates b scale x i = scale i * b.repr x i := rfl

theorem basisWeightedCoordinates_norm_le_iff [Fintype ι]
    (b : Basis ι ℝ E) (scale : ι → ℝ) (hscale : ∀ i, 0 < scale i)
    {M : ℝ} (hM : 0 ≤ M) (x : E) :
    ‖basisWeightedCoordinates b scale x‖ ≤ M ↔ ∀ i, |b.equivFun x i| ≤ M / scale i := by
  constructor
  · intro hx i
    apply (le_div_iff₀ (hscale i)).mpr
    have hi := (norm_le_pi_norm (basisWeightedCoordinates b scale x) i).trans hx
    simpa only [basisWeightedCoordinates_apply, Real.norm_eq_abs, abs_mul,
      abs_of_pos (hscale i), Basis.equivFun_apply, mul_comm] using hi
  · intro hx
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro i
    have hi := (le_div_iff₀ (hscale i)).mp (hx i)
    simpa only [basisWeightedCoordinates_apply, Real.norm_eq_abs, abs_mul,
      abs_of_pos (hscale i), Basis.equivFun_apply, mul_comm] using hi

theorem basisWeightedCoordinates_operator_bound [Fintype ι]
    (b : Basis ι ℝ E) (scale : ι → ℝ) (hscale : ∀ i, 0 < scale i)
    (A : E →ₗ[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ M, 0 ≤ M → ∀ x, (∀ i, |b.equivFun x i| ≤ M / scale i) →
      ∀ i, |b.equivFun (A x) i| ≤ C * M / scale i) (x : E) :
    ‖basisWeightedCoordinates b scale (A x)‖ ≤ C * ‖basisWeightedCoordinates b scale x‖ := by
  apply (basisWeightedCoordinates_norm_le_iff b scale hscale
    (mul_nonneg hC (norm_nonneg _)) (A x)).mpr
  exact hA _ (norm_nonneg _) x
    ((basisWeightedCoordinates_norm_le_iff b scale hscale (norm_nonneg _) x).mp le_rfl)

theorem basisWeightedCoordinates_norm_le_euclidean [Fintype ι]
    (b : Basis ι ℝ E) (scale : ι → ℝ) (x : E) :
    ‖basisWeightedCoordinates b scale x‖ ≤
      ‖(EuclideanSpace.equiv ι ℝ).symm (basisWeightedCoordinates b scale x)‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le
    ((EuclideanSpace.equiv ι ℝ).symm (basisWeightedCoordinates b scale x)) i

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem transport_coordinate_derivatives_to_rational_span
    {σ E V : Type*} [Fintype σ] [DecidableEq σ]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℚ V]
    {a d : ℕ} (ha : a ≤ d) (b : Basis (Fin d) ℝ E)
    (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] V)) (P : E →ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (hP : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = P x)
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] E) (f : E ≃ₗ[ℝ] E)
    (scale : Fin d → ℝ) (bound : ℝ)
    (D : CoordinateDerivativeSystem ha T (b.equivFun.toLinearMap.comp Y)
      (b.equivFun.symm.trans (f.trans b.equivFun)) scale bound)
    (K : Submodule ℚ V) (bK : Basis (Fin D.k) ℚ K)
    (hspan : D.K.map η.toLinearMap = K.baseChange ℝ)
    (hbasis : ∀ j, (1 : ℝ) ⊗ₜ[ℚ] (bK j : V) = η ((D.basisMatrix.map (Rat.castHom ℝ)).col j)) :
    ∃ S R : (K.baseChange ℝ) →ₗ[ℝ] E,
      S = f.toLinearMap.comp R ∧ P.comp S = (K.baseChange ℝ).subtype ∧
      P.comp R = (K.baseChange ℝ).subtype ∧
      (∀ x, ‖basisWeightedCoordinates b scale (S x)‖ ≤ bound * ‖η.symm x.val‖) ∧
      (∀ j, b.equivFun (R (realSubmoduleBasis K bK j)) ∈ realDenominatorGrid D.liftDenominator) ∧
      ∃ (small rational : σ → E) (k : σ → K.baseChange ℝ),
        (∀ i, Y (Pi.single i 1) = small i + f (rational i) + S (k i)) ∧
        (∀ i, b.equivFun (rational i) ∈ realDenominatorGrid D.derivativeDenominator) ∧
        (∀ i, ‖basisWeightedCoordinates b scale (small i)‖ ≤ bound / T i) := by
  have hraw := transport_coordinate_derivative_system ha b η P hP T Y f scale bound D
  obtain ⟨_, R₀, S₀, hSR₀, hR₀, hS₀, hnorm₀, hgrid₀, hsystem₀⟩ := hraw
  let eK : (K.baseChange ℝ) ≃ₗ[ℝ] D.K.map η.toLinearMap :=
    LinearEquiv.ofEq _ _ hspan.symm
  have heK (x : K.baseChange ℝ) : (eK x).val = x.val :=
    LinearEquiv.coe_ofEq_apply hspan.symm x
  let S := S₀.comp eK.toLinearMap
  let R := R₀.comp eK.toLinearMap
  have hSR : S = f.toLinearMap.comp R := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hSR₀ (eK x)
  have hS : P.comp S = (K.baseChange ℝ).subtype := by
    apply LinearMap.ext
    intro x
    exact (hS₀ (eK x)).trans (heK x)
  have hR : P.comp R = (K.baseChange ℝ).subtype := by
    apply LinearMap.ext
    intro x
    exact (hR₀ (eK x)).trans (heK x)
  refine ⟨S, R, hSR, hS, hR, ?_, ?_, ?_⟩
  · intro x
    have h := (basisWeightedCoordinates_norm_le_euclidean b scale (S x)).trans (hnorm₀ (eK x))
    simpa only [heK] using h
  · intro j
    obtain ⟨x, hx, hg⟩ := hgrid₀ j
    have he : eK (realSubmoduleBasis K bK j) = x := by
      apply Subtype.ext
      exact (heK _).trans ((realSubmoduleBasis_coe K bK j).trans ((hbasis j).trans hx.symm))
    exact (congrArg (fun z => b.equivFun (R₀ z) ∈ realDenominatorGrid D.liftDenominator) he).mpr hg
  · choose small rational k₀ hsystem hgrid hsmall using hsystem₀
    refine ⟨small, rational, fun i => eK.symm (k₀ i), ?_, hgrid, ?_⟩
    · intro i
      have he : S (eK.symm (k₀ i)) = S₀ (k₀ i) :=
        congrArg S₀ (eK.apply_symm_apply (k₀ i))
      have hi : Pi.basisFun ℝ σ i = (Pi.single i 1 : σ → ℝ) := Pi.basisFun_apply ℝ σ i
      exact (congrArg Y hi).symm.trans
        ((hsystem i).trans (congrArg (fun z => small i + f (rational i) + z) he.symm))
    · intro i
      exact (basisWeightedCoordinates_norm_le_euclidean b scale (small i)).trans (hsmall i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastHorizontalFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def realLayerOneLieSection :
    (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) →ₗ[ℝ] (ℝ ⊗[ℚ] L) :=
  (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2)).baseChange ℝ

theorem realLayerOneLieSection_rightInverse (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    (F.layer 2).mkQ.baseChange ℝ (F.realLayerOneLieSection e ω hF x) = x :=
  realSupportedQuotientSection_rightInverse e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x

theorem realLayerOneLieSection_coordinate
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : LayerOneBasisIndex ω) :
    (e.baseChange ℝ).repr (F.realLayerOneLieSection e ω hF x) i =
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr x i :=
  realSupportedQuotientSection_coordinate e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x i

theorem realLayerOneLieSection_coordinate_zero
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : ι) (hi : 2 ≤ ω i) :
    (e.baseChange ℝ).repr (F.realLayerOneLieSection e ω hF x) i = 0 :=
  realSupportedQuotientSection_coordinate_zero e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x i hi

theorem realLayerOneLieSection_norm [Fintype ι] (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    ‖(e.baseChange ℝ).equivFun (F.realLayerOneLieSection e ω hF x)‖ =
      ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x‖ :=
  realSupportedQuotientSection_norm e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x

variable [Fintype σ]

noncomputable def layerOnePolynomialCorrection (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
  F.realification.linearPolynomialGroup (fun i => F.realLayerOneLieSection e ω hF (a i))

theorem layerOnePolynomialCorrection_slow [Fintype ι]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (a i)‖ ≤ M / T i) :
    F.PolynomialSlowBound e (fun _ => 1) T M (F.layerOnePolynomialCorrection e ω hF a) := by
  apply F.polynomialSlowBound_linear e T hT hM
  intro i j
  have h := norm_le_pi_norm ((e.baseChange ℝ).equivFun (F.realLayerOneLieSection e ω hF (a i))) j
  rw [F.realLayerOneLieSection_norm] at h
  exact h.trans (ha i)

theorem layerOnePolynomialCorrection_grid (l : ℕ)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : (fun z : σ × LayerOneBasisIndex ω =>
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid l) :
    F.PolynomialRationalGrid e (fun _ => 1) l (F.layerOnePolynomialCorrection e ω hF a) := by
  apply F.polynomialRationalGrid_linear
  classical
  obtain ⟨v, hv⟩ := ha
  refine ⟨fun z => if hz : 2 ≤ ω z.2 then 0 else v (z.1, ⟨z.2, hz⟩), ?_⟩
  funext z
  change ((if hz : 2 ≤ ω z.2 then 0 else v (z.1, ⟨z.2, hz⟩) : ℤ) : ℝ) =
    (l : ℝ) * (e.baseChange ℝ).repr (F.realLayerOneLieSection e ω hF (a z.1)) z.2
  by_cases hz : 2 ≤ ω z.2
  · rw [dif_pos hz, F.realLayerOneLieSection_coordinate_zero e ω hF _ _ hz]
    simp only [Int.cast_zero, mul_zero]
  · rw [dif_neg hz, F.realLayerOneLieSection_coordinate e ω hF _ ⟨z.2, hz⟩]
    exact congrFun hv (z.1, ⟨z.2, hz⟩)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def realLayerOneCorrection (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.RealAdaptedPolynomialGroup (fun _ : σ => 1) :=
  F.realAdaptedPolynomialGroupLift (fun _ => 1) e ω hF (F.layerOnePolynomialCorrection e ω hF a)

theorem realLayerOneCorrection_realize (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realAdaptedPolynomialGroupHom (fun _ => 1) (F.realLayerOneCorrection e ω hF a) =
      F.layerOnePolynomialCorrection e ω hF a :=
  F.realAdaptedPolynomialGroupHom_lift (fun _ => 1) e ω hF _

theorem realLayerOneCorrection_log (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realAdaptedPolynomialMap (fun _ => 1) (F.realLayerOneCorrection e ω hF a).coord =
      linearPolynomial (fun i => F.realLayerOneLieSection e ω hF (a i)) := by
  have he := congrArg (fun g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group =>
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) (F.realLayerOneCorrection_realize e ω hF a)
  exact he

theorem realLayerOneCorrection_slow [Fintype ι]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (a i)‖ ≤ M / T i) :
    F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M (F.realLayerOneCorrection e ω hF a).coord := by
  apply (F.realAdaptedCoefficientBound_polynomial_iff e ω hF (fun _ => 1) T hT hM _).mpr
  rw [F.realLayerOneCorrection_realize]
  exact F.layerOnePolynomialCorrection_slow e ω hF T hT hM a ha

theorem realLayerOneCorrection_grid (l : ℕ)
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : (fun z : σ × LayerOneBasisIndex ω =>
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid l) :
    F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l (F.realLayerOneCorrection e ω hF a).coord := by
  apply (F.realAdaptedCoefficientGrid_polynomial_iff e ω hF (fun _ => 1) l _).mpr
  rw [F.realLayerOneCorrection_realize]
  exact F.layerOnePolynomialCorrection_grid e ω hF l a ha

omit [Fintype σ] in
theorem realLayerOneProjection_coordinate (x : ℝ ⊗[ℚ] L) (i : LayerOneBasisIndex ω) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).repr ((F.layer 2).mkQ.baseChange ℝ x) i =
      (e.baseChange ℝ).repr x i :=
  baseChange_coordinate_eq e (F.layerOneBasis e ω hF) (F.layer 2).mkQ Subtype.val
    (F.layerOneBasis_repr_mk e ω hF) x i

theorem realAdaptedLogDerivative_constant_unit [DecidableEq σ] (i : σ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) 0 = 0) :
    coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realAdaptedLogDerivative (Pi.single i 1) x)) 0 =
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) (Finsupp.single i 1) := by
  have he := congrArg
    (fun q : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => coefficients q.val 0)
    (F.realAdaptedLogDerivative_tensor (Pi.single i 1) x)
  exact he.trans (F.realification.adaptedLogDerivative_constant_unit i
    (F.realAdaptedPolynomialTensor (fun _ => 1) x) hx)

include e ω hF in
theorem realFirstCoefficientDirectionMap_horizontal_unit [DecidableEq σ] (i : σ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) 0 = 0) :
    F.realFirstCoefficientHorizontal (fun _ => 1)
      (F.realFirstCoefficientDirectionMap x (Pi.single i 1)) =
      (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) (Finsupp.single i 1)) := by
  classical
  have hunit : (Pi.single i (1 : ℝ)) = (fun j => (((Pi.single i (1 : ℚ) : σ → ℚ) j) : ℝ)) := by
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  apply ((F.layerOneBasis e ω hF).baseChange ℝ).repr.injective
  ext j
  rw [F.realFirstCoefficientHorizontal_coordinates e ω hF, hunit,
    F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientBasis_polynomial_coordinate]
  change (e.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
    (F.realAdaptedLogDerivative (Pi.single i 1) x)) 0) j.val = _
  rw [F.realAdaptedLogDerivative_constant_unit i x hx, F.realLayerOneProjection_coordinate]

theorem realLayerOneCorrection_horizontal_derivative [DecidableEq σ]
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (i : σ) :
    F.realFirstCoefficientHorizontal (fun _ => 1)
      (F.realFirstCoefficientDirectionMap (F.realLayerOneCorrection e ω hF a).coord (Pi.single i 1)) =
      a i := by
  have hz : coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF a).coord) 0 = 0 := by
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  rw [F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i _ hz,
    F.realLayerOneCorrection_log, coefficients_linearPolynomial_single,
    F.realLayerOneLieSection_rightInverse]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace VectorPolynomial

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def layerOneGradedMap : (L ⧸ F.layer 2) →ₗ[ℚ] F.AssociatedGraded :=
  (F.gradedPieceProjection e ω hF 1).comp
    (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2))

theorem layerOneGradedMap_mk (x : L) :
    F.layerOneGradedMap e ω hF ((F.layer 2).mkQ x) = F.gradedPieceProjection e ω hF 1 x := by
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext i
  change (F.associatedGradedBasis e ω hF).repr
    (F.gradedPieceProjection e ω hF 1
      (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2) ((F.layer 2).mkQ x))) i = _
  rw [F.gradedPieceProjection_coordinate, F.gradedPieceProjection_coordinate]
  by_cases hi : ω i = 1
  · rw [if_pos hi, if_pos hi]
    have hni : ¬2 ≤ ω i := by omega
    exact (supportedQuotientSection_coordinate e (F.layer 2) {i | 2 ≤ ω i}
      (hF 2) ((F.layer 2).mkQ x) ⟨i, hni⟩).trans
        (supportedQuotientBasis_repr_mk e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x ⟨i, hni⟩)
  · rw [if_neg hi, if_neg hi]

theorem realLayerOneGradedMap_mk (x : ℝ ⊗[ℚ] L) :
    (F.layerOneGradedMap e ω hF).baseChange ℝ ((F.layer 2).mkQ.baseChange ℝ x) =
      (F.gradedPieceProjection e ω hF 1).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, F.layerOneGradedMap_mk]

theorem realLayerOneGradedMap_section (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    (F.layerOneGradedMap e ω hF).baseChange ℝ x =
      (F.gradedPieceProjection e ω hF 1).baseChange ℝ (F.realLayerOneLieSection e ω hF x) := by
  change ((F.gradedPieceProjection e ω hF 1).comp
    (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i} (hF 2))).baseChange ℝ x = _
  rw [LinearMap.baseChange_comp]
  rfl

noncomputable def layerOneGradedSubmodule (U : LieSubalgebra ℚ F.AssociatedGraded) :
    Submodule ℚ (L ⧸ F.layer 2) :=
  U.toSubmodule.comap (F.layerOneGradedMap e ω hF)

theorem mem_realLayerOneGradedSubmodule (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    x ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ ↔
      (F.layerOneGradedMap e ω hF).baseChange ℝ x ∈ realificationLieSubalgebra U := by
  rw [layerOneGradedSubmodule, realification_comap]
  rfl

theorem mem_realLayerOneGradedSubmodule_mk (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : ℝ ⊗[ℚ] L) :
    (F.layer 2).mkQ.baseChange ℝ x ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ ↔
      (F.gradedPieceProjection e ω hF 1).baseChange ℝ x ∈ realificationLieSubalgebra U := by
  rw [F.mem_realLayerOneGradedSubmodule, F.realLayerOneGradedMap_mk]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem realLayerOneCorrection_mem_pointwise (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) :
    F.realExtendedSymbolMap (fun _ => 1) (F.realLayerOneCorrection e ω hF a).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ => 1) U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ => 1) U _).mpr
  intro α
  rw [← F.realSymbolOfPolynomial_realAdaptedPolynomialMap e ω hF,
    F.realGradedSymbolPolynomial_coefficient_of_polynomial,
    F.realLayerOneCorrection_log]
  by_cases hα : ∃ i, Finsupp.single i 1 = α
  · obtain ⟨i, rfl⟩ := hα
    rw [coefficients_linearPolynomial_single]
    simp only [Finsupp.weight_single, one_smul]
    rw [← F.realLayerOneGradedMap_section]
    exact (F.mem_realLayerOneGradedSubmodule e ω hF U (a i)).mp (ha i)
  · rw [coefficients_linearPolynomial_of_ne _ α (by simpa only [not_exists] using hα), map_zero]
    exact (realificationLieSubalgebra U).zero_mem

omit [Fintype σ] in
theorem pointwise_horizontal_coefficient_mem
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.realExtendedSymbolMap (fun _ => 1) x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ => 1) U)) (i : σ) :
    (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) (Finsupp.single i 1)) ∈
        (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ := by
  apply (F.mem_realLayerOneGradedSubmodule_mk e ω hF U _).mpr
  have h := (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ => 1) U _).mp hx
    (Finsupp.single i 1)
  rw [← F.realSymbolOfPolynomial_realAdaptedPolynomialMap e ω hF,
    F.realGradedSymbolPolynomial_coefficient_of_polynomial] at h
  simpa only [Finsupp.weight_single, one_smul] using h

theorem pointwise_horizontal_derivative_mem [DecidableEq σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.realExtendedSymbolMap (fun _ => 1) x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ => 1) U))
    (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) 0 = 0) (i : σ) :
    F.realFirstCoefficientHorizontal (fun _ => 1)
      (F.realFirstCoefficientDirectionMap x (Pi.single i 1)) ∈
        (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ := by
  rw [F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i x hzero]
  exact F.pointwise_horizontal_coefficient_mem e ω hF U x hx i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

noncomputable def realFastCoefficientDirectionMap
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    (σ → ℝ) →ₗ[ℝ] F.RealFastCoefficientModule (fun _ => 1) (fun _ => Nat.zero_lt_one) U :=
  (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ.comp
      (F.realFirstCoefficientDirectionMap g.coord)

variable {ι : Type*} (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFastCoefficientDirectionMap_mul
    (g h : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) (v : σ → ℝ) :
    F.realFastCoefficientDirectionMap U (g * h).val v =
      F.realFastCoefficientDirectionMap U g.val v +
        F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U g
          (F.realFastCoefficientDirectionMap U h.val v) := by
  change (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
      (F.realFirstCoefficientDirectionMap (g.val * h.val).coord v) = _
  rw [F.realFirstCoefficientDirectionMap_mul e ω hF, map_add]
  rfl

theorem realFastCoefficientDirectionMap_triple
    (a b c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) (v : σ → ℝ) :
    F.realFastCoefficientDirectionMap U (a * b * c).val v =
      F.realFastCoefficientDirectionMap U a.val v +
        F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a
          (F.realFastCoefficientDirectionMap U b.val v) +
        F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a
          (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U b
            (F.realFastCoefficientDirectionMap U c.val v)) := by
  exact linear_cocycle_triple (F.realFastCoefficientAction (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) U)
    (fun g => F.realFastCoefficientDirectionMap U g.val v)
    (fun g h => F.realFastCoefficientDirectionMap_mul U e ω hF g h v) a b c

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFastCoefficient_remove_derivative
    (a b c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) (v : σ → ℝ)
    (small rational z : F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U)
    (hsystem : F.realFastCoefficientDirectionMap U (a * b * c).val v = small +
      F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U (a * b * c) rational + z) :
    F.realFastCoefficientDirectionMap U b.val v =
      (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm
        (small - F.realFastCoefficientDirectionMap U a.val v) +
      F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U b
        (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U c rational -
          F.realFastCoefficientDirectionMap U c.val v) +
      (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm z := by
  let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
  apply linear_derivative_remove (ρ a) (ρ c) (ρ (a * b * c)) (ρ b)
    (linear_action_triple ρ a b c)
    _ _ _ _ small rational z
    (F.realFastCoefficientDirectionMap_triple U e ω hF a b c v) hsystem

omit e ω hF [Fintype σ] in
theorem realFastCoefficient_remove_lifts {K : Type*} [AddCommGroup K] [Module ℝ K]
    (a b c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U)
    (S R : K →ₗ[ℝ] F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U)
    (hSR : S = (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U (a * b * c)).toLinearMap.comp R) :
    (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm.toLinearMap.comp S =
      (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U b).toLinearMap.comp
        ((F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U c).toLinearMap.comp R) := by
  let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
  exact linear_lift_remove (ρ a) (ρ c) (ρ (a * b * c)) (ρ b)
    (linear_action_triple ρ a b c) S R hSR

omit [Fintype σ] in
theorem realFastCoefficient_remove_horizontal_lifts {K : Type*}
    [AddCommGroup K] [Module ℝ K]
    (a c : F.realFastDiagonalSubgroup (fun _ : σ => 1) U)
    (S R : K →ₗ[ℝ] F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U)
    (I : K →ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
    (hS : (F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).comp S = I)
    (hR : (F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).comp R = I) :
    let P := F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
    P.comp ((F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U a).symm.toLinearMap.comp S) = I ∧
      P.comp ((F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U c).toLinearMap.comp R) = I := by
  exact horizontal_lift_remove _ _ _
    (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) U e ω hF a)
    (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) U e ω hF c) S R I hS hR

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def realPointwisePolynomialSubgroup : Subgroup (F.RealAdaptedPolynomialGroup w) :=
  (show Subgroup (F.RealPolynomialSymbolGroup w) from
    realLieSubgroup (realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF w U))).comap
      ((F.realPolynomialSymbolHom e ω hF w).comp (F.realAdaptedPolynomialGroupHom w))

theorem mem_realPointwisePolynomialSubgroup (g : F.RealAdaptedPolynomialGroup w) :
    g ∈ F.realPointwisePolynomialSubgroup e ω hF w U ↔
      F.realExtendedSymbolMap w g.coord ∈
        realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF w U) := by
  change F.realSymbolOfPolynomial e ω hF w (F.realAdaptedPolynomialMap w g.coord) ∈
    realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF w U) ↔ _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap]

omit w in
theorem realLayerOneCorrection_mem_pointwiseSubgroup [Fintype σ]
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) :
    F.realLayerOneCorrection e ω hF a ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U := by
  apply (F.mem_realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U _).mpr
  exact F.realLayerOneCorrection_mem_pointwise e ω hF U a ha

end Erdos3.NilpotentLieFiltration

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem adaptedReducedRealSymbolHom_coord (g : F.RealAdaptedPolynomialGroup w) :
    (F.adaptedReducedRealSymbolHom w g).coord =
      (F.quotientTopSymbolMap w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w g.coord) := by
  change ((F.quotientTopSymbolMap w).toLinearMap.comp
    (F.polynomialSymbolMap w).toLinearMap).baseChange ℝ g.coord = _
  rw [LinearMap.baseChange_comp]
  rfl

theorem realPointwisePolynomialSubgroup_le_fast
    (hU : (F.symbolPointwiseSubalgebra e ω hF w U).map (F.quotientTopSymbolMap w) ≤
      F.reducedSquareFastDiagonalSubalgebra w W) :
    F.realPointwisePolynomialSubgroup e ω hF w U ≤ F.realFastDiagonalSubgroup w W := by
  intro g hg
  have hs := (F.mem_realPointwisePolynomialSubgroup e ω hF w U g).mp hg
  apply (F.mem_realFastDiagonalSubgroup w W g).mpr
  rw [F.adaptedReducedRealSymbolHom_coord]
  have hm : (F.quotientTopSymbolMap w).toLinearMap.baseChange ℝ
      (F.realExtendedSymbolMap w g.coord) ∈
      ((F.symbolPointwiseSubalgebra e ω hF w U).toSubmodule.map
        (F.quotientTopSymbolMap w).toLinearMap).baseChange ℝ := by
    rw [realification_map]
    exact ⟨_, hs, rfl⟩
  exact Submodule.baseChange_mono ℝ hU hm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

theorem realAdaptedCoefficientBound_inv {σ ι L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (T : σ → ℝ) (M : ℝ) (g : F.RealAdaptedPolynomialGroup w)
    (hg : F.RealAdaptedCoefficientBound e ω hF w T M g.coord) :
    F.RealAdaptedCoefficientBound e ω hF w T M (g⁻¹).coord := by
  simpa only [RealAdaptedCoefficientBound, coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hg

theorem realFastCoefficientAction_symm {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.realFastDiagonalSubgroup w U) (x : F.RealFastCoefficientModule w hw U) :
    (F.realFastCoefficientAction w hw U g).symm x = F.realFastCoefficientAction w hw U g⁻¹ x :=
  congrArg (fun A : F.RealFastCoefficientModule w hw U ≃ₗ[ℝ] F.RealFastCoefficientModule w hw U => A x)
    (map_inv (F.realFastCoefficientAction w hw U) g).symm

theorem fastCoefficientAdjoint_norm_bound {σ ι κ L : Type*}
    [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (b : Basis κ ℝ (F.RealFastCoefficientModule w hw U))
    (R : (κ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw
      (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y)
    (rows : κ → FirstCoefficientIndex w ω) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (Cproj Clift D : ℝ) (hCproj : 0 ≤ Cproj) (hClift : 0 ≤ Clift) (hD : 0 ≤ D)
    (hproj : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      ∀ i, |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
        (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
          Cproj * M / monomialScale T (rows i).val.1)
    (hlift : ∀ M, 0 ≤ M → ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
      F.FirstCoefficientSlowBound e ω hF w T (Clift * M) (R y))
    (g : F.realFastDiagonalSubgroup w U)
    (had : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF w T M x →
      F.FirstCoefficientSlowBound e ω hF w T (D * M) (F.realFirstCoefficientAdjoint w g.val x))
    (x : F.RealFastCoefficientModule w hw U) :
    ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
        (F.realFastCoefficientAction w hw U g x)‖ ≤
      (Cproj * D * Clift) * ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) x‖ := by
  apply basisWeightedCoordinates_operator_bound b (fun i => monomialScale T (rows i).val.1)
    (fun i => monomialScale_pos T hT _) (F.realFastCoefficientAction w hw U g).toLinearMap
    (Cproj * D * Clift) (mul_nonneg (mul_nonneg hCproj hD) hClift)
  intro M hM y hy
  exact F.fastCoefficientAdjoint_weighted_bound e ω hF w hw U b R hR rows T
    Cproj Clift D hClift hD hproj hlift g had hM y hy

theorem fastCoefficientDirection_norm_bound {σ ι κ L : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (Cproj D : ℝ) (hCproj : 0 ≤ Cproj) (hD : 0 ≤ D)
    (hproj : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
      ∀ j, |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) j| ≤
          Cproj * M / monomialScale T (rows j).val.1)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hg : ∀ i, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (D / T i)
      (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1))) (i : σ) :
    ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1)
        (F.realFastCoefficientDirectionMap U g (Pi.single i 1))‖ ≤ Cproj * D / T i := by
  apply (basisWeightedCoordinates_norm_le_iff b (fun j => monomialScale T (rows j).val.1)
    (fun j => monomialScale_pos T hT _) (div_nonneg (mul_nonneg hCproj hD) (hT i).le) _).mpr
  intro j
  have h := hproj (D / T i) (div_nonneg hD (hT i).le) _ (hg i) j
  change |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
      (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1))) j| ≤ _
  simpa only [mul_div_assoc] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
    (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)

noncomputable def realFastLayerOneCorrection (a : σ → 𝓗)
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) : 𝓖 :=
  ⟨F.realLayerOneCorrection e ω hF a,
    F.realPointwisePolynomialSubgroup_le_fast e ω hF (fun _ => 1) U W hU
      (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U a ha)⟩

theorem realFastLayerOneCorrection_horizontal [DecidableEq σ] (a : σ → 𝓗)
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) (i : σ) :
    𝓟 (F.realFastCoefficientDirectionMap W
      (F.realFastLayerOneCorrection e ω hF U W hU a ha).val (Pi.single i 1)) = a i := by
  change F.realFirstCoefficientHorizontal (fun _ => 1)
    (F.realFirstCoefficientDirectionMap (F.realLayerOneCorrection e ω hF a).coord (Pi.single i 1)) = _
  exact F.realLayerOneCorrection_horizontal_derivative e ω hF a i

include hU in
theorem realFast_horizontal_normalization [DecidableEq σ]
    (B : 𝓖) (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔)
    (hSR : S = (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W B).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, F.realFastCoefficientDirectionMap W B.val (Pi.single i 1) = small i +
      F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W B (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ)
    (hrational : ∀ i, 𝓟 (rational i) ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ)
    (hk : ∀ i, (k i).val ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) :
    ∃ a B' c : 𝓖,
      a.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (small i)) ∧
      c.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (rational i)) ∧
      (B.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U →
        B'.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U) ∧
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B'.val.coord) 0 =
        coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 ∧
      (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 = 0 →
        ∀ i, (F.layer 2).mkQ.baseChange ℝ
          (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B'.val.coord) (Finsupp.single i 1)) =
          (k i).val) ∧
      let ρ := F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W
      let Y := fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W g.val (Pi.single i 1)
      let S' := (ρ a).symm.toLinearMap.comp S
      let R' := (ρ c).toLinearMap.comp R
      let small' := fun i => (ρ a).symm (small i - Y a i)
      let rational' := fun i => ρ c (rational i) - Y c i
      a * B' * c = B ∧ S' = (ρ B').toLinearMap.comp R' ∧
        (𝓟).comp S' = K.subtype ∧ (𝓟).comp R' = K.subtype ∧
        ∀ i, Y B' i = small' i + ρ B' (rational' i) + S' (k i) ∧
          𝓟 (small' i) = 0 ∧ 𝓟 (rational' i) = 0 ∧ 𝓟 (Y B' i) = (k i).val ∧
          𝓟 (Y B' i) ∈ (F.layerOneGradedSubmodule e ω hF U).baseChange ℝ ⊓ K := by
  let a := F.realFastLayerOneCorrection e ω hF U W hU (fun i => 𝓟 (small i)) hsmall
  let c := F.realFastLayerOneCorrection e ω hF U W hU (fun i => 𝓟 (rational i)) hrational
  let ρ := F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) W
  let Y := fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W g.val (Pi.single i 1)
  have hdata := cocycle_horizontal_normalization ρ Y
    (fun g h i => F.realFastCoefficientDirectionMap_mul W e ω hF g h (Pi.single i 1))
    𝓟 (F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one) W e ω hF)
    ((F.layerOneGradedSubmodule e ω hF U).baseChange ℝ) K B a c S R hSR hS hR small rational k hsystem
    (fun i => F.realFastLayerOneCorrection_horizontal e ω hF U W hU _ hsmall i)
    (fun i => F.realFastLayerOneCorrection_horizontal e ω hF U W hU _ hrational i) hk
  have hpointwise : B.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U →
      (a⁻¹ * B * c⁻¹).val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) U := by
    intro hB
    let G := F.realPointwisePolynomialSubgroup e ω hF (fun _ : σ => 1) U
    exact G.mul_mem (G.mul_mem (G.inv_mem
      (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U _ hsmall)) hB)
        (G.inv_mem (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF U _ hrational))
  have hzeroa : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) a.val.coord) 0 = 0 := by
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF _).coord) 0 = 0
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  have hzeroc : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) c.val.coord) 0 = 0 := by
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      (F.realLayerOneCorrection e ω hF _).coord) 0 = 0
    rw [F.realLayerOneCorrection_log, coefficients_linearPolynomial_zero]
  have hconst := F.realAdapted_factor_middle_constant (fun _ => 1) B.val a.val
    (a⁻¹ * B * c⁻¹).val c.val (congrArg Subtype.val hdata.1) hzeroa hzeroc
  have hlinear : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.val.coord) 0 = 0 →
      ∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) (a⁻¹ * B * c⁻¹).val.coord)
          (Finsupp.single i 1)) = (k i).val := by
    intro hz i
    have hd := F.realFirstCoefficientDirectionMap_horizontal_unit e ω hF i
      (a⁻¹ * B * c⁻¹).val.coord (hconst.trans hz)
    have he : 𝓟 (Y (a⁻¹ * B * c⁻¹) i) = (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) (a⁻¹ * B * c⁻¹).val.coord)
          (Finsupp.single i 1)) := hd
    exact he.symm.trans (hdata.2.2.2.2 i).2.2.2.1
  exact ⟨a, a⁻¹ * B * c⁻¹, c, rfl, rfl, hpointwise, hconst, hlinear, hdata⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF U)
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W (Subtype.val g) (Pi.single i 1))

theorem realFast_bounded_horizontal_normalization
    (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
      (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)
    (g : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g i = small i + ρ g (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) ∈ 𝓤) (hrational : ∀ i, 𝓟 (rational i) ∈ 𝓤)
    (hk : ∀ i, (k i).val ∈ 𝓤)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, ‖cH (𝓟 (small i))‖ ≤ M / T i)
    (l : ℕ) (hgrid : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l) :
    ∃ a g' q : 𝓖,
      a.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (small i)) ∧
      q.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (rational i)) ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M a.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l q.val.coord ∧
      coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) 0 = 0 ∧
      (∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) (Finsupp.single i 1)) =
          (k i).val) ∧
      let S' := (ρ a).symm.toLinearMap.comp S
      let R' := (ρ q).toLinearMap.comp R
      let small' := fun i => (ρ a).symm (small i - Y a i)
      let rational' := fun i => ρ q (rational i) - Y q i
      a * g' * q = g ∧ S' = (ρ g').toLinearMap.comp R' ∧
        (𝓟).comp S' = K.subtype ∧ (𝓟).comp R' = K.subtype ∧
        ∀ i, Y g' i = small' i + ρ g' (rational' i) + S' (k i) ∧
          𝓟 (small' i) = 0 ∧ 𝓟 (rational' i) = 0 ∧ 𝓟 (Y g' i) = (k i).val ∧
          𝓟 (Y g' i) ∈ 𝓤 ⊓ K := by
  classical
  have h := F.realFast_horizontal_normalization (σ := σ) (ι := ι) e ω hF U W hU
    g K S R hSR hS hR small rational k hsystem hsmall hrational hk
  obtain ⟨a, g', q, ha, hq, _, hconst, hlinear, hnew⟩ := h
  refine ⟨a, g', q, ha, hq, ?_, ?_, hconst.trans hzero, hlinear hzero, hnew⟩
  · rw [ha]
    exact F.realLayerOneCorrection_slow e ω hF T hT hM (fun i => 𝓟 (small i)) hbound
  · rw [hq]
    apply F.realLayerOneCorrection_grid e ω hF
    choose z hz using hgrid
    refine ⟨fun x => z x.1 x.2, ?_⟩
    funext x
    exact congrFun (hz x.1) x.2

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ F.AssociatedGraded)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) W
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) W)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF U)
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) W
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap W (Subtype.val g) (Pi.single i 1))

theorem realFast_controlled_horizontal_factorization
    (hU : (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) U).map
      (F.quotientTopSymbolMap (fun _ => 1)) ≤ F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) W)
    (g₀ : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g₀.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g₀).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g₀ i = small i + ρ g₀ (rational i) + S (k i))
    (hsmall : ∀ i, 𝓟 (small i) ∈ 𝓤) (hrational : ∀ i, 𝓟 (rational i) ∈ 𝓤)
    (hk : ∀ i, (k i).val ∈ 𝓤)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, ‖cH (𝓟 (small i))‖ ≤ M / T i)
    (l : ℕ) (hgrid : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l) :
    ∃ a g c : 𝓖, a * g * c = g₀ ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T M a.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l c.val.coord ∧
      (∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) (Finsupp.single i 1)) =
          (k i).val) ∧
      (∀ i, 𝓟 (Y a i) = 𝓟 (small i)) ∧ (∀ i, 𝓟 (Y c i) = 𝓟 (rational i)) := by
  have hnorm := F.realFast_bounded_horizontal_normalization e ω hF U W hU
    g₀ hzero K S R hSR hS hR small rational k hsystem hsmall hrational hk T hT M hM hbound l hgrid
  obtain ⟨a, g, c, ha, hc, habound, hcgrid, _, hlinear, hnew⟩ := hnorm
  refine ⟨a, g, c, hnew.1, habound, hcgrid, hlinear, ?_, ?_⟩
  · intro i
    change F.realFirstCoefficientHorizontal (fun _ : σ => 1)
      (F.realFirstCoefficientDirectionMap a.val.coord (Pi.single i 1)) = _
    rw [ha]
    exact F.realLayerOneCorrection_horizontal_derivative e ω hF (fun j => 𝓟 (small j)) i
  · intro i
    change F.realFirstCoefficientHorizontal (fun _ : σ => 1)
      (F.realFirstCoefficientDirectionMap c.val.coord (Pi.single i 1)) = _
    rw [hc]
    exact F.realLayerOneCorrection_horizontal_derivative e ω hF (fun j => 𝓟 (rational j)) i

end Erdos3.NilpotentLieFiltration

end

end OAI

end


