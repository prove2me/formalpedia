-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
-- name    : GroundTheory_HeightsAndTheta_Heights_HermitianLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:29.037798+00:00
-- url     : https://prove2.me/theorems/5283f41a-6e96-428e-a914-d6f82c9cc2ac
-- title:
--   Hermitian Lattice
-- statement:
--   Definitions and structural lemmas for Hermitian Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct
noncomputable section
def ComplexAt {K : Type*} [Field K] (_σ : K →+* ℂ) : Type := ℂ
namespace ComplexAt
variable {K : Type*} {_ : Field K} (σ : K →+* ℂ)
instance : CommRing (ComplexAt σ) := inferInstanceAs (CommRing ℂ)
instance : Algebra ℂ (ComplexAt σ) := inferInstanceAs (Algebra ℂ ℂ)
def ofComplex : ℂ ≃ₐ[ℂ] ComplexAt σ := AlgEquiv.refl
instance : Algebra (𝓞 K) (ComplexAt σ) :=
  ((ofComplex σ).toRingHom.comp (σ.comp (algebraMap (𝓞 K) K))).toAlgebra
theorem smul_def (a : 𝓞 K) (z : ComplexAt σ) : a • z = ofComplex σ (σ (a : K)) * z := rfl
theorem complex_smul_def (c : ℂ) (z : ComplexAt σ) : c • z = ofComplex σ c * z := rfl
instance : SMulCommClass (𝓞 K) ℂ (ComplexAt σ) where
  smul_comm a c z := by
    rw [smul_def, complex_smul_def, complex_smul_def, smul_def, mul_left_comm]
instance : SMulCommClass ℂ (𝓞 K) (ComplexAt σ) := SMulCommClass.symm _ _ _
def conj : ComplexAt σ →+* ComplexAt (conjugate σ) :=
  (ofComplex (conjugate σ)).toRingHom.comp ((starRingEnd ℂ).comp (ofComplex σ).symm.toRingHom)
theorem conj_ofComplex (z : ℂ) :
    conj σ (ofComplex σ z) = ofComplex (conjugate σ) (starRingEnd ℂ z) := rfl
def conjLinear : ComplexAt σ →ₗ[𝓞 K] ComplexAt (conjugate σ) where
  toFun := conj σ
  map_add' := map_add _
  map_smul' a z := by
    rw [smul_def, map_mul, RingHom.id_apply, smul_def, conj_ofComplex]
    rfl
end ComplexAt
open ComplexAt
variable {K : Type*} [Field K]
abbrev Fibre (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E] : Type _ :=
  ComplexAt σ ⊗[𝓞 K] E
section Fibre
variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]
def conjMap : Fibre σ E →ₗ[𝓞 K] Fibre (conjugate σ) E :=
  TensorProduct.map (conjLinear σ) LinearMap.id
variable {σ E}
@[simp]
theorem conjMap_tmul (z : ComplexAt σ) (e : E) : conjMap σ E (z ⊗ₜ e) = conj σ z ⊗ₜ e := rfl
end Fibre
structure HermitianMetric (K : Type*) [Field K] [NumberField K] (E : Type*) [AddCommGroup E]
    [Module (𝓞 K) E] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] where

  form : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (Fibre σ E)

  form_conj : ∀ (σ : K →+* ℂ) (x y : Fibre σ E),
    (form (conjugate σ)).inner (conjMap σ E x) (conjMap σ E y) = starRingEnd ℂ ((form σ).inner x y)
structure HermitianBundle.{u} (K : Type*) [Field K] [NumberField K] where

  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module (𝓞 K) carrier]
  [instFinite : Module.Finite (𝓞 K) carrier]
  [instProjective : Module.Projective (𝓞 K) carrier]

  metric : HermitianMetric K carrier
attribute [instance] HermitianBundle.instAddCommGroup HermitianBundle.instModule
  HermitianBundle.instFinite HermitianBundle.instProjective
@[instance_reducible]
def coreOfInjective {𝕜 V W : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] (f : V →ₗ[𝕜] W)
    (hf : Function.Injective f) : InnerProductSpace.Core 𝕜 V where
  inner x y := inner 𝕜 (f x) (f y)
  conj_inner_symm x y := inner_conj_symm (f x) (f y)
  re_inner_nonneg x := inner_self_nonneg
  add_left x y z := by simp only [map_add, inner_add_left]
  smul_left x y r := by simp only [map_smul, inner_smul_left]
  definite x h := hf (by rw [map_zero]; exact inner_self_eq_zero.mp h)
theorem coreOfInjective_inner {𝕜 V W : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] (f : V →ₗ[𝕜] W)
    (hf : Function.Injective f) (x y : V) :
    (coreOfInjective f hf).inner x y = inner 𝕜 (f x) (f y) := rfl
section Examples
variable (K : Type*) [Field K] [NumberField K]
def integersCoord (σ : K →+* ℂ) : Fibre σ (𝓞 K) ≃ₗ[ℂ] ℂ :=
  ((AlgebraTensorModule.rid (𝓞 K) (ComplexAt σ) (ComplexAt σ)).restrictScalars ℂ).trans
    (ofComplex σ).symm.toLinearEquiv
variable {K}
omit [NumberField K] in
theorem integersCoord_tmul (σ : K →+* ℂ) (z : ComplexAt σ) (a : 𝓞 K) :
    integersCoord K σ (z ⊗ₜ a) = σ (a : K) * (ofComplex σ).symm z := rfl
omit [NumberField K] in
theorem integersCoord_conjMap (σ : K →+* ℂ) (x : Fibre σ (𝓞 K)) :
    integersCoord K (conjugate σ) (conjMap σ (𝓞 K) x) = starRingEnd ℂ (integersCoord K σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z a =>
    rw [conjMap_tmul, integersCoord_tmul, integersCoord_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
variable (K)
def HermitianMetric.integers : HermitianMetric K (𝓞 K) where
  form σ := coreOfInjective (integersCoord K σ).toLinearMap (integersCoord K σ).injective
  form_conj σ x y := by
    simp only [coreOfInjective_inner, LinearEquiv.coe_coe, integersCoord_conjMap,
      RCLike.inner_apply, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
def standardCoord (σ : K →+* ℂ) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Fibre σ (ι → 𝓞 K) ≃ₗ[ℂ] EuclideanSpace ℂ ι :=
  ((piScalarRight (𝓞 K) (ComplexAt σ) (ComplexAt σ) ι).restrictScalars ℂ).trans
    ((LinearEquiv.piCongrRight fun _ ↦ (ofComplex σ).symm.toLinearEquiv).trans
      (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm)
variable {K}
omit [NumberField K] in
theorem standardCoord_tmul (σ : K →+* ℂ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (z : ComplexAt σ) (v : ι → 𝓞 K) (i : ι) :
    standardCoord K σ ι (z ⊗ₜ v) i = σ (v i : K) * (ofComplex σ).symm z := rfl
omit [NumberField K] in
theorem standardCoord_conjMap (σ : K →+* ℂ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (x : Fibre σ (ι → 𝓞 K)) (i : ι) :
    standardCoord K (conjugate σ) ι (conjMap σ (ι → 𝓞 K) x) i =
      starRingEnd ℂ (standardCoord K σ ι x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, PiLp.zero_apply]
  | tmul z v =>
    rw [conjMap_tmul, standardCoord_tmul, standardCoord_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, PiLp.add_apply, hx, hy, map_add, PiLp.add_apply, map_add]
variable (K)
def HermitianMetric.standard (ι : Type*) [Fintype ι] [DecidableEq ι] :
    HermitianMetric K (ι → 𝓞 K) where
  form σ := coreOfInjective (standardCoord K σ ι).toLinearMap (standardCoord K σ ι).injective
  form_conj σ x y := by
    simp only [coreOfInjective_inner, LinearEquiv.coe_coe, PiLp.inner_apply, RCLike.inner_apply,
      standardCoord_conjMap, map_sum, map_mul, Complex.conj_conj]
theorem HermitianMetric.standard_inner (ι : Type*) [Fintype ι] [DecidableEq ι] (σ : K →+* ℂ)
    (x y : Fibre σ (ι → 𝓞 K)) :
    ((HermitianMetric.standard K ι).form σ).inner x y =
      ∑ i, starRingEnd ℂ (standardCoord K σ ι x i) * standardCoord K σ ι y i := by
  change inner ℂ (standardCoord K σ ι x) (standardCoord K σ ι y) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
def HermitianBundle.integers : HermitianBundle K := ⟨𝓞 K, HermitianMetric.integers K⟩
def HermitianBundle.standard (n : ℕ) : HermitianBundle K :=
  ⟨Fin n → 𝓞 K, HermitianMetric.standard K (Fin n)⟩
end Examples
abbrev GaussianField : Type := CyclotomicField 4 ℚ
example : NumberField GaussianField := inferInstance
def ratIntegers : HermitianBundle ℚ := HermitianBundle.integers ℚ
def ratStandard (n : ℕ) : HermitianBundle ℚ := HermitianBundle.standard ℚ n
def gaussianIntegers : HermitianBundle GaussianField := HermitianBundle.integers GaussianField
def gaussianStandard (n : ℕ) : HermitianBundle GaussianField :=
  HermitianBundle.standard GaussianField n
theorem HermitianMetric.standard_inner_single (K : Type*) [Field K] [NumberField K] (n : ℕ)
    (σ : K →+* ℂ) (i : Fin n) :
    ((HermitianMetric.standard K (Fin n)).form σ).inner (1 ⊗ₜ Pi.single i 1) (1 ⊗ₜ Pi.single i 1)
      = 1 := by
  rw [HermitianMetric.standard_inner, Finset.sum_eq_single i]
  · simp only [standardCoord_tmul, Pi.single_eq_same, map_one]
    show starRingEnd ℂ (1 * 1) * (1 * 1) = 1
    simp
  · intro j _ hj
    simp [standardCoord_tmul, Pi.single_eq_of_ne hj]
  · simp
def ratEmbedding : ℚ →+* ℂ := Rat.castHom ℂ
example : ((HermitianMetric.standard ℚ (Fin 2)).form ratEmbedding).inner
    ((1 : ComplexAt ratEmbedding) ⊗ₜ[𝓞 ℚ] (Pi.single 0 1 : Fin 2 → 𝓞 ℚ))
    ((1 : ComplexAt ratEmbedding) ⊗ₜ[𝓞 ℚ] (Pi.single 0 1 : Fin 2 → 𝓞 ℚ)) = 1 :=
  HermitianMetric.standard_inner_single ℚ 2 ratEmbedding 0
end
end GroundTheory.Heights₂.Heights


