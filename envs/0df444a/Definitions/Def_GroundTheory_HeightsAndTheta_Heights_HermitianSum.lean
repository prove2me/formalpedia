-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
-- name    : GroundTheory_HeightsAndTheta_Heights_HermitianSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:59.793965+00:00
-- url     : https://prove2.me/theorems/47f8efc8-3512-4f63-abb5-aa181441009a
-- title:
--   Hermitian Sum
-- statement:
--   Definitions and structural lemmas for Hermitian Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
section Core
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
theorem core_inner_self_im (h : InnerProductSpace.Core ℂ V) (x : V) : (h.inner x x).im = 0 := by
  have := h.conj_inner_symm x x
  exact Complex.conj_eq_iff_im.mp this
theorem core_eq_zero_of_re (h : InnerProductSpace.Core ℂ V) (x : V)
    (hx : (h.inner x x).re = 0) : x = 0 :=
  h.definite x (Complex.ext hx (core_inner_self_im h x))
@[instance_reducible]
def coreComap (h : InnerProductSpace.Core ℂ W) (f : V →ₗ[ℂ] W) (hf : Function.Injective f) :
    InnerProductSpace.Core ℂ V where
  inner x y := h.inner (f x) (f y)
  conj_inner_symm x y := h.conj_inner_symm (f x) (f y)
  re_inner_nonneg x := h.re_inner_nonneg (f x)
  add_left x y z := by simp only [map_add, h.add_left]
  smul_left x y r := by simp only [map_smul, h.smul_left]
  definite x hx := hf (by rw [map_zero]; exact h.definite _ hx)
theorem coreComap_inner (h : InnerProductSpace.Core ℂ W) (f : V →ₗ[ℂ] W)
    (hf : Function.Injective f) (x y : V) :
    (coreComap h f hf).inner x y = h.inner (f x) (f y) := rfl
@[instance_reducible]
def coreProd (hV : InnerProductSpace.Core ℂ V) (hW : InnerProductSpace.Core ℂ W) :
    InnerProductSpace.Core ℂ (V × W) where
  inner x y := hV.inner x.1 y.1 + hW.inner x.2 y.2
  conj_inner_symm x y := by
    rw [map_add, hV.conj_inner_symm, hW.conj_inner_symm]
  re_inner_nonneg x := by
    rw [map_add]
    exact add_nonneg (hV.re_inner_nonneg _) (hW.re_inner_nonneg _)
  add_left x y z := by
    simp only [Prod.fst_add, Prod.snd_add, hV.add_left, hW.add_left]
    ring
  smul_left x y r := by
    simp only [Prod.smul_fst, Prod.smul_snd, hV.smul_left, hW.smul_left]
    ring
  definite x hx := by
    have h1 := hV.re_inner_nonneg x.1
    have h2 := hW.re_inner_nonneg x.2
    have hre : (hV.inner x.1 x.1).re + (hW.inner x.2 x.2).re = 0 := by
      rw [← Complex.add_re, hx, Complex.zero_re]
    have e1 : (hV.inner x.1 x.1).re = 0 := by
      change 0 ≤ (hV.inner x.1 x.1).re at h1
      change 0 ≤ (hW.inner x.2 x.2).re at h2
      linarith
    have e2 : (hW.inner x.2 x.2).re = 0 := by
      change 0 ≤ (hV.inner x.1 x.1).re at h1
      change 0 ≤ (hW.inner x.2 x.2).re at h2
      linarith
    exact Prod.ext (core_eq_zero_of_re hV _ e1) (core_eq_zero_of_re hW _ e2)
theorem coreProd_inner (hV : InnerProductSpace.Core ℂ V) (hW : InnerProductSpace.Core ℂ W)
    (x y : V × W) : (coreProd hV hW).inner x y = hV.inner x.1 y.1 + hW.inner x.2 y.2 := rfl
end Core
variable {K : Type*} [Field K]
section Split
variable (σ : K →+* ℂ) (E F : Type*) [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F]
  [Module (𝓞 K) F]
def fibreProd : Fibre σ (E × F) ≃ₗ[ℂ] Fibre σ E × Fibre σ F :=
  (prodRight (𝓞 K) (ComplexAt σ) (ComplexAt σ) E F).restrictScalars ℂ
variable {σ E F}
@[simp]
theorem fibreProd_tmul (z : ComplexAt σ) (e : E) (f : F) :
    fibreProd σ E F (z ⊗ₜ (e, f)) = (z ⊗ₜ e, z ⊗ₜ f) := rfl
theorem fibreProd_conjMap (x : Fibre σ (E × F)) :
    fibreProd (conjugate σ) E F (conjMap σ (E × F) x) =
      (conjMap σ E (fibreProd σ E F x).1, conjMap σ F (fibreProd σ E F x).2) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Prod.mk_zero_zero]
  | tmul z v => rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, Prod.fst_add, Prod.snd_add, map_add, map_add,
      Prod.mk_add_mk]
end Split
variable [NumberField K]
variable {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup F] [Module (𝓞 K) F] [Module.Finite (𝓞 K) F]
  [Module.Projective (𝓞 K) F]
def HermitianMetric.prod (hE : HermitianMetric K E) (hF : HermitianMetric K F) :
    HermitianMetric K (E × F) where
  form σ := coreComap (coreProd (hE.form σ) (hF.form σ)) (fibreProd σ E F).toLinearMap
    (fibreProd σ E F).injective
  form_conj σ x y := by
    simp only [coreComap_inner, coreProd_inner, LinearEquiv.coe_coe, fibreProd_conjMap,
      hE.form_conj, hF.form_conj, map_add]
def HermitianBundle.prod (A B : HermitianBundle K) : HermitianBundle K :=
  ⟨A.carrier × B.carrier, A.metric.prod B.metric⟩
example : HermitianBundle GaussianField := gaussianIntegers.prod (gaussianStandard 2)
end
end GroundTheory.Heights₂.Heights


