-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:38.812489+00:00
-- url     : https://prove2.me/theorems/f06ea7fa-5d20-4fca-a650-8f688fc36537
-- title:
--   Ext Of Symm Apply
-- statement:
--   Definitions and structural lemmas for Ext Of Symm Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_h_x__comb_726bcd8e9864
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
namespace SplitBAux
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
theorem exists_of_orth (S : VecSplit h h') {v : V} (hv : h S.x₀ v = 0) : ∃ a, S.ι a = v := by
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [S.h_x₀_comb] at hv
  have hc : c = 0 := (mul_eq_zero.mp hv).resolve_right S.hx₀
  exact ⟨a, by rw [hc, zero_smul, zero_add]⟩
def liftι {W : Type} [AddCommGroup W] [Module K W] (S : VecSplit h h') (f : W →ₗ[K] V)
    (hf : ∀ w, ∃ b, S.ι b = f w) : W →ₗ[K] V' where
  toFun a := (hf a).choose
  map_add' a b := S.inj (by
    rw [map_add S.ι, (hf a).choose_spec, (hf b).choose_spec, (hf (a + b)).choose_spec, map_add f])
  map_smul' c a := S.inj (by
    simp only [RingHom.id_apply]
    rw [map_smul S.ι, (hf a).choose_spec, (hf (c • a)).choose_spec, map_smul f])
theorem liftι_spec {W : Type} [AddCommGroup W] [Module K W] (S : VecSplit h h') (f : W →ₗ[K] V)
    (hf : ∀ w, ∃ b, S.ι b = f w) (w : W) : S.ι (liftι S f hf w) = f w := (hf w).choose_spec
def projX (S : VecSplit h h') : V →ₗ[K] V :=
  ((h S.x₀ S.x₀)⁻¹ • h S.x₀).smulRight S.x₀
theorem projX_apply (S : VecSplit h h') (c : K) (a : V') :
    projX S (c • S.x₀ + S.ι a) = c • S.x₀ := by
  unfold projX
  rw [LinearMap.smulRight_apply, LinearMap.smul_apply, S.h_x₀_comb, smul_eq_mul]
  congr 1
  rw [inv_mul_eq_iff_eq_mul₀ S.hx₀]
  exact mul_comm _ _
def coordA (S : VecSplit h h') : V →ₗ[K] V' :=
  liftι S (LinearMap.id - projX S) (by
    intro v; obtain ⟨c, b, rfl⟩ := S.cover v
    exact ⟨b, by simp [projX_apply]⟩)
theorem coordA_apply (S : VecSplit h h') (c : K) (a : V') : coordA S (c • S.x₀ + S.ι a) = a := by
  apply S.inj
  unfold coordA
  rw [liftι_spec, LinearMap.sub_apply, LinearMap.id_apply, projX_apply, add_sub_cancel_left]
theorem linearMap_ext (S : VecSplit h h') {f g : V →ₗ[K] V} (h0 : f S.x₀ = g S.x₀)
    (h1 : ∀ a, f (S.ι a) = g (S.ι a)) : f = g := by
  ext v
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [map_add, map_add, map_smul, map_smul, h0, h1]
theorem isom_apply {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (x y : V) : h (g x) (g y) = h x y := hg x y
theorem symm_mem_isom {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) : g.symm ∈ Formalism.HermitianLatticesTheory.isom h := by
  exact inv_mem hg
theorem maps_of_fix (S : VecSplit h h') {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) (a : V') : ∃ b, S.ι b = (g.toLinearMap ∘ₗ S.ι) a := by
  apply exists_of_orth S
  show h S.x₀ (g (S.ι a)) = 0
  rw [← hx, isom_apply hg, S.orth]
theorem symm_fix {g : V ≃ₗ[K] V} {x : V} (hx : g x = x) : g.symm x = x := by
  exact g.symm_apply_eq.mpr hx.symm
def res (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hx : g S.x₀ = S.x₀) :
    V' ≃ₗ[K] V' :=
  LinearEquiv.ofLinearMap (liftι S _ (maps_of_fix S hg hx))
    (liftι S _ (maps_of_fix S (symm_mem_isom hg) (symm_fix hx)))
    (by ext a; apply S.inj; simp [liftι_spec])
    (by ext a; apply S.inj; simp [liftι_spec])
def extFun (S : VecSplit h h') (f : V' →ₗ[K] V') : V →ₗ[K] V :=
  projX S + S.ι ∘ₗ f ∘ₗ coordA S
theorem extFun_apply (S : VecSplit h h') (f : V' →ₗ[K] V') (c : K) (a : V') :
    extFun S f (c • S.x₀ + S.ι a) = c • S.x₀ + S.ι (f a) := by
  unfold extFun
  rw [LinearMap.add_apply, projX_apply, LinearMap.comp_apply, LinearMap.comp_apply, coordA_apply]
theorem eq_decomp_x₀ (S : VecSplit h h') : S.x₀ = (1 : K) • S.x₀ + S.ι 0 := by
  simp
theorem eq_decomp_ι (S : VecSplit h h') (a : V') : S.ι a = (0 : K) • S.x₀ + S.ι a := by
  simp
def extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (extFun S g'.toLinearMap) (extFun S g'.symm.toLinearMap)
    (linearMap_ext S (by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [eq_decomp_x₀ S, extFun_apply, extFun_apply]; simp)
      (fun a => by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
        rw [eq_decomp_ι S, extFun_apply, extFun_apply]; simp))
    (linearMap_ext S (by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [eq_decomp_x₀ S, extFun_apply, extFun_apply]; simp)
      (fun a => by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
        rw [eq_decomp_ι S, extFun_apply, extFun_apply]; simp))
end SplitBAux
end Formalism.HermitianLattices.Ext.L3


