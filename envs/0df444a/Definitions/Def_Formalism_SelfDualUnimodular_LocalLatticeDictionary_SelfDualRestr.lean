-- Prove2me | Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
-- name    : Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:48:38.127085+00:00
-- url     : https://prove2.me/theorems/d983369a-691e-4e1e-b717-04390d91d452
-- title:
--   Self Dual Restr
-- statement:
--   Definitions and structural lemmas for Self Dual Restr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open NumberField
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
def restr (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : W →ₗ⋆[K] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y)
    (by intro x y z; simp) (by intro c x y; simp) (by intro x y z; simp) (by intro c x y; simp)
def coef (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) : V →ₗ[K] K := (h X X)⁻¹ • h X
theorem coef_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X x : V) : coef h X x = (h X X)⁻¹ * h X x := rfl
def proj (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) : V →ₗ[K] LinearMap.ker (h X) :=
  LinearMap.codRestrict (LinearMap.ker (h X)) (LinearMap.id - (coef h X).smulRight X) (by
    intro x
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
      smul_eq_mul, coef_apply]
    field_simp
    ring)
theorem proj_val (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (x : V) :
    (proj h X hX x : V) = x - coef h X x • X := rfl
theorem coef_self (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) : coef h X X = 1 := by
  rw [coef_apply, inv_mul_cancel₀ hX]
theorem coef_ker (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (w : LinearMap.ker (h X)) : coef h X w = 0 := by
  rw [coef_apply, LinearMap.mem_ker.mp w.2, mul_zero]
theorem decomp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (x : V) :
    x = coef h X x • X + (proj h X hX x : V) := by
  rw [proj_val]
  abel
def ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) :
    V →ₗ[K] V :=
  (coef h X).smulRight X + (LinearMap.ker (h X)).subtype ∘ₗ (g : _ →ₗ[K] _) ∘ₗ proj h X hX
theorem ext_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    ext h X hX g x = coef h X x • X + (g (proj h X hX x) : V) := rfl
theorem coef_ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    coef h X (ext h X hX g x) = coef h X x := by
  rw [ext_apply, map_add, map_smul, coef_self h X hX, coef_ker h X (g (proj h X hX x)), smul_eq_mul,
    mul_one, add_zero]
theorem proj_ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    proj h X hX (ext h X hX g x) = g (proj h X hX x) := by
  apply Subtype.ext
  rw [proj_val, coef_ext, ext_apply]
  abel
theorem ext_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    ext h X hX g.symm (ext h X hX g x) = x := by
  rw [ext_apply, coef_ext, proj_ext, LinearEquiv.symm_apply_apply]
  exact (decomp h X hX x).symm
def extE (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (ext h X hX g) (ext h X hX g.symm)
    (by
      ext x
      have := ext_comp h X hX g.symm x
      rwa [LinearEquiv.symm_symm] at this)
    (by ext x; exact ext_comp h X hX g x)
variable {S : Subring K}
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB


