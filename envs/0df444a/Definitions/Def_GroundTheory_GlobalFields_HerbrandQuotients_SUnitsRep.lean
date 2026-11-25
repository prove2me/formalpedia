-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
-- name    : GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:49:22.157538+00:00
-- url     : https://prove2.me/theorems/7c28ad95-1687-4a69-a112-2cbff735ee70
-- title:
--   SUnits Rep
-- statement:
--   Definitions and structural lemmas for SUnits Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsRep.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain NumberField.Units
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
section Units
variable [NumberField L]
def unitsMap (g : L ≃ₐ[K] L) : (𝓞 L)ˣ →* (𝓞 L)ˣ :=
  Units.map (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) g : 𝓞 L →* 𝓞 L)
variable (K L) in

def unitsRep : Representation ℤ (L ≃ₐ[K] L) (Additive (𝓞 L)ˣ) where
  toFun g := (unitsMap g).toAdditive.toIntLinearMap
  map_one' := by
    refine LinearMap.ext fun u => ?_
    apply Additive.toMul.injective
    apply Units.ext
    apply RingOfIntegers.ext
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun u => ?_
    apply Additive.toMul.injective
    apply Units.ext
    apply RingOfIntegers.ext
    rfl
end Units
section SUnits
variable [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L)))
theorem map_mem_unit (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) {x : Lˣ}
    (hx : x ∈ S.unit L) : Units.map (g : L →+* L).toMonoidHom x ∈ S.unit L := by
  intro w hw
  have hw' : g⁻¹ • w ∉ S := fun h => hw (by simpa using hS g _ h)
  have h1 := SemiLocal.valuation_smul g (g⁻¹ • w) (x : L)
  rw [smul_inv_smul] at h1
  change w.valuation L (g (x : L)) = 1
  rw [h1]
  exact hx _ hw'
def sUnitMap (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) :
    S.unit L →* S.unit L :=
  ((Units.map (g : L →+* L).toMonoidHom).comp (S.unit L).subtype).codRestrict (S.unit L)
    fun x => map_mem_unit S hS g x.2
def sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    Representation ℤ (L ≃ₐ[K] L) (Additive (S.unit L)) where
  toFun g := (sUnitMap S hS g).toAdditive.toIntLinearMap
  map_one' := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
end SUnits
end
end GroundTheory.Global


