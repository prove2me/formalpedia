-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExtensionIdentityOfMemCompl
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExtensionIdentityOfMemCompl
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T11:10:28.707111+00:00
-- url     : https://prove2.me/theorems/e4324e7f-a41d-5125-aaee-63d0deeff2ba
-- title:
--   Extension Identity Of Mem Compl
-- statement:
--   Definitions and structural lemmas for Extension Identity Of Mem Compl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
import Theorems.Thm_Formalism_L2_SG_Pf_G9_apply_mem_orthK
import Theorems.Thm_Formalism_L2_SG_Pf_G9_mem_orthK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def formOn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : ↥X →ₗ⋆[K] ↥X →ₗ[K] K :=
  (h.comp X.subtype).compl₂ X.subtype
@[simp] theorem formOn_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x y : ↥X) :
    formOn h X x y = h x y := rfl
def incl (X : Submodule K V) : ↥X →ₗ[𝓞 K] V := X.subtype.restrictScalars (𝓞 K)
def push (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : Submodule (𝓞 K) V := L.map (incl X)
def pull (X : Submodule K V) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) ↥X := L.comap (incl X)
section Ext
variable [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
def extId (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm.trans
    (((LinearEquiv.refl K ↥U).prodCongr g).trans (Submodule.prodEquivOfIsCompl U (orthK h U) hc))
theorem extId_add (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u w : V}
    (hu : u ∈ U) (hw : w ∈ orthK h U) : extId hc g (u + w) = u + (g ⟨w, hw⟩ : V) := by
  have e1 : (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm (u + w) = (⟨u, hu⟩, ⟨w, hw⟩) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
  simp only [extId, LinearEquiv.trans_apply, e1, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl']
theorem exists_add (hc : IsCompl U (orthK h U)) (v : V) :
    ∃ u ∈ U, ∃ w ∈ orthK h U, u + w = v := by
  have hv : v ∈ U ⊔ orthK h U := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  exact Submodule.mem_sup.mp hv
theorem extId_of_mem_U (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u : V}
    (hu : u ∈ U) : extId hc g u = u := by
  have := extId_add hc g hu (orthK h U).zero_mem
  rw [add_zero] at this
  rw [this]
  simp
theorem extId_mem (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) : extId hc g ∈ isomFix h U := by
  refine ⟨fun v v' => ?_, fun u hu => extId_of_mem_U hc g hu⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add hc v
  obtain ⟨u', hu', w', hw', rfl⟩ := exists_add hc v'
  rw [extId_add hc g hu hw, extId_add hc g hu' hw']
  have hg' : h (g ⟨w, hw⟩ : V) (g ⟨w', hw'⟩ : V) = h w w' := hg _ _
  have o1 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h x y = 0 := fun hx hy => mem_orthK.mp hy _ hx
  have o2 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h y x = 0 := fun {x y} hx hy => by
    rw [← hs.eq x y, o1 hx hy, map_zero]
  simp only [map_add, LinearMap.add_apply]
  rw [hg', o1 hu (g ⟨w', hw'⟩).2, o2 hu' (g ⟨w, hw⟩).2, o1 hu hw', o2 hu' hw]
theorem map_orthK {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    (orthK h U).map (g : V →ₗ[K] V) = orthK h U := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact apply_mem_orthK hg hy
  · intro hx
    exact ⟨g.symm x, apply_mem_orthK ((isomFix h U).inv_mem hg) hx, g.apply_symm_apply x⟩
def restr {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U) :=
  g.ofSubmodules (orthK h U) (orthK h U) (map_orthK hg)
end Ext
end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass


