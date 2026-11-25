-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulTopIff
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulTopIff
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:16:46.889233+00:00
-- url     : https://prove2.me/theorems/02d02b38-f5e8-593b-80c2-8bf60f24332a
-- title:
--   Mem Smul Top Iff
-- statement:
--   Definitions and structural lemmas for Mem Smul Top Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulTopIff.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotInfNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomCongr
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
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
open NumberField Module Filter
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace DA
theorem one_app (x : V) : (1 : V ≃ₗ[K] V) x = x := rfl
theorem apply_mem_smul {g : V ≃ₗ[K] V} {A : Submodule (𝓞 K) V} (hg : Formalism.HermitianLatticesTheory.gmap g A = A)
    (I : Ideal (𝓞 K)) {z : V} (hz : z ∈ (I • A : Submodule (𝓞 K) V)) :
    g z ∈ (I • A : Submodule (𝓞 K) V) := by
  have h1 : g z ∈ (I • A : Submodule (𝓞 K) V).map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) :=
    Submodule.mem_map_of_mem hz
  rw [Submodule.map_smul''] at h1
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg
  rwa [h2] at h1
end DA
def stabB (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x : V) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g ∈ autSub h A ∧ g x - x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V)}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : (a * b) x - x = a (b x - x) + (a x - x) := by
      rw [LinearEquiv.mul_apply, map_sub]
      abel
    rw [e]
    exact add_mem (DA.apply_mem_smul ha.2 _ hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : a⁻¹ x - x = -(a⁻¹ (a x - x)) := by
      rw [map_sub, ← LinearEquiv.mul_apply, inv_mul_cancel, DA.one_app]
      abel
    rw [e]
    exact neg_mem (DA.apply_mem_smul (inv_mem ha).2 _ ha')
end Formalism.HermitianLattices.Ext.L3.LIOrb


