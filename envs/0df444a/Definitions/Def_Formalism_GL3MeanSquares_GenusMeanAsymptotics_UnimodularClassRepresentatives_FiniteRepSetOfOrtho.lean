-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:02.049271+00:00
-- url     : https://prove2.me/theorems/04a91793-e4f3-4c22-841a-87498310606a
-- title:
--   Finite Rep Set Of Ortho
-- statement:
--   Definitions and structural lemmas for Finite Rep Set Of Ortho, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FiniteRepSetOfOrtho.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
theorem autSub_gmap_one (L : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  simp [Submodule.mem_map]
theorem autSub_gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  simp [Submodule.mem_map]
def autSub (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := Formalism.ThetaLiftIndependence.autL h L
  one_mem' := ⟨one_mem _, autSub_gmap_one L⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨mul_mem ha.1 hb.1, by rw [autSub_gmap_mul, hb.2, ha.2]⟩
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem ha.1, ?_⟩
    conv_lhs => rw [← ha.2]
    rw [← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
end Formalism.HermitianLattices.Ext.L3


