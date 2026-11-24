-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:09.270606+00:00
-- url     : https://prove2.me/theorems/acd1a28f-54bb-4f9a-b06d-5a232b2839a7
-- title:
--   Rel Index Eq Map Mul Ker
-- statement:
--   Definitions and structural lemmas for Rel Index Eq Map Mul Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqMapMulKer.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
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
namespace Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace J
def adjF (s : V →ₗ⋆[K] V →ₗ[K] K) : V →ₗ⋆[K] V →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star (s y x))
    (fun x x' y => by simp) (fun c x y => by simp [starRingEnd_apply]) (fun x y y' => by simp)
    (fun c x y => by simp [starRingEnd_apply])
theorem adjF_apply (s : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) : adjF s x y = star (s y x) := rfl
def symF : (V →ₗ⋆[K] V →ₗ[K] K) →+ (V →ₗ⋆[K] V →ₗ[K] K) where
  toFun s := s + adjF s
  map_zero' := by
    ext x y
    simp [adjF_apply]
  map_add' s t := by
    ext x y
    simp only [LinearMap.add_apply, adjF_apply, star_add]
    ring
end J
end Formalism.HermitianLattices.Ext.L3.D2


