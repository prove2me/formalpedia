-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocReps
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocReps
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:35:08.367319+00:00
-- url     : https://prove2.me/theorems/5465ee5c-bc08-5d3b-97c9-8f715c753cae
-- title:
--   Exists Loc Reps
-- statement:
--   Definitions and structural lemmas for Exists Loc Reps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocReps.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BrB
section One
variable {K V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end One
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
def scaleSplit (S : VecSplit h h') (c : K) (hc : c ≠ 0) : VecSplit h h' where
  x₀ := c • S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := by
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_ne_zero hc (mul_ne_zero ((map_ne_zero _).mpr hc) S.hx₀)
  isom := S.isom
  orth := fun a => by
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, S.orth, smul_zero]
  cover := fun v => by
    obtain ⟨d, a, rfl⟩ := S.cover v
    exact ⟨d / c, a, by rw [smul_smul, div_mul_cancel₀ _ hc]⟩
end Formalism.HermitianLattices.Ext.L3.BrB


