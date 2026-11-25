-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsTotPosDefOfSmul
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsTotPosDefOfSmul
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:14:29.235637+00:00
-- url     : https://prove2.me/theorems/a104a722-95ae-4e59-a84b-96f1e3c298ea
-- title:
--   Is Tot Pos Def Of Smul
-- statement:
--   Definitions and structural lemmas for Is Tot Pos Def Of Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsTotPosDefOfSmul.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealSmulLeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocFSpanConsBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.PinD
section One
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K] in
theorem smul_form_apply (c : K) (h : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) : (c • h) x y = c * h x y := by
  rfl
end One
section Two
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
def unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) : VecSplit h h' where
  x₀ := S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := fun e => S.hx₀ (by rw [smul_form_apply, e, mul_zero])
  isom := fun a b => by
    have := S.isom a b
    rw [smul_form_apply, smul_form_apply] at this
    exact mul_left_cancel₀ hc this
  orth := fun a => by
    have := S.orth a
    rw [smul_form_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  cover := S.cover
end Two
end Formalism.HermitianLattices.Ext.L3.PinD


