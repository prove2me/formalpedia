-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtHomInjective
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtHomInjective
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:40:13.393326+00:00
-- url     : https://prove2.me/theorems/1171d2f2-cfc9-5c19-abb3-466b9c5eee6b
-- title:
--   Ext Hom Injective
-- statement:
--   Definitions and structural lemmas for Ext Hom Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtHomInjective.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulTopIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatioHolds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_cut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
def extHom (S : VecSplit h h') : (V' ≃ₗ[K] V') →* (V ≃ₗ[K] V) where
  toFun := SplitBAux.extOf S
  map_one' := by
    ext v
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [SplitBAux.extOf_apply]
    rfl
  map_mul' := by
    intro a b
    ext v
    obtain ⟨c, x, rfl⟩ := S.cover v
    rw [SplitBAux.extOf_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, SplitBAux.extOf_apply,
      SplitBAux.extOf_apply]
def autExt (S : VecSplit h h') (M : Submodule (𝓞 K) V) : Subgroup (V' ≃ₗ[K] V') :=
  (autSub h M).comap (extHom S)
def oM (S : VecSplit h h') (M : Submodule (𝓞 K) V) : ℕ :=
  (autExt S M).relIndex (autSub h' (S.cut M))
def nu {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (h₀ : W →ₗ⋆[K] W →ₗ[K] K) (A : Submodule (𝓞 K) W) (𝔭 : Ideal (𝓞 F)) : ℝ :=
  alphaL h₀ A 𝔭 / (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K W * vd h₀ A 𝔭)
def kap (S : VecSplit h h') (M : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) (J k : ℕ) : ℝ :=
  (cnt h M 𝔭 k n (tube (autSub h M) M 𝔭 J S.x₀) : ℝ) /
    ((Ideal.absNorm 𝔭 : ℝ) ^ vd h M 𝔭 * nu h M 𝔭) * (nu h' (S.cut M) 𝔭 / (oM S M : ℝ))
end Formalism.HermitianLattices.Ext.L3.LIOrb


