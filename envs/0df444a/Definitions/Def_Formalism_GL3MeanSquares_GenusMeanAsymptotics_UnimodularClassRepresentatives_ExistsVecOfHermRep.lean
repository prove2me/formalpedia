-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:48.636526+00:00
-- url     : https://prove2.me/theorems/fe202728-2d7f-4a3e-9099-518071464f89
-- title:
--   Exists Vec Of Herm Rep
-- statement:
--   Definitions and structural lemmas for Exists Vec Of Herm Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsVecOfHermRep.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
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
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
def perpSpace (h : V →ₗ⋆[K] V →ₗ[K] K) (x₀ : V) : Submodule K V := LinearMap.ker (h x₀)
def perpForm (h : V →ₗ⋆[K] V →ₗ[K] K) (x₀ : V) :
    ↥(perpSpace h x₀) →ₗ⋆[K] ↥(perpSpace h x₀) →ₗ[K] K :=
  (h.comp (perpSpace h x₀).subtype).compl₂ (perpSpace h x₀).subtype
def vecSplitPerp (h : V →ₗ⋆[K] V →ₗ[K] K) {x₀ : V} (hx : h x₀ x₀ ≠ 0) :
    VecSplit h (perpForm h x₀) where
  x₀ := x₀
  ι := (perpSpace h x₀).subtype
  inj := Subtype.val_injective
  hx₀ := hx
  isom := fun _ _ => rfl
  orth := fun a => LinearMap.mem_ker.mp a.2
  cover := fun v => by
    refine ⟨h x₀ v / h x₀ x₀, ⟨v - (h x₀ v / h x₀ x₀) • x₀, ?_⟩, ?_⟩
    · change v - (h x₀ v / h x₀ x₀) • x₀ ∈ LinearMap.ker (h x₀)
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx, sub_self]
    · simp
end Formalism.HermitianLattices.Ext.L3


