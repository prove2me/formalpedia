-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:49.86886+00:00
-- url     : https://prove2.me/theorems/a7f2c746-fef8-4464-9e6d-66a99e85ad32
-- title:
--   Is Unimodular At Adjoin Iff
-- statement:
--   Definitions and structural lemmas for Is Unimodular At Adjoin Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
structure VecSplit (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) where
  x₀ : V
  ι : V' →ₗ[K] V
  inj : Function.Injective ι
  hx₀ : h x₀ x₀ ≠ 0
  isom : ∀ a b, h (ι a) (ι b) = h' a b
  orth : ∀ a, h x₀ (ι a) = 0
  cover : ∀ v, ∃ (c : K) (a : V'), v = c • x₀ + ι a
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
def VecSplit.adjoin (S : VecSplit h h') (L' : Submodule (𝓞 K) V') : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) {S.x₀} ⊔ L'.map (S.ι.restrictScalars (𝓞 K))
def VecSplit.cut (S : VecSplit h h') (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V' :=
  L.comap (S.ι.restrictScalars (𝓞 K))
namespace VecSplit
variable (S : VecSplit h h')
end VecSplit
namespace VecSplit
variable (S : VecSplit h h')
end VecSplit
namespace VecSplit
variable (S : VecSplit h h')
end VecSplit
end Formalism.HermitianLattices.Ext.L3


