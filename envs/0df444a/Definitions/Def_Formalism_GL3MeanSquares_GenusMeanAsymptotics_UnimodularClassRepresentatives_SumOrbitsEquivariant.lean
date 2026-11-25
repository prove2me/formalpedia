-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:45:44.254129+00:00
-- url     : https://prove2.me/theorems/b2cab3b2-e154-4752-b3df-8d036c0ddc7a
-- title:
--   Sum Orbits Equivariant
-- statement:
--   Definitions and structural lemmas for Sum Orbits Equivariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumOrbitsEquivariant.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
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
namespace Formalism.HermitianLattices.Ext.L3
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
def fibG (S : VecSplit h h') (L : Submodule (𝓞 K) V) (Λ' : Submodule (𝓞 K) V') :
    Set (Submodule (𝓞 K) V) :=
  {Λ | Λ ∈ Formalism.HermitianLatticesTheory.genus h L ∧ S.x₀ ∈ Λ ∧ S.cut Λ = Λ'}
def IsFibReps (S : VecSplit h h') (L : Submodule (𝓞 K) V) (s' : Finset (Submodule (𝓞 K) V')) :
    Prop :=
  (∀ Λ' ∈ s', (fibG S L Λ').Nonempty) ∧
  ∀ Λ' : Submodule (𝓞 K) V', (fibG S L Λ').Nonempty →
    ∃! Λ₀, Λ₀ ∈ s' ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g Λ₀ = Λ'
namespace StabilizerLattices
open SplitBAux
end StabilizerLattices
end Formalism.HermitianLattices.Ext.L3


