-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:18.744796+00:00
-- url     : https://prove2.me/theorems/e385ce99-bd58-4fe0-979b-cfdae5208977
-- title:
--   Discr Ideal Le Iff
-- statement:
--   Definitions and structural lemmas for Discr Ideal Le Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscrIdealLeIff.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
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
namespace Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
def IsGen (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : V) : Prop :=
  e ∈ L ∧ e ≠ 0 ∧ ∀ x ∈ L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 F) (𝓞 K) t • x = a • e
end Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals


