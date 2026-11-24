-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LaurentAdjoinEqOfImageEq
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LaurentAdjoinEqOfImageEq
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T09:27:19.007608+00:00
-- url     : https://prove2.me/theorems/28d94909-272f-41d7-9cd2-6f8bee8a5bb1
-- title:
--   Laurent Adjoin Eq Of Image Eq
-- statement:
--   Definitions and structural lemmas for Laurent Adjoin Eq Of Image Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LaurentAdjoinEqOfImageEq.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
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
namespace Formalism.HermitianLattices.Ext.L3.WCB
section Alg
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
def skewY (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) : V →ₗ[K] V :=
  (θ • h u - h w).smulRight u + (h u).smulRight w
end Alg
section Int
open WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
end Int
end Formalism.HermitianLattices.Ext.L3.WCB


