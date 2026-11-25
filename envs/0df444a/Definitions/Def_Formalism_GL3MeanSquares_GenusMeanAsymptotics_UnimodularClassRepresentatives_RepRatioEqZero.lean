-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RepRatioEqZero
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RepRatioEqZero
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:16.978237+00:00
-- url     : https://prove2.me/theorems/9c9fd4af-61f4-5263-835a-b74cabe3ac2b
-- title:
--   Rep Ratio Eq Zero
-- statement:
--   Definitions and structural lemmas for Rep Ratio Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RepRatioEqZero.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NuGmapLocF
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
namespace Formalism.HermitianLattices.Ext.L3
namespace LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
end LIOrb
end Formalism.HermitianLattices.Ext.L3


