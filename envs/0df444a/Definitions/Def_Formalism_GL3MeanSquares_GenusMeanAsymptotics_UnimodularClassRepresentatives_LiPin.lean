-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LiPin
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LiPin
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:01.124801+00:00
-- url     : https://prove2.me/theorems/b3680c79-3a03-5cb0-8fe7-c874f0fc733c
-- title:
--   Li Pin
-- statement:
--   Definitions and structural lemmas for Li Pin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LiPin.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RepRatioEqZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LamGEqOneOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsTotPosDefOfSmul
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
namespace PinD
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
end PinD
end Formalism.HermitianLattices.Ext.L3


