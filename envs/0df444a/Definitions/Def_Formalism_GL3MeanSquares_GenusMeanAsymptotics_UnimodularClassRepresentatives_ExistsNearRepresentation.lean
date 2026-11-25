-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:56:44.164406+00:00
-- url     : https://prove2.me/theorems/2b11e90a-c273-5a9f-9bb8-5c4b337eaf1e
-- title:
--   Exists Near Representation
-- statement:
--   Definitions and structural lemmas for Exists Near Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNearRepresentation.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
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
namespace Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
end Formalism.HermitianLattices.Ext.L3.Cell


