-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:16.038392+00:00
-- url     : https://prove2.me/theorems/3db8aa77-8e0d-4daa-9116-1d89280ce784
-- title:
--   IRRFrob Orbit Irred
-- statement:
--   Definitions and structural lemmas for IRRFrob Orbit Irred, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRFrobOrbitIrred.lean

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.GaloisIrreducibility (IsOrbit)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


