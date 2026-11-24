-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_FlagKernelVanishing
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_FlagKernelVanishing
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:52.021347+00:00
-- url     : https://prove2.me/theorems/6745bf2e-0dc6-41e2-916b-d63d32254946
-- title:
--   Flag Kernel Vanishing
-- statement:
--   Definitions and structural lemmas for Flag Kernel Vanishing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/FlagKernelVanishing.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLattice
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Matrix
open scoped InnerProductSpace
namespace Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
end Formalism.HermitianLatticeCounting.P


