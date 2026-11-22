-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
-- name    : Formalism_ZetaNonvanishing_MeasurableGchi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:09.082711+00:00
-- url     : https://prove2.me/theorems/4f985d9b-891c-4655-ac8a-71d2c4e4413c
-- title:
--   Measurable Gchi
-- statement:
--   Definitions and structural lemmas for Measurable Gchi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Formalism
open ArithmeticFunction
end Formalism


