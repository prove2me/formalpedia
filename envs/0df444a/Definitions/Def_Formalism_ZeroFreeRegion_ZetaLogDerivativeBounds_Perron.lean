-- Prove2me | Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
-- name    : Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:00.893806+00:00
-- url     : https://prove2.me/theorems/87969947-2322-4112-98d8-b79ffbc8db7d
-- title:
--   Perron
-- statement:
--   Definitions and structural lemmas for Perron, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
namespace Formalism.ZF
end Formalism.ZF


