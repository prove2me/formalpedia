-- Prove2me | Definitions.Def_Formalism_SmithDeterminants_DefsDVR
-- name    : Formalism_SmithDeterminants_DefsDVR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:12.46437+00:00
-- url     : https://prove2.me/theorems/29ba22ca-8323-4428-83b6-2b4736c9e9d6
-- title:
--   Defs DVR
-- statement:
--   Definitions and structural lemmas for Defs DVR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SmithDeterminants/DefsDVR.lean

import Definitions.Def_Formalism_SmithDeterminants_StatementDVR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.A
def L3of : Prop := RangePowGenerators → LengthQuotientBound
def FinalOf : Prop := SmithGen → LengthQuotientBound → TruncDet → TruncFinal
def HornOf : Prop := SatChain → GradedHorn
end Formalism.A


