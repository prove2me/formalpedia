-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff
-- name    : Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:35.163813+00:00
-- url     : https://prove2.me/theorems/4c2b074e-d539-4c42-b429-9cb98786030a
-- title:
--   Weight Diff
-- statement:
--   Definitions and structural lemmas for Weight Diff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightDiff.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
namespace WD
variable {d : ℕ}
end WD
end
end ZetaZeros.D.EllReg


