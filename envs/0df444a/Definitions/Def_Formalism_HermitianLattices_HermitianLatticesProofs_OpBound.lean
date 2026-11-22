-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:44.798348+00:00
-- url     : https://prove2.me/theorems/aa190166-bf0a-499e-b7a3-f57882ad63a7
-- title:
--   Op Bound
-- statement:
--   Definitions and structural lemmas for Op Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/OpBound.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
namespace Formalism.HermitianLatticesTheory
section OpBoundAux
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
end OpBoundAux
end Formalism.HermitianLatticesTheory


