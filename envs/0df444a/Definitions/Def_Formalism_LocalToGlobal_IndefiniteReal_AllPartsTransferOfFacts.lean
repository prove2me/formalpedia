-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts
-- name    : Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:14:42.864598+00:00
-- url     : https://prove2.me/theorems/770843ed-8c6d-42e1-a421-949d9bac6362
-- title:
--   All Parts Transfer Of Facts
-- statement:
--   Definitions and structural lemmas for All Parts Transfer Of Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/AllPartsTransferOfFacts.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement Formalism.HN _root_.Formalism.IndefR.LatticeTransfer.Lat
end Formalism.IndefR.LatticeTransfer


