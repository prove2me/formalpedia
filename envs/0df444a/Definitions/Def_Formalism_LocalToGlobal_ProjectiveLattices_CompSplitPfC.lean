-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:52.50485+00:00
-- url     : https://prove2.me/theorems/968ead2e-56d8-40f8-9d1e-4d2fbb09f3c9
-- title:
--   Comp Split Pf C
-- statement:
--   Definitions and structural lemmas for Comp Split Pf C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfC.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.CompSplitPfC
open TensorProduct
variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]
end Formalism.L2.Pj.CompSplitPfC


