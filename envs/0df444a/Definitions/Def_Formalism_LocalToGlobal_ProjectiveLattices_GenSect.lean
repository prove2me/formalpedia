-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSect
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_GenSect
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:37:30.124567+00:00
-- url     : https://prove2.me/theorems/da28e6a5-906f-5e9f-afa4-bcbc521966f3
-- title:
--   Gen Sect
-- statement:
--   Definitions and structural lemmas for Gen Sect, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSect.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
end Formalism.L2.Pj.GenSect


