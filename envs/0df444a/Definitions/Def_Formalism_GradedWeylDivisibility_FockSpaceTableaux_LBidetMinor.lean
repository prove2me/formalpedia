-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:22.894682+00:00
-- url     : https://prove2.me/theorems/8606c59e-b3cc-43a6-8522-9c99aee6fa37
-- title:
--   LBidet Minor
-- statement:
--   Definitions and structural lemmas for LBidet Minor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetMinor.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
def initW (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0
end Formalism.GradedWeylDivisibility


