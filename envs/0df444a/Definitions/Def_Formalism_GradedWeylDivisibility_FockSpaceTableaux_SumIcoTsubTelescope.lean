-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:59:40.307889+00:00
-- url     : https://prove2.me/theorems/bfd24d9f-ff98-4f30-b510-f86bb4d9760b
-- title:
--   Sum Ico Tsub Telescope
-- statement:
--   Definitions and structural lemmas for Sum Ico Tsub Telescope, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SumIcoTsubTelescope.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
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
def extNu {n : ℕ} (ν : Fin n → ℕ) (k : ℕ) : ℕ := if h : k < n then ν ⟨k, h⟩ else 0
end Formalism.GradedWeylDivisibility


