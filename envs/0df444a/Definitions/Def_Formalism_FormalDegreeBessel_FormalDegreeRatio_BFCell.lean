-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:13.804288+00:00
-- url     : https://prove2.me/theorems/f0bfa21d-6fb1-4c24-a339-e68dfb468d24
-- title:
--   BFCell
-- statement:
--   Definitions and structural lemmas for BFCell, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace Formalism.QuantumDeterminants
namespace BruhatBigCell
open GBasic
variable {k r : ℕ}
variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
end BruhatBigCell
namespace BruhatBigCell
open GBasic
end BruhatBigCell
end Formalism.QuantumDeterminants


