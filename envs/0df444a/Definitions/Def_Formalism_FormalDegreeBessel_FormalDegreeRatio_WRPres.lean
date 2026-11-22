-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:46:02.71905+00:00
-- url     : https://prove2.me/theorems/2e818e9c-1e4c-47c3-a417-b325a1e9c1f2
-- title:
--   WRPres
-- statement:
--   Definitions and structural lemmas for WRPres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRPres.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace Formalism.QuantumDeterminants
namespace WRPres
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end WRPres
open WRPres
end Formalism.QuantumDeterminants


