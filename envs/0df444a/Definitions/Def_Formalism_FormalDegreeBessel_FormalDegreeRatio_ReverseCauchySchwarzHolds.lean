-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:54.753654+00:00
-- url     : https://prove2.me/theorems/78a52d6e-eb32-4aeb-931f-bfd8e8ddefff
-- title:
--   Reverse Cauchy Schwarz Holds
-- statement:
--   Definitions and structural lemmas for Reverse Cauchy Schwarz Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
namespace Formalism.QuantumDeterminants
def ggLastU (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if i = Fin.last n ∧ j = Fin.last n then 1 else 0
end Formalism.QuantumDeterminants


