-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:05.196733+00:00
-- url     : https://prove2.me/theorems/3c07a2e6-3140-43bd-9b96-aaed505b3cd7
-- title:
--   Functional Equation Hom Vector
-- statement:
--   Definitions and structural lemmas for Functional Equation Hom Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationHomVector.lean

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
namespace Formalism.FG.FunctionalEquationHom
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Formalism.FG.FunctionalEquationHom
namespace Formalism.FG
end Formalism.FG


