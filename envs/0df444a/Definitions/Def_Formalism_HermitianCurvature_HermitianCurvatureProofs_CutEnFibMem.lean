-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnFibMem
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnFibMem
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:13.919908+00:00
-- url     : https://prove2.me/theorems/59bed23b-117b-5e94-aee1-dc53b38706ce
-- title:
--   Cut En Fib Mem
-- statement:
--   Definitions and structural lemmas for Cut En Fib Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnFibMem.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
namespace Formalism.FourierDecayAlt.P.CutMP.En
end Formalism.FourierDecayAlt.P.CutMP.En


