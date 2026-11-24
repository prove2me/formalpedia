-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JConvOfJDom
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_JConvOfJDom
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:09:25.09879+00:00
-- url     : https://prove2.me/theorems/057ff9ee-fbd9-46fc-8e68-8b4161343c29
-- title:
--   JConv Of JDom
-- statement:
--   Definitions and structural lemmas for JConv Of JDom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JConvOfJDom.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxDs1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.JFxDs1


