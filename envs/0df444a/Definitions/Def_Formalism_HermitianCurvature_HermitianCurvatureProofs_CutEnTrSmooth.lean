-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnTrSmooth
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnTrSmooth
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:16.344365+00:00
-- url     : https://prove2.me/theorems/3d8c5b6b-5ba1-5956-93ec-f0aa2ef66dc0
-- title:
--   Cut En Tr Smooth
-- statement:
--   Definitions and structural lemmas for Cut En Tr Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnTrSmooth.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnFibMem
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
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
open scoped ContDiff
namespace Formalism.FourierDecayAlt.P.CutMP.En
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.CutMP.En


