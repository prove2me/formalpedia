-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscMeanValue
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscMeanValue
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:56:16.306469+00:00
-- url     : https://prove2.me/theorems/a1ef9e8e-db54-4916-b617-9d0fa468710d
-- title:
--   Disc Mean Value
-- statement:
--   Definitions and structural lemmas for Disc Mean Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscMeanValue.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Metric
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.DiscFubiniVolume
end Formalism.FourierDecayAlt.P


