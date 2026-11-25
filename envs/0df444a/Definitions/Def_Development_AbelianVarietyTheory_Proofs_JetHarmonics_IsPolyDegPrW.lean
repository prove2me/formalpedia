-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegPrW
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegPrW
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:57:19.294886+00:00
-- url     : https://prove2.me/theorems/984278bf-9f24-5a09-98fe-caed0440d72f
-- title:
--   Is Poly Deg Pr W
-- statement:
--   Definitions and structural lemmas for Is Poly Deg Pr W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsPolyDegPrW.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmpCofLPd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
namespace GlobalTheory.WigSh
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
end GlobalTheory.WigSh


