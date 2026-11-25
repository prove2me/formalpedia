-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegStar
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegStar
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:05:06.565151+00:00
-- url     : https://prove2.me/theorems/46057f56-9821-4ec3-b547-d97296ed711f
-- title:
--   Is Poly Deg Star
-- statement:
--   Definitions and structural lemmas for Is Poly Deg Star, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsPolyDegStar.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegPrW
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgMulLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HpkConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
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
namespace GlobalTheory.WigSh.OmgContr
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {N : ℕ}
end GlobalTheory.WigSh.OmgContr
namespace GlobalTheory.WigSh
open OmgContr
end GlobalTheory.WigSh


