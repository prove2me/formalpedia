-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:55:53.138812+00:00
-- url     : https://prove2.me/theorems/6c28a99c-376f-5295-8e11-eed6d3757555
-- title:
--   Omg Equivariant
-- statement:
--   Definitions and structural lemmas for Omg Equivariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgEquivariant.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
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
namespace GlobalTheory.WigSh.OmgEquiv
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
end GlobalTheory.WigSh.OmgEquiv
namespace GlobalTheory.WigSh
open OmgEquiv
end GlobalTheory.WigSh


