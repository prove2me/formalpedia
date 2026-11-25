-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisAddPiSmul
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisAddPiSmul
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:07:29.206677+00:00
-- url     : https://prove2.me/theorems/ed540ed5-524a-466a-92b4-cd063caa3d8f
-- title:
--   Exists Basis Add Pi Smul
-- statement:
--   Definitions and structural lemmas for Exists Basis Add Pi Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBasisAddPiSmul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoordApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie
namespace GlobalTheory.WachTie
end GlobalTheory.WachTie


