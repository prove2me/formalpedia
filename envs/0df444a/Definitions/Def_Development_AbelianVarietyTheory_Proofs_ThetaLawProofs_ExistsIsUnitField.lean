-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:00.370341+00:00
-- url     : https://prove2.me/theorems/d135b3a2-4e5e-4a74-b3fd-8b42291775cb
-- title:
--   Exists Is Unit Field
-- statement:
--   Definitions and structural lemmas for Exists Is Unit Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsIsUnitField.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
namespace GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]
end GlobalTheory.TorsExists


