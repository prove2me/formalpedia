-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CommuteOfLocEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CommuteOfLocEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:59.525697+00:00
-- url     : https://prove2.me/theorems/fc89a6d3-290a-4bc8-a3ce-2d1a5c262b26
-- title:
--   Commute Of Loc Eq One
-- statement:
--   Definitions and structural lemmas for Commute Of Loc Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CommuteOfLocEqOne.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCompAtEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
noncomputable section
namespace GlobalTheory.SplitLocComm
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
end GlobalTheory.SplitLocComm


