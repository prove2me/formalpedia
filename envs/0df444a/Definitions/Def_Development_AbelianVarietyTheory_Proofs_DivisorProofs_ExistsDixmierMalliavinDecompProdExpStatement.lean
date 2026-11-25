-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExpStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExpStatement
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:21.080209+00:00
-- url     : https://prove2.me/theorems/30498642-5a3d-4d4e-9c54-84e979afb8de
-- title:
--   Exists Dixmier Malliavin Decomp Prod Exp Statement
-- statement:
--   Definitions and structural lemmas for Exists Dixmier Malliavin Decomp Prod Exp Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDixmierMalliavinDecompProdExpStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff


