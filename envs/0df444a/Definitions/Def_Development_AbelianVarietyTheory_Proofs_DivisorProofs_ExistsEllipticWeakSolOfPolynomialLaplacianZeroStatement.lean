-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEllipticWeakSolOfPolynomialLaplacianZeroStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEllipticWeakSolOfPolynomialLaplacianZeroStatement
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:10:17.009902+00:00
-- url     : https://prove2.me/theorems/2ed1d6a8-527b-4a9c-9feb-4cf6198e6bb4
-- title:
--   Exists Elliptic Weak Sol Of Polynomial Laplacian Zero Statement
-- statement:
--   Definitions and structural lemmas for Exists Elliptic Weak Sol Of Polynomial Laplacian Zero Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEllipticWeakSolOfPolynomialLaplacianZeroStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEllipticWeakSolOfPolynomialLaplacianZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff


