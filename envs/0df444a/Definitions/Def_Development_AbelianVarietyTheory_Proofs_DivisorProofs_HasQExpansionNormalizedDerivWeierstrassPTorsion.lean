-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedDerivWeierstrassPTorsion
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedDerivWeierstrassPTorsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:37.201809+00:00
-- url     : https://prove2.me/theorems/01a39425-1b89-46fb-8c0d-c788cad74aa2
-- title:
--   Has QExpansion Normalized Deriv Weierstrass PTorsion
-- statement:
--   Definitions and structural lemmas for Has QExpansion Normalized Deriv Weierstrass PTorsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionNormalizedDerivWeierstrassPTorsion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowsSumEqDivisorSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonIntegerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumRowsInvCubeDerivWeierstrassPStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
namespace GlobalTheory.WpFam.DerivExpansion
end GlobalTheory.WpFam.DerivExpansion


