-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansion
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:48.450487+00:00
-- url     : https://prove2.me/theorems/77d90690-79f6-467a-83e0-c0595d399a38
-- title:
--   Weierstrass Division Value QExpansion
-- statement:
--   Definitions and structural lemmas for Weierstrass Division Value QExpansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeierstrassDivisionValueQExpansion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowsSumEqDivisorSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonIntegerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_G2AddWeierstrassPRowSumStatement
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
namespace GlobalTheory.WpFam.ExpansionB
end GlobalTheory.WpFam.ExpansionB


