-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_G2AddWeierstrassPRowSum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_G2AddWeierstrassPRowSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:21.630414+00:00
-- url     : https://prove2.me/theorems/7b7a4394-2724-401c-b68a-744290444d09
-- title:
--   G2 Add Weierstrass PRow Sum
-- statement:
--   Definitions and structural lemmas for G2 Add Weierstrass PRow Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/G2AddWeierstrassPRowSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Legendre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
namespace GlobalTheory.WpFam
end GlobalTheory.WpFam


