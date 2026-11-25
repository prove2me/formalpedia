-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussLemmaSymPowMatrixUpperTriangularPlaceOrderStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussLemmaSymPowMatrixUpperTriangularPlaceOrderStatement
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:21:51.93845+00:00
-- url     : https://prove2.me/theorems/f59cedc9-67db-40a3-b867-ec55ca3be672
-- title:
--   Gauss Lemma Sym Pow Matrix Upper Triangular Place Order Statement
-- statement:
--   Definitions and structural lemmas for Gauss Lemma Sym Pow Matrix Upper Triangular Place Order Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussLemmaSymPowMatrixUpperTriangularPlaceOrderStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussLemmaSymPowMatrixUpperTriangularPlaceOrder
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial


