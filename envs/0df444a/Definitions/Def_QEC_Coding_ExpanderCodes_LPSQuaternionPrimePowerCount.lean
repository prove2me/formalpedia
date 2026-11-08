-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:24:30.382492+00:00
-- url     : https://prove2.me/theorems/31d6da58-721b-4308-bf0d-053fc0624949
-- title:
--   LPSQuaternion Prime Power Count
-- statement:
--   Definitions and structural lemmas for LPSQuaternion Prime Power Count, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
noncomputable def lpsAlternatingReducedWordCount
    (hp : 0 < p) : ℕ → ℕ
  | 0 => (lpsReducedWords hp 0).card
  | 1 => (lpsReducedWords hp 1).card
  | n + 2 => (lpsReducedWords hp (n + 2)).card +
      lpsAlternatingReducedWordCount hp n
end QEC.Coding.TannerLiftedProduct


