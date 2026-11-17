-- Prove2me | Definitions.Def_SpencerEight_Supplement_family16
-- name    : SpencerEight_Supplement_family16
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:50:22.723521+00:00
-- url     : https://prove2.me/theorems/a77ef0b7-75ed-450f-b608-9831169be9d1
-- title:
--   The sixteen words $A_1,\dots,A_{16}$ of Theorem 15.4
-- statement:
--   The matrices $A_1,\dots,A_{16}\in\mathbb R^{16\times16}$ of Theorem 15.4 are the four-letter words read from left to right, one row at a time, from the array
--   $$
--   \begin{array}{cccc}IIII&XZZZ&ZJXJ&JIZJ\\JZJZ&ZXXX&JIJI&XZJJ\\JJXX&XXXI&XIXZ&JIJZ\\IJJX&JJII&XZXI&ZIIZ\end{array}
--   $$
--   so $A_1=IIII$, $A_2=XZZZ$, …, $A_{16}=ZIIZ$.
--
--   **Formalization Note** The Lean index is 0-based: `family16 i` is $A_{i+1}$. Each word is a `word` of four letters.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Theorem 15.4, p.290 (PDF p.290)

import Mathlib
import Definitions.Def_SpencerEight_Supplement_word

namespace SpencerEight.Supplement

open Letter in
/-- The sixteen `16 × 16` words `A₁, …, A₁₆` of Theorem 15.4 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.290 (PDF p.290)),
read from left to right, one row at a time, from the printed array
`IIII XZZZ ZJXJ JIZJ JZJZ ZXXX JIJI XZJJ JJXX XXXI XIXZ JIJZ IJJX JJII XZXI ZIIZ`.

**Formalization Note** `family16 i` is the source's `A_{i+1}` (0-based index); `Fin (2^4)` is `Fin 16`. -/
def family16 : Fin 16 → Matrix (Fin (2 ^ 4)) (Fin (2 ^ 4)) ℝ :=
  ![word ![I, I, I, I], word ![X, Z, Z, Z], word ![Z, J, X, J], word ![J, I, Z, J],
    word ![J, Z, J, Z], word ![Z, X, X, X], word ![J, I, J, I], word ![X, Z, J, J],
    word ![J, J, X, X], word ![X, X, X, I], word ![X, I, X, Z], word ![J, I, J, Z],
    word ![I, J, J, X], word ![J, J, I, I], word ![X, Z, X, I], word ![Z, I, I, Z]]

end SpencerEight.Supplement


