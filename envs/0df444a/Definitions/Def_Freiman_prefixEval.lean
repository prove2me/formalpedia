-- Prove2me | Definitions.Def_Freiman_prefixEval
-- name    : Freiman_prefixEval
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:06:03.003988+00:00
-- url     : https://prove2.me/theorems/3558c7d1-66f0-412a-8cab-2cce740fcf15
-- title:
--   Finite continued-fraction prefix acting on a tail
-- statement:
--   For a finite word $w$ of positive integers, define $T_w$ by composing the maps $x\mapsto1/(a+x)$ in the order of the digits. The empty word acts as the identity. This auxiliary evaluation leaves the existing definitions of finiteCF and cfValue unchanged.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p. 7, definition of T_w immediately before (found:continuants).

import Definitions.Def_Freiman_cfValue

namespace Freiman

noncomputable def prefixEval : List ℕ+ → ℝ → ℝ
  | [], x => x
  | a :: w, x => 1 / (((a : ℕ) : ℝ) + prefixEval w x)

end Freiman


