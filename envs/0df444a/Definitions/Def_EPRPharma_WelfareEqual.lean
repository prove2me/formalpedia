-- Prove2me | Definitions.Def_EPRPharma_WelfareEqual
-- name    : EPRPharma_WelfareEqual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:16:49.133773+00:00
-- url     : https://prove2.me/theorems/dd97e8ea-0e79-4617-a84f-11ea8d5cc382
-- title:
--   The models give equal maximal welfare (EC = SR)
-- statement:
--   "EC = SR" holds if both models have a maximal total welfare and the two maxima coincide: $W_{EC}^*=W_{SR}^*$. It is the entry "EC = SR" of Table 2.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), Table 2, p. 18

import Mathlib
import Definitions.Def_EPRPharma_IsMaxWelfare

namespace EPRPharma

/-- **"EC = SR": the two models give the same maximal total welfare.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), Table 2, p. 18: the entry "EC = SR".
`WelfareEqual P` says that both models have a maximal total welfare and the two maxima are
equal. -/
def WelfareEqual (P : Params) : Prop :=
  ∃ v : ℝ, IsMaxWelfare P .EC v ∧ IsMaxWelfare P .SR v

end EPRPharma


