-- Prove2me | Definitions.Def_NSWBetter_Inst_WellFormed
-- name    : NSWBetter_Inst_WellFormed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:13.994834+00:00
-- url     : https://prove2.me/theorems/3ea9e36d-b9da-48c1-8a66-08629384a0f1
-- title:
--   Well-formed instance: nonnegative valuations
-- statement:
--   An instance is **well formed** when every value is nonnegative: $v_i(g)\ge 0$ for every agent $i$ and good $g$ (valuations map into $\mathbb R_{\ge0}$).
--
--   No other restriction is imposed: instances with no agents, no goods, fewer goods than agents, or optimal Nash welfare $0$ are all admitted.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2, p.8 ($v_i : 2^G \to \mathbb R_{\ge 0}$)

import Mathlib
import Definitions.Def_NSWBetter_Inst

namespace NSWBetter

/-- **Nonnegative valuations.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.8: "vi : 2G → R≥0".

`I.WellFormed` says every value `v i g` is nonnegative. Nothing else is required: `n = 0`, `m = 0`, `m < n`, zero rows and instances with optimal Nash welfare `0` are all instances. -/
def Inst.WellFormed (I : Inst) : Prop := ∀ i g, 0 ≤ I.v i g

end NSWBetter


