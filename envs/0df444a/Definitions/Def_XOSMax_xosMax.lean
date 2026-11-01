-- Prove2me | Definitions.Def_XOSMax_xosMax
-- name    : XOSMax_xosMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:32.156135+00:00
-- url     : https://prove2.me/theorems/e2c764b7-4e50-490d-84cb-baa301cc00eb
-- title:
--   The algorithm of Theorem 4
-- statement:
--   The algorithm of Theorem 4 has two stages on the ground list $L$:
--
--   1. the preprocessing of §2: query $f(v)$ for every $v\in L$ and remove the elements with $f(v)\le 0$;
--   2. Algorithm 4 on the remaining list.
--
--   The paper assumes $f(v)>0$ throughout §2 and justifies it in a remark: the assumption "can be tested in linear time, and when it is violated, one can modify the instance just by removing such unnecessary elements". This program makes that step part of the algorithm, so the goal theorem has no positivity hypothesis.
--
--   **Formalization Note** If no element survives, the output is $\emptyset$, a case the paper leaves implicit; then $f(X)\le 0=f(\emptyset)$ for every $X$.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, §2, p.3, "This assumption can be tested in linear time"; Algorithm 4, p.7

import Mathlib
import Definitions.Def_XOSMax_OracleProg
import Definitions.Def_XOSMax_alg4

namespace XOSMax

open OracleProg

variable {E : Type} [DecidableEq E]

/-- One element of the §2 preprocessing: keep `v` if and only if the oracle gives `f(v) > 0`. -/
noncomputable def filterStep (acc : List E) (v : E) : OracleProg E (List E) := do
  tick
  let a ← ask {v}
  tick
  if 0 < a then pure (acc ++ [v]) else pure acc

/-- **The algorithm of Theorem 4**: the §2 preprocessing followed by Algorithm 4. Elements with
`f(v) ≤ 0` are removed in linear time ("This assumption can be tested in linear time, and when it is
violated, one can modify the instance just by removing such unnecessary elements", Filmus, Kawase,
Kobayashi & Yamaguchi, arXiv:1811.09045v3, §2, p.3), then `alg4` runs on the remaining list.

**Formalization Note** `xosMax L` is built from the ground list alone, with neither `k` nor `f`. If
no element survives the preprocessing, the output is `∅`, a maximizer because then `f(X) ≤ 0 = f(∅)`
for every `X`; the paper leaves this case implicit. -/
noncomputable def xosMax (L : List E) : OracleProg E (Finset E) := do
  let L' ← L.foldlM filterStep []
  alg4 L'

end XOSMax


