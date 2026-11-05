-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_ConcaveOnE
-- name    : BauerleRiederMDP_TransactionCosts_ConcaveOnE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:15.863275+00:00
-- url     : https://prove2.me/theorems/d173caa4-c9cb-4951-8220-c85c0776c249
-- title:
--   Concave extended-real functions on $E$
-- statement:
--   A function $v:E\to[-\infty,\infty)$ is concave if
--   $$t\,v(x)+(1-t)\,v(y)\le v\big(tx+(1-t)y\big)\qquad\text{for all }x,y\in E,\ t\in[0,1],$$
--   with the conventions $0\cdot(-\infty)=0$ and $t\cdot(-\infty)=-\infty$ for $t>0$ (concavity of the hypograph).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, p.107 (PDF 121)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace

namespace BauerleRiederMDP.TransactionCosts

/-- A function `v : E → [−∞, ∞)` is *concave* on `E = ℝ²₊` (Bäuerle & Rieder 2011, §4.5,
p.107, PDF 121): for all `x, y ∈ E` and `t ∈ [0, 1]`,
`t v(x) + (1 − t) v(y) ≤ v(t x + (1 − t) y)`.

**Formalization Note.** Values are in `EReal`, with `0 · (−∞) = 0` and `t · (−∞) = −∞` for
`t > 0`; for functions with values in `[−∞, ∞)` this is concavity of the hypograph (the usual
concavity of extended-real functions). -/
def ConcaveOnE (v : ℝ × ℝ → EReal) : Prop :=
  ∀ x ∈ stateSpace, ∀ y ∈ stateSpace, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (t : EReal) * v x + ((1 - t : ℝ) : EReal) * v y
      ≤ v (t * x.1 + (1 - t) * y.1, t * x.2 + (1 - t) * y.2)

end BauerleRiederMDP.TransactionCosts


