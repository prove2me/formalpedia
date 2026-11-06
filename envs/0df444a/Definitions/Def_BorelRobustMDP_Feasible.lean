-- Prove2me | Definitions.Def_BorelRobustMDP_Feasible
-- name    : BorelRobustMDP_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:05.619203+00:00
-- url     : https://prove2.me/theorems/071c778b-8608-4b69-97a5-a852089a04d9
-- title:
--   Feasible histories $\mathcal H_n$
-- statement:
--   A history $h_n=(x_0,a_0,x_1,\dots,x_n)$ is **feasible** if $a_k\in D_k(x_k)$ for every $k<n$. The feasible histories form the set $\mathcal H_n$.
--
--   **Formalization Note.** This predicate cuts $\mathcal H_n$ out of the platform's raw history space.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, §2, p.3

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_DecisionModel

open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- `h_n = (x_0, a_0, x_1, …, x_n)` is a feasible history, i.e. a point of `𝓗_n`: `a_k ∈ D_k(x_k)` for
every `k < n` (Bäuerle & Glauner, arXiv:2007.13103v1, p.3).

**Formalization Note.** `Hist E A n` is the platform's raw history space `E × (A × E)^n`; this
predicate cuts out `𝓗_n`, which is a measurable subset of it. -/
def DecisionModel.Feasible (M : DecisionModel E A Z N) : (n : ℕ) → Hist E A n → Prop
  | 0, _ => True
  | n + 1, h =>
      let w : Hist E A n × A × E := h
      DecisionModel.Feasible M n w.1 ∧ (histState n w.1, w.2.1) ∈ M.D n

end BorelRobustMDP


