-- Prove2me | Definitions.Def_MemQueryFeas_IsMeasurableAdaptive
-- name    : MemQueryFeas_IsMeasurableAdaptive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:26.40396+00:00
-- url     : https://prove2.me/theorems/4312e706-1b51-467b-acd7-2bda4dc080ef
-- title:
--   Measurable adaptive oracle
-- statement:
--   An adaptive oracle $O$ is **measurable** if, for every history length $n$, on $(\mathbb R^d)^n\times\mathbb R^d$ the set of (history, query) pairs answered with Success is a Borel set and the returned normal (taken to be $0$ on Success) is a Borel function of the history and the query.
--
--   Probabilities of events of a run of a randomized algorithm against an oracle are defined for such oracles.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4); Theorem 1, p.2

import Mathlib
import Definitions.Def_MemQueryFeas_Vec

namespace MemQueryFeas

/-- **Measurable adaptive oracle.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4), and the success probability
of Theorem 1, p.2: probabilities of events of a run against an oracle are taken over the algorithm's
randomness, which presupposes that the oracle's response is a measurable function of the history
and the query.

`IsMeasurableAdaptive O`: for every history length `n`, on `(ℝ^d)^n × ℝ^d` the Success region
`{(h, x) | O h x = none}` is Borel and the returned normal (with `0` on Success) is Borel measurable.

**Formalization Note.** The history `[x_0, …, x_{n-1}]` is read as a vector `Fin n → Vec d`
(`List.ofFn`). -/
def IsMeasurableAdaptive {d : ℕ} (O : List (Vec d) → Vec d → Option (Vec d)) : Prop :=
  ∀ n : ℕ,
    Measurable (fun z : (Fin n → Vec d) × Vec d => (O (List.ofFn z.1) z.2).getD 0) ∧
    MeasurableSet {z : (Fin n → Vec d) × Vec d | O (List.ofFn z.1) z.2 = none}

end MemQueryFeas


