-- Prove2me | Definitions.Def_SweepingDesing_UpperRegularAt
-- name    : SweepingDesing_UpperRegularAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:01.75489+00:00
-- url     : https://prove2.me/theorems/f7ef184a-f292-4d05-a32c-6da46a323a28
-- title:
--   Assumption (A2) — upper regularity at $\bar t$
-- statement:
--   Let $T=\sup\operatorname{dom}(S)\in\mathbb R\cup\{+\infty\}$. The map $S$ satisfies the **upper regular assumption (A2)** at $\bar t\in\operatorname{dom}(S)$ with $\bar t<T$ if there is $\delta>0$ such that
--
--   $$
--   \varphi^\uparrow(t)<+\infty\quad\text{for all }t\in(\bar t,\bar t+\delta).
--   $$
--
--   It says that $\bar t$ is an upper-isolated critical value of the oriented coderivative, the analogue of upper-isolated critical values in the Kurdyka–Łojasiewicz theory.
--
--   **Formalization Note** $\bar t<T$ is encoded as: some $s>\bar t$ has $S(s)\neq\emptyset$.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Assumption (A2), p.8

import Mathlib
import Definitions.Def_SweepingDesing_orientedTalweg
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §3.1, Assumption (A2), p.8: `S` satisfies the *upper regular assumption* at
`t̄ ∈ dom(S)` with `t̄ < T = sup dom(S)` if there exists `δ > 0` with `φ↑(t) < +∞` for all
`t ∈ (t̄, t̄ + δ)`.

**Formalization Note** `t̄ ∈ dom(S)` is `S(t̄) ≠ ∅`; `t̄ < T` is "some `s > t̄` lies in
`dom(S)`" (`T` may be `+∞`). -/
def UpperRegularAt {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (tbar : ℝ) : Prop :=
  (S tbar).Nonempty ∧ (∃ s, tbar < s ∧ (S s).Nonempty) ∧
    ∃ δ > (0 : ℝ), ∀ t ∈ Ioo tbar (tbar + δ), orientedTalweg S t < ⊤

end SweepingDesing


