-- Prove2me | Definitions.Def_OrderedExperts_active
-- name    : OrderedExperts_active
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:45.727191+00:00
-- url     : https://prove2.me/theorems/35cedf0a-5f52-4e1c-bd4f-a0e08ea8ea42
-- title:
--   The active chain $X_t$
-- statement:
--   On round $t$ every expert $f$ of a finite class $\mathcal F$ recommends an action $a_{t,f}$ in a totally ordered action space. The **active chain** is the set of distinct recommended actions,
--   $$
--   X_t=\{a_{t,f}:f\in\mathcal F\}=\{x_{t,1}\prec\cdots\prec x_{t,m_t}\},\qquad m_t\le|\mathcal F|.
--   $$
--
--   **Formalization Note** Experts are $\mathrm{Fin}\,n$ with $n=|\mathcal F|$; the recommendations are a function of the round and the expert.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 2.1, p.4

import Mathlib

namespace OrderedExperts

/-- **The active chain of round `t`.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 2.1, p.4: "Let
`Xt = {at,f : f ∈ F} = {xt,1 ≺ · · · ≺ xt,mt}`, `mt ≤ |F|`, be the distinct active actions at round
`t`."

For recommendations `rec t f = at,f` of the experts `f ∈ Fin n`, `active rec t` is the finite set of
distinct recommended actions at round `t`.

**Formalization Note.** Experts are `Fin n` (`|F| = n`) and rounds are natural numbers. -/
def active {A : Type*} [LinearOrder A] {n : ℕ} (rec : ℕ → Fin n → A) (t : ℕ) : Finset A :=
  Finset.univ.image (rec t)

end OrderedExperts


