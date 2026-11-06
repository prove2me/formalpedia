-- Prove2me | Definitions.Def_OrderedExperts_chainPt
-- name    : OrderedExperts_chainPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:36.17627+00:00
-- url     : https://prove2.me/theorems/03ce6e75-6560-4028-97c7-3c2854885f1c
-- title:
--   The $j$-th active action $x_{t,j}$
-- statement:
--   For $1\le j\le m_t$, $x_{t,j}$ is the $j$-th smallest action of the active chain $X_t=\{x_{t,1}\prec\cdots\prec x_{t,m_t}\}$; $j$ is its **rank**. A distribution over $X_t$ is identified with a distribution over the ranks $\{1,\dots,m_t\}$.
--
--   **Formalization Note** Ranks are 1-based natural numbers; outside $1\le j\le m_t$ the value is the junk value $\bot$, which no statement reads.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 2.1, p.4

import Definitions.Def_OrderedExperts_chainSize

namespace OrderedExperts

/-- **The `j`-th active action `xt,j`.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 2.1, p.4:
"`Xt = {at,f : f ∈ F} = {xt,1 ≺ · · · ≺ xt,mt}` [...] We call `j` the rank of `xt,j`".

`chainPt rec t j = xt,j` is the `j`-th smallest distinct recommended action at round `t`, for
`1 ≤ j ≤ mt`.

**Formalization Note.** Ranks are 1-based natural numbers; outside `1 ≤ j ≤ mt` the value is the
junk value `⊥`, which no statement of the mission reads. -/
noncomputable def chainPt {A : Type*} [LinearOrder A] [OrderBot A] {n : ℕ}
    (rec : ℕ → Fin n → A) (t j : ℕ) : A :=
  if h : 1 ≤ j ∧ j ≤ chainSize rec t then
    (active rec t).orderEmbOfFin rfl
      ⟨j - 1, by have h2 := h.2; simp only [chainSize] at h2; omega⟩
  else ⊥

end OrderedExperts


