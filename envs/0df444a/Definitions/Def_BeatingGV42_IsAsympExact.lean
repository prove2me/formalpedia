-- Prove2me | Definitions.Def_BeatingGV42_IsAsympExact
-- name    : BeatingGV42_IsAsympExact
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:33:08.942391+00:00
-- url     : https://prove2.me/theorems/797d60b6-9f9d-4fa4-80b6-c9ee3b873934
-- title:
--   Asymptotically exact sequence of function fields with limits $\beta_r$
-- statement:
--   Let $(F_i/\mathbb F_Q)_{i\ge 1}$ be a sequence of function fields with genera $g_i\to\infty$ and let $B_r(F_i)$ be the number of places of degree $r$ of $F_i$. The sequence is **asymptotically exact** if for every $r\ge 1$ the limit
--   $$
--   \beta_r=\lim_{i\to\infty}\frac{B_r(F_i)}{g_i}
--   $$
--   exists. Theorem 4.7 bounds $\sum_r r\beta_r/(Q^{r/2}-1)$ for such sequences.
--
--   **Formalization Note** `IsAsympExact Fs β` states $g_i\to\infty$ and $B_r(F_i)/g_i\to\beta(r)$ for every $r\ge 1$; "the limits exist" is $\exists\beta$, and they are then unique. $\beta(0)$ is unused.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §4.3 and Definition 4.6, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_BeatingGV42_FunctionFieldOver
import Definitions.Def_BeatingGV42_numPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter Topology

universe u

namespace BeatingGV42

/-- **Asymptotically exact sequence of function fields, with limits `β_r`** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.3 and
Definition 4.6, p.17 (PDF p.19)): "The sequence is asymptotically exact if for all r ≥ 1, the limit
β_r := lim_{i→∞} B_r(F_i)/g_i exists."

**Formalization Note** `IsAsympExact Fs β` says that the sequence has genera `g_i → ∞` (the §4.3
standing assumption) and that `B_r(F_i)/g_i → β r` for every `r ≥ 1`; "the limits exist" is
`∃ β, IsAsympExact Fs β`, and the limits are then unique. `β 0` is unconstrained and unused. -/
def IsAsympExact {k : Type u} [Field k] (Fs : ℕ → FunctionFieldOver k) (β : ℕ → ℝ) : Prop :=
  Tendsto (fun i => AlgebraicCurve.genusFF k (Fs i).carrier) atTop atTop ∧
    ∀ r : ℕ, 1 ≤ r →
      Tendsto (fun i => (numPlaces k (Fs i).carrier r : ℝ) /
          (AlgebraicCurve.genusFF k (Fs i).carrier : ℝ)) atTop (𝓝 (β r))

end BeatingGV42


