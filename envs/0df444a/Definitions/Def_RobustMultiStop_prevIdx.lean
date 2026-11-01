-- Prove2me | Definitions.Def_RobustMultiStop_prevIdx
-- name    : RobustMultiStop_prevIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:53.019296+00:00
-- url     : https://prove2.me/theorems/0511597d-cabc-4939-b688-5d0bdc2cb496
-- title:
--   Predecessor index $j_{k-1}$ with $j_0=t$
-- statement:
--   For a vector $(j_1,\dots,j_L)$ and a start value $t$, the **predecessor** of the $k$-th entry is
--
--   $$j_{k-1}\quad (k\ge2),\qquad j_0:=t\quad(k=1).$$
--
--   It is used for exercise dates in the dual (3.1)–(3.3) and Proposition 4.4, and for stopping times in (B.1), with $\tau_0:=t$.
--
--   **Formalization Note** $0$-based: `prevIdx t j k` is `t` for `k = 0` and `j (k - 1)` otherwise.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, proof of Theorem 3.1, p.41 ("with j_0 = t"), and Proposition 4.4, p.15 ("with j_0 = i")

import Mathlib

namespace RobustMultiStop

/-- The predecessor index `j_{k−1}` with the convention `j_0 = t`, Laeven, Schoenmakers, Schweizer
& Stadje, *Robust Multiple Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, proof of
Theorem 3.1, p.41 ("with `j_0 = t`"), and Proposition 4.4, p.15 ("with `j_0 = i`").

For a `0`-based vector `j : Fin L → α` and a start value `t`, `prevIdx t j k` is `t` if `k = 0` and
`j (k - 1)` otherwise. It is used both for exercise dates (`α = ℕ`) and for stopping times
(`α = Ω → ℕ`, the paper's `τ_{k−1}` with `τ_0 := t`, (B.1), p.40). -/
def prevIdx {α : Type*} {L : ℕ} (t : α) (j : Fin L → α) (k : Fin L) : α :=
  if h : (k : ℕ) = 0 then t else j ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩

end RobustMultiStop


