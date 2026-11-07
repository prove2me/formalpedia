-- Prove2me | Definitions.Def_GSRandomOrder_contract
-- name    : GSRandomOrder_contract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:46.416179+00:00
-- url     : https://prove2.me/theorems/f478024d-259a-4a21-a422-82efeac1d267
-- title:
--   Contraction $v/x$ of a valuation, eq. (4)
-- statement:
--   For a valuation $v$ and an item $x$ with $v(\{x\})>-\infty$, the **contraction** $v/x$ is
--   $$
--   (v/x)(T)=v(T+x)-v(\{x\}),\qquad T\subseteq N-x.
--   $$
--   It describes the valuation of the remaining items when $x$ has already been taken. The survival algorithm compares the survival law of $v$ with that of $v/x$ when $x$ arrives.
--
--   **Formalization Note** The contraction is defined on every subset $T\subseteq$ `Fin n`; on a set containing $x$ it equals $(v/x)(T-x)$, so $x$ behaves as a dummy item. It is used only when $v(\{x\})\ne-\infty$, and then it subtracts the real number $v(\{x\})$; $-\infty$ minus a real number is $-\infty$. Labels are those of $N$.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §2.1, p.6, eq. (4)

import Mathlib

set_option autoImplicit false

namespace GSRandomOrder

/-- **Contraction** `v/x` (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §2.1, p.6, eq. (4)):
`(v/x)(T) = v(T + x) − v({x})` for `T ⊆ N − x`, when `v({x}) > −∞`.

**Formalization Note.** The contraction is defined on every finite set `T ⊆ Fin n`: on a set that
contains `x` it gives `(v/x)(T − x)`, so `x` acts as a dummy item. Only sets `T` with `x ∉ T` are
meaningful, and the contraction is only used when `v {x} ≠ ⊥` (it then subtracts the real number
`v({x})`; the `0` fallback of `unbotD` is never reached in that case). Subtraction of a real
number from `−∞` gives `−∞` (`WithBot.map`). Labels are inherited from `N`. -/
noncomputable def contract {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (x : Fin n)
    (T : Finset (Fin n)) : WithBot ℝ :=
  (v (insert x T)).map fun a => a - (v {x}).unbotD 0

end GSRandomOrder


