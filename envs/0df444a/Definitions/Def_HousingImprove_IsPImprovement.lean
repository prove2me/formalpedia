-- Prove2me | Definitions.Def_HousingImprove_IsPImprovement
-- name    : HousingImprove_IsPImprovement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:49.205033+00:00
-- url     : https://prove2.me/theorems/de83513d-ca60-4205-a255-46dd88c1f761
-- title:
--   $(p,q)$-improvements and $p$-improvements (corrected)
-- statement:
--   Let $H$ and $H'$ be housing markets on the same agent set $N$, with orders $\prec_a$ and $\prec'_a$, and let $p,q\in N$. Then $H'$ is a **$(p,q)$-improvement** of $H$ if $q\neq p$, $\prec'_a=\prec_a$ for every $a\neq q$, and
--
--   1. $a\prec'_q b$ if and only if $a\prec_q b$, for all $a,b\in N\setminus\{p\}$;
--   2. if $a\prec_q p$ then $a\prec'_q p$, for every $a\in N$;
--   3. if $p\prec'_q a$ then $p\prec_q a$, for every $a\in N$.
--
--   So agent $q$ only "increases the value" of $p$'s house: houses below $p$ stay below it, no house moves above $p$, and the order among the other houses is kept. $H'$ is a **$p$-improvement** of $H$ if it is obtained from $H$ by a sequence of $(p,q_i)$-improvements, $i=1,\dots,k$, for some agents $q_1,\dots,q_k$ (not necessarily distinct; $k=0$ gives $H'=H$).
--
--   **Formalization Note** Clause 3 and $q\neq p$ are not printed on p.9. Without clause 3 a house incomparable to $p$ can move above $p$ and Theorem 2 fails: with $N=\{p,q,a\}$, $p$ ranking $q$ above $a$ above $p$, $a$ ranking $q$ above $a$ (with $p$ unacceptable), and $q$ having $p$ and $a$ incomparable above $q$ in $H$ but $a$ above $p$ above $q$ in $H'$, clauses 1 and 2 hold, the swap $(p\,q)$ is in the core of $H$, and every core allocation of $H'$ gives $p$ the house of $a$ or her own. With $q=p$ the theorem also fails ($p$ raising her own house above the house she obtains). For strict orders clause 3 follows from clause 2.
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, §4, p.9 (definition of (p,q)-improvement and p-improvement), corrected by clause (iii) and q ≠ p

import Mathlib
import Definitions.Def_HousingImprove_Market

namespace HousingImprove

universe u

variable {N : Type u}

/-- `H'` is a **`(p, q)`-improvement** of `H` (Schlotter, Biró, Fleiner, arXiv:2110.06875v3, §4, p.9),
**corrected**: "`≺_a = ≺'_a` for any `a ∈ N \ {q}`, and `≺'_q` is such that (i) `a ≺'_q b` if and only
if `a ≺_q b` for each `a, b ∈ N \ {p}`, and (ii) if `a ≺_q p`, then `a ≺'_q p` for each `a ∈ N`",
plus `q ≠ p` and the added clause (iii) "if `p ≺'_q a`, then `p ≺_q a`, for each `a ∈ N`".

**Formalization Note.** Clause (iii) is a correction: with (i) and (ii) alone, a house incomparable
to `p` for `q` may move strictly above `p`, which lowers `p`'s value, and Theorem 2 fails. For
`N = {p, q, a}` with `p: q ≻ a ≻ p`, `a: q ≻ a` (`p` unacceptable to `a`), `q` ranking `p` and `a`
incomparable above `q` in `H` and `a ≻' p ≻' q` in `H'`, clauses (i), (ii) hold, the swap `(p q)` is
in the core of `H`, and every core allocation of `H'` gives `p` the house of `a` or her own. For
strict total orders (iii) follows from (ii). `q ≠ p` is the reading of "the preferences of `p` remain
unchanged" (p.12); without it Theorem 2 also fails (two agents, `p` raising her own house above
`b`). -/
def IsImprovementAt (p q : N) (H H' : Market N) : Prop :=
  q ≠ p ∧
  (∀ a, a ≠ q → H'.lt a = H.lt a) ∧
  (∀ a b, a ≠ p → b ≠ p → (H'.lt q a b ↔ H.lt q a b)) ∧
  (∀ a, H.lt q a p → H'.lt q a p) ∧
  (∀ a, H'.lt q p a → H.lt q p a)

/-- `ImprovesAlong p [q₁, …, q_k] H H'`: `H'` is obtained from `H` by a sequence of
`(p, q_i)`-improvements, first `q₁`, then `q₂`, …, then `q_k` (arXiv:2110.06875v3, p.9). -/
def ImprovesAlong (p : N) : List N → Market N → Market N → Prop
  | [], H, H' => H' = H
  | q :: qs, H, H' => ∃ H₁, IsImprovementAt p q H H₁ ∧ ImprovesAlong p qs H₁ H'

/-- `H'` is a **`p`-improvement** of `H` (arXiv:2110.06875v3, p.9): "if it can be obtained by a
sequence of `(p, q_i)`-improvements for a series `q₁, …, q_k` of agents for some `k ∈ ℕ`".

**Formalization Note.** `k = 0` is allowed (`H' = H`); the `q_i` need not be distinct. Each
intermediate market is a market (partial orders). -/
def IsPImprovement (p : N) (H H' : Market N) : Prop :=
  ∃ qs : List N, ImprovesAlong p qs H H'

end HousingImprove


