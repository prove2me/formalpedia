-- Prove2me | Definitions.Def_Farey
-- name    : Farey
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-10T10:46:06.374517+00:00
-- url     : https://prove2.me/theorems/27dded92-b965-4636-b610-25311a34f3fd
-- title:
--   Farey pairs of order $P$: the index set of the Farey dissection
-- statement:
--   The **Farey pairs of order $P$** are the pairs $(q,a)$ of natural numbers with $$1 \le a \le q \le P, \qquad \gcd(a,q)=1.$$ The first component is the denominator and the second the numerator, so $(q,a)$ represents the fraction $a/q \in (0,1]$ written in lowest terms. Collected as a `Finset (ℕ × ℕ)`, this is the index set of the **Farey dissection** of order $P$: in the Hardy–Littlewood circle method each pair labels one major arc, centred at $a/q$.
--
--   The convention here excludes $0/1$ and includes $1/1$, which is what the circle method wants; the classical Farey sequence $F_P$ additionally contains $0/1$.
-- source:
--   Standard. See e.g. R. C. Vaughan, The Hardy-Littlewood Method, 2nd ed., Cambridge University Press 1997, Chapter 2 (Farey dissection and major arcs); Hardy & Wright, An Introduction to the Theory of Numbers, Chapter III (Farey series).

import Mathlib

namespace Farey

/-- The **Farey pairs** of order `P`: all pairs `(q, a)` of natural numbers with
`1 ≤ a ≤ q ≤ P` and `a` coprime to `q`.

The first component is the *denominator* and the second the *numerator*, so the pair
`(q, a)` represents the fraction `a / q ∈ (0, 1]` in lowest terms.  This is the index set of
the Farey dissection used in the Hardy–Littlewood circle method, where each pair labels one
major arc centred at `a / q`.

Note that `0/1` is excluded and `1/1` is included, which is the convention the circle method
wants; the classical Farey sequence `F_P` additionally contains `0/1`. -/
def pairs (P : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 P).biUnion fun q =>
    ((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a => (q, a)

end Farey


