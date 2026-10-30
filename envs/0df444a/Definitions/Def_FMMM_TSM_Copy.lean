-- Prove2me | Definitions.Def_FMMM_TSM_Copy
-- name    : FMMM_TSM_Copy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:16:48.813085+00:00
-- url     : https://prove2.me/theorems/602f6584-8fe1-4c7d-a13c-dc9fb93acfca
-- title:
--   Copies of the impression types
-- statement:
--   Let $I$ be a finite set of impression types with integers $e_i \ge 0$ and $n = \sum_{i \in I} e_i$. The reduction to the case $e_i = 1$ makes $e_i$ copies of each type $i$: the set of **copies** is
--
--   $$I' = \{(i, k) : i \in I,\ 0 \le k < e_i\},$$
--
--   which has $n$ elements. A type with $e_i = 0$ has no copy.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.4, p. 9 (reduction: e_i copies of each impression type)

import Mathlib

namespace FMMM.TSM

/-- **The copies of the impression types (reduction to `e_i = 1`).**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.4, p. 9: "Given a set of instance Γ = (G, D, n), we reduce to a new
instance Γ′ = (G′, D′, n) with e′_i = 1 by making e_i copies of each impression type i."

`Copy e` is the type of pairs `⟨i, k⟩` with `i` an impression type and `k < e i`: the `e i`
copies of type `i`. It has `∑ i, e i = n` elements.

**Formalization Note.** A type with `e i = 0` has no copy. -/
abbrev Copy {I : Type} (e : I → ℕ) : Type := (i : I) × Fin (e i)

end FMMM.TSM


