-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_OddTransversal
-- name    : MatroidOptGame_Supplement_OddTransversal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:49:39.863207+00:00
-- url     : https://prove2.me/theorems/111ab8d5-611d-4f3c-b1c9-06adb6e0ef88
-- title:
--   Odd transversals $H$ of the pairs $\{2i,2i+1\}$
-- statement:
--   A set $H\subseteq E_n=\{0,\dots,2n-1\}$ is an **odd transversal** if it contains exactly one element of each pair $\{2i,2i+1\}$ and $|H\cap S_1|$ is odd, where $S_1$ is the set of odd elements. There are $2^{n-1}$ odd transversals. They index the family $\mathcal M_{n,H}$, and in Theorem 14 $H$ is drawn uniformly at random from them.
--
--   **Formalization Note** The type is the finite subtype of $\mathrm{Finset}(\mathrm{Fin}\,2n)$ cut out by the two conditions. $H$ and $\bar H=E_n\setminus H$ give the same matroid (for even $n$); the law is uniform over $H$, as in the paper.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.2, p.14 (definition), p.15 (uniform law)

import Mathlib
import Definitions.Def_MatroidOptGame_Supplement_partner

namespace MatroidOptGame.Supplement

/-- The odd transversals of the pairing `{2i, 2i+1}` of `E_n = Fin (2n)`: sets `H` containing
exactly one element of every pair, with `|H ∩ S₁|` odd, where `S₁` is the set of odd elements.
These index the Theorem 14 family `M_{n,H}`.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.2, p.14 ("A transversal means a set that contains one and only one element
from each pair, and the parity of a transversal is the parity of the cardinality of its
intersection with S₁ = E_n ∖ S₀"; "Choose one odd transversal H"); p.15 ("H is drawn uniformly at
random from the set of odd parity transversals").
**Formalization Note.** `H ∩ S₁` is written `H.filter (odd value)`. There are `2^{n−1}` such
`H`; `H` and its complement give the same matroid, and the law is uniform over the `H`, as in
the paper. -/
abbrev OddTransversal (n : ℕ) : Type :=
  {H : Finset (Fin (2 * n)) //
    (∀ i, i ∈ H ↔ partner n i ∉ H) ∧ Odd (H.filter (fun i => i.val % 2 = 1)).card}

end MatroidOptGame.Supplement


