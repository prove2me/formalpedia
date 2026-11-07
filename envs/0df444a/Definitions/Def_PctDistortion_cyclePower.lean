-- Prove2me | Definitions.Def_PctDistortion_cyclePower
-- name    : PctDistortion_cyclePower
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:52.114194+00:00
-- url     : https://prove2.me/theorems/16a9e372-9e4c-4930-a404-6e1cd017891c
-- title:
--   The $r$-th power of the directed $\ell$-cycle
-- statement:
--   For integers $\ell\ge 1$ and $r$, $\vec C^{\,r}_\ell$ is the digraph on $\{0,\dots,\ell-1\}$ in which each node points to the next $r$ nodes in cyclic order: $(i,j)$ is an arc iff
--   $$1\le (j-i)\bmod\ell\le r.$$
--   In §4 it is used with $\ell=sr+1$ as the outer digraph $C$ of the construction behind Theorem 2.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §4.1, p.13

import Mathlib

set_option autoImplicit false

namespace PctDistortion

/-- The **`r`-th power of the directed `ℓ`-cycle**, `C = C⃗^r_ℓ`, on the nodes `{0, …, ℓ − 1}`
(`Fin ℓ`): each node points to the next `r` nodes in cyclic order, i.e. `(i, j)` is an arc iff
`1 ≤ (j − i) mod ℓ ≤ r`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §4.1, p.13: "Let C = C⃗^r_ℓ be the rth power of the directed ℓ-cycle C⃗ℓ, i.e., the digraph on
node set {0, . . . , ℓ − 1} in which each node points to the next r nodes in cyclic order. That is,
(i, j) is an arc of C if and only if 1 ≤ (j − i) mod ℓ ≤ r."

**Formalization Note.** Subtraction in `Fin ℓ` is modulo `ℓ`, so `(j - i).val` is
`(j − i) mod ℓ`. -/
def cyclePower (ℓ r : ℕ) : Digraph (Fin ℓ) where
  Adj i j := 1 ≤ (j - i).val ∧ (j - i).val ≤ r

end PctDistortion


