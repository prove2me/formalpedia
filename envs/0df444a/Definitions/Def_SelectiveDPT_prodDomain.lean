-- Prove2me | Definitions.Def_SelectiveDPT_prodDomain
-- name    : SelectiveDPT_prodDomain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:34.895923+00:00
-- url     : https://prove2.me/theorems/ee912ec9-f3e6-40f1-94ad-5ee681109ac1
-- title:
--   Product domain $D^m$
-- statement:
--   For a domain $D \subseteq X^\iota$ and $m \ge 0$, the **product domain** $D^m$ is the set of $m$-copy inputs $x = (x_1, \dots, x_m)$ with $x_j \in D$ for every copy $j \in [m]$, viewed as a subset of $X^{[m] \times \iota}$.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.2, p.10 (x ∈ D^m)

import Mathlib
import Definitions.Def_SelectiveDPT_copy

namespace SelectiveDPT

/-- The product domain `D^m ⊆ (X^n)^m` of `m`-copy inputs all of whose copies lie in `D`
(arXiv:2609.26678, §2.2, p.10: "`x ∈ D^m`"). -/
def prodDomain {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (m : ℕ) : Finset (Fin m × ι → ZMod d) :=
  Finset.univ.filter fun x => ∀ j, copy x j ∈ D

end SelectiveDPT


