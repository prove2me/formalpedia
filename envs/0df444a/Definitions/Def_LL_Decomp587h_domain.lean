-- Prove2me | Definitions.Def_LL_Decomp587h_domain
-- name    : LL_Decomp587h_domain
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T01:07:14.096229+00:00
-- url     : https://prove2.me/theorems/84114ea2-f276-4f9d-a93c-f4c0d51c78fd
-- title:
--   Box intersected with the ordered simplex
-- statement:
--   For $n\in\mathbb N$ and vectors $\ell,h\in\mathbb R^n$, indexed by $\{0,\dots,n-1\}$, the set of $x\in\mathbb R^n$ that are monotone, meaning $x_i\le x_j$ whenever $i\le j$, and satisfy $\ell_j\le x_j\le h_j$ for every $j$.

import Mathlib

open Real Set MeasureTheory
open scoped Classical

namespace LL_Decomp587h

def domain {n : ℕ} (lo hi : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | Monotone x ∧ ∀ j, lo j ≤ x j ∧ x j ≤ hi j}

end LL_Decomp587h


