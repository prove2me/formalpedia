-- Prove2me | Definitions.Def_LL_Decomp587f_domain
-- name    : LL_Decomp587f_domain
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T01:00:19.731231+00:00
-- url     : https://prove2.me/theorems/10975263-630e-4da4-8bc9-48b624c23cfb
-- title:
--   Box intersected with the ordered simplex
-- statement:
--   For $n\in\mathbb N$ and vectors $\ell,h\in\mathbb R^n$, indexed by $\{0,\dots,n-1\}$, the set of $x\in\mathbb R^n$ that are monotone, meaning $x_i\le x_j$ whenever $i\le j$, and satisfy $\ell_j\le x_j\le h_j$ for every $j$.

import Mathlib

open Real Set MeasureTheory
open scoped Classical

namespace LL_Decomp587f

def domain {n : ℕ} (lo hi : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | Monotone x ∧ ∀ j, lo j ≤ x j ∧ x j ≤ hi j}

end LL_Decomp587f


