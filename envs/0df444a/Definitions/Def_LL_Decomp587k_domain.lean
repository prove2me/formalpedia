-- Prove2me | Definitions.Def_LL_Decomp587k_domain
-- name    : LL_Decomp587k_domain
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:41:30.740142+00:00
-- url     : https://prove2.me/theorems/242787d6-3223-40a2-9ade-5e98159a12e7
-- title:
--   Box intersected with the ordered simplex
-- statement:
--   For $n\in\mathbb N$ and vectors $\ell,h\in\mathbb R^n$, indexed by $\{0,\dots,n-1\}$, the set of $x\in\mathbb R^n$ that are monotone, meaning $x_i\le x_j$ whenever $i\le j$, and satisfy $\ell_j\le x_j\le h_j$ for every $j$.

import Mathlib

namespace LL_Decomp587k

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def domain {n : ℕ} (lo hi : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | Monotone x ∧ ∀ j, lo j ≤ x j ∧ x j ≤ hi j}

end

end LL_Decomp587k


