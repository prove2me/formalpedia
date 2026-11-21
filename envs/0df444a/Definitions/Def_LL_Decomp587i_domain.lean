-- Prove2me | Definitions.Def_LL_Decomp587i_domain
-- name    : LL_Decomp587i_domain
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:35:49.069846+00:00
-- url     : https://prove2.me/theorems/487727de-48b6-4b66-b563-88ff57df906d
-- title:
--   Box intersected with the ordered simplex
-- statement:
--   For $n\in\mathbb N$ and vectors $\ell,h\in\mathbb R^n$, indexed by $\{0,\dots,n-1\}$, the set of $x\in\mathbb R^n$ that are monotone, meaning $x_i\le x_j$ whenever $i\le j$, and satisfy $\ell_j\le x_j\le h_j$ for every $j$.

import Mathlib

namespace LL_Decomp587i

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def domain {n : ℕ} (lo hi : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | Monotone x ∧ ∀ j, lo j ≤ x j ∧ x j ≤ hi j}

end

end LL_Decomp587i


