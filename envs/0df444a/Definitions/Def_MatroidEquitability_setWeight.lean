-- Prove2me | Definitions.Def_MatroidEquitability_setWeight
-- name    : MatroidEquitability_setWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:46.531948+00:00
-- url     : https://prove2.me/theorems/b590f5ec-0960-45a8-bfcc-dcd670a1d126
-- title:
--   Weight $x(A)=\sum_{e\in A}x_e$ of a set
-- statement:
--   For a vector $x\in\mathbb R^E$ and a set $A\subseteq E$, the **weight** of $A$ is
--
--   $$
--   x(A):=\sum_{e\in A}x_e .
--   $$
--
--   Every balance condition of the mission compares weights of this form.
--
--   **Formalization Note** The vector is a function on the whole type and the sum is a `finsum`. A `finsum` over a set on which $x$ has infinite support is $0$, but the mission applies it only to subsets of a finite ground set, where it is the genuine sum.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), §1.3, p.7 (PDF p.9)

import Mathlib

namespace MatroidEquitability

/-- The weight `x(A) := Σ_{e∈A} x_e` of a set `A` under a vector `x` (§1.3, printed p.7 = PDF p.9 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** Sets are `Set α` and the sum is a `finsum`. A `finsum` over a set on which
`x` has infinite support is `0`; every statement of this mission applies `setWeight` only to subsets
of a finite ground set, where it is the genuine sum. -/
noncomputable def setWeight {α : Type*} (x : α → ℝ) (A : Set α) : ℝ :=
  ∑ᶠ e ∈ A, x e

end MatroidEquitability


