-- Prove2me | Definitions.Def_MegiddoLP_FixedDim_Infeasibility
-- name    : MegiddoLP_FixedDim_Infeasibility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:08:06.986401+00:00
-- url     : https://prove2.me/theorems/6bea5960-6468-4b0d-8940-ba4ce494151a
-- title:
--   The infeasibility function $f(x)=\max_i\,(b_i-a_i^Tx)$
-- statement:
--   For a system of linear inequalities $\sum_{j=1}^d a_{ij}x_j\ge b_i$ $(i=1,\dots,n)$ with at least one inequality, the **infeasibility function** is
--
--   $$f(x_1,\dots,x_d)=\max\Big\{b_i-\sum_{j=1}^d a_{ij}x_j:\ i=1,\dots,n\Big\}.$$
--
--   It is convex and piecewise linear, and $x$ satisfies the system exactly when $f(x)\le0$. Megiddo's linear programming procedure returns a minimizer of $f$ when the problem is infeasible. The recursion needs this output to decide on which side of a hyperplane to continue.
--
--   **Formalization Note** The rows are indexed by `Fin (n + 1)`, so the maximum is over a nonempty finite set and has no junk value. It is a finite `sup'`, not a real `iSup`.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §4, p. 123 (definition of f)

import Mathlib

/-!
The infeasibility function of a linear system (Megiddo, J. ACM 31 (1984), §4, p. 123).

For the system `Σⱼ a_ij xⱼ ≥ bᵢ (i = 1, …, n)` the paper defines
`f(x) = max {bᵢ - Σⱼ a_ij xⱼ : i = 1, …, n}`. It is defined here for a system with at
least one constraint (rows indexed by `Fin (n + 1)`), so the maximum is over a nonempty
finite set; `x` satisfies the system iff `f x ≤ 0`.
-/

namespace MegiddoLP.FixedDim

/-- `f(x) = max_i (bᵢ - Aᵢ ⬝ᵥ x)` over the `n + 1` rows of `A`. -/
noncomputable def infeas {n d : ℕ} (A : Matrix (Fin (n + 1)) (Fin d) ℝ) (b : Fin (n + 1) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => b i - A i ⬝ᵥ x)

end MegiddoLP.FixedDim


