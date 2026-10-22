-- Prove2me | Definitions.Def_ThinFlowSP_Breakpoints_LCP
-- name    : ThinFlowSP_Breakpoints_LCP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:11.173418+00:00
-- url     : https://prove2.me/theorems/889f1a59-81f7-44cd-b6df-6deb53b4638c
-- title:
--   The linear complementarity problem
-- statement:
--   Let $I$ be a finite index set, $M \in \mathbb R^{I\times I}$ a square matrix and $q \in \mathbb R^I$. A vector $z \in \mathbb R^I$ **solves the linear complementarity problem** with data $(M, q)$ if
--   $$z \ge 0, \qquad Mz - q \ge 0, \qquad z^\top (Mz - q) = 0 .$$
--   The last condition, together with the two sign conditions, says that for every index $i$ at least one of $z_i$ and $(Mz-q)_i$ vanishes.
--
--   This is the general problem class into which Kaiser casts normalized thin flows with resetting (Theorem 6, display (LCP), with $q = \ell'_0\mathbb 1_s + \nu'_0\mathbb 1_t$).
--
--   **Formalization Note** The index set is any finite type; the inequalities are componentwise.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 6, display (LCP)

import Mathlib

namespace ThinFlowSP.Breakpoints

/-- The linear complementarity problem with matrix `M` and right-hand side `q`, on a finite
index type `ι`: `z` solves it if `z ≥ 0`, `M z - q ≥ 0` and `zᵀ (M z - q) = 0`. -/
def SolvesLCP {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (q z : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ z i) ∧ (∀ i, 0 ≤ (M.mulVec z - q) i) ∧ dotProduct z (M.mulVec z - q) = 0

end ThinFlowSP.Breakpoints


