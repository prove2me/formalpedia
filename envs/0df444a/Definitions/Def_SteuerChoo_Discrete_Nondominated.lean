-- Prove2me | Definitions.Def_SteuerChoo_Discrete_Nondominated
-- name    : SteuerChoo_Discrete_Nondominated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:42:57.460921+00:00
-- url     : https://prove2.me/theorems/2c16772f-a428-4601-acca-e33dd57f8a6a
-- title:
--   Steuer–Choo §1: dominance, the nondominated set N, maximizers of an objective
-- statement:
--   Consider a multiple objective program with $k \ge 1$ objectives, $\max f_1(x), \dots, \max f_k(x)$ subject to $x \in S$, and let $Z \subset \mathbb R^k$ be its set of feasible criterion vectors (the image of $S$ under $(f_1,\dots,f_k)$). This file fixes three notions for a finite set $Z$.
--
--   1. **Dominance.** A vector $z \in \mathbb R^k$ *dominates* $\bar z \in \mathbb R^k$ if $z_i \ge \bar z_i$ for all $i$ and $z_i > \bar z_i$ for at least one $i$.
--   2. **Nondominated set.** A vector $\bar z \in Z$ is *nondominated* if no $z \in Z$ dominates it:
--   $$N = \{\bar z \in Z \mid \nexists\, z \in Z \text{ with } z_i \ge \bar z_i \ \forall i \text{ and } z_i > \bar z_i \text{ for some } i\}.$$
--   3. **Maximizer of an objective.** A vector $z$ *maximizes the $i$-th objective* over $Z$ if $z \in Z$ and $w_i \le z_i$ for every $w \in Z$.
--
--   These are the basic objects of multiple objective programming: $N$ is the set the interactive procedure samples, and the maximizers of the individual objectives enter the definition of the ideal criterion vector.
--
--   **Formalization Note** Criterion vectors are functions $\mathrm{Fin}\,k \to \mathbb R$, so the paper's objective index $i = 1,\dots,k$ becomes $i = 0,\dots,k-1$. The decision set $S$ and the objectives $f_i$ are eliminated: $Z$ is given directly as a finite set (`Finset`), which is the paper's discrete case ($S$ discrete, hence $Z$ finite). $N$ is returned as a `Finset`.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, p. 326, §1, definition of nondominated criterion vector and N

import Mathlib

/-!
# Steuer–Choo (1983), §1: dominance, the nondominated set, maximizers of an objective

R. E. Steuer and E.-U. Choo, *An Interactive Weighted Tchebycheff Procedure for Multiple Objective
Programming*, Math. Programming 26 (1983), §1, p. 326.

The multiple objective program is `max {f₁(x) = z₁}, …, max {f_k(x) = z_k}, s.t. x ∈ S`, and `Z` is
the set of feasible criterion vectors (the image of `S` under the `fᵢ`). Here `Z` is given directly
as a finite set of vectors `Fin k → ℝ` (the paper's objective index `i = 1, …, k` is `i : Fin k`).
-/

namespace SteuerChoo.Discrete

/-- `Dominates z zbar`: `zᵢ ≥ z̄ᵢ` for all `i` and `zᵢ > z̄ᵢ` for at least one `i`
(Steuer–Choo 1983, §1, p. 326). -/
def Dominates {k : ℕ} (z zbar : Fin k → ℝ) : Prop :=
  (∀ i, zbar i ≤ z i) ∧ ∃ i, zbar i < z i

/-- The set `N ⊆ Z` of nondominated criterion vectors: `z̄ ∈ Z` such that no `z ∈ Z` dominates `z̄`
(Steuer–Choo 1983, §1, p. 326). -/
noncomputable def nondominated {k : ℕ} (Z : Finset (Fin k → ℝ)) : Finset (Fin k → ℝ) := by
  classical
  exact Z.filter (fun zbar => ¬ ∃ z ∈ Z, Dominates z zbar)

/-- `MaximizesObj Z i z`: the criterion vector `z ∈ Z` maximizes the `i`-th objective over `Z`. -/
def MaximizesObj {k : ℕ} (Z : Finset (Fin k → ℝ)) (i : Fin k) (z : Fin k → ℝ) : Prop :=
  z ∈ Z ∧ ∀ w ∈ Z, w i ≤ z i

end SteuerChoo.Discrete


