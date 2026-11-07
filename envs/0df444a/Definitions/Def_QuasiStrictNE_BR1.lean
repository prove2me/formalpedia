-- Prove2me | Definitions.Def_QuasiStrictNE_BR1
-- name    : QuasiStrictNE_BR1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:01.042641+00:00
-- url     : https://prove2.me/theorems/3df394b2-95cd-45f4-b896-2173c46f71c5
-- title:
--   Pure best responses $BR_1(y)$ of player 1
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ be player 1's payoff matrix and $y\in\mathbb R^n$. The set of **pure best responses** of player 1 to $y$ is
--   $$
--   BR_1(y)=\{i\in M : i\in\arg\max_{j\in M} e_j^\top A y\},
--   $$
--   the rows $i$ whose payoff $(Ay)_i$ is maximal.
--
--   **Formalization Note** $M=[m]$ is `Fin m` (0-based).
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 1, p.4

import Mathlib

namespace QuasiStrictNE

open Matrix

/-- **Pure best responses of player 1** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, Definition 1, p.4:
"BR1(y) := {i ∈ M : i ∈ arg max_{j∈M} e_j^⊤ Ay}").

For the payoff matrix `A` of player 1 and a vector `y`, `BR1 A y` is the set of rows `i` whose
payoff `(A y)_i` is maximal among all rows.

**Formalization Note** `M = [m]` is `Fin m` (0-based); `A *ᵥ y` is the vector `A y`. -/
noncomputable def BR1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∀ h, (A *ᵥ y) h ≤ (A *ᵥ y) i)

end QuasiStrictNE


