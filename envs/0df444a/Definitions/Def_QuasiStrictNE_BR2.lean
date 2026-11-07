-- Prove2me | Definitions.Def_QuasiStrictNE_BR2
-- name    : QuasiStrictNE_BR2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:05:57.74808+00:00
-- url     : https://prove2.me/theorems/84494214-98e5-41fb-b8cb-18bf325b1c6d
-- title:
--   Pure best responses $BR_2(x)$ of player 2
-- statement:
--   Let $B\in\mathbb R^{m\times n}$ be player 2's payoff matrix and $x\in\mathbb R^m$. The set of **pure best responses** of player 2 to $x$ is
--   $$
--   BR_2(x)=\{j\in N : j\in\arg\max_{\ell\in N} x^\top B e_\ell\},
--   $$
--   the columns $j$ whose payoff $(B^\top x)_j$ is maximal.
--
--   **Formalization Note** $N=[n]$ is `Fin n` (0-based).
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 1, p.4

import Mathlib

namespace QuasiStrictNE

open Matrix

/-- **Pure best responses of player 2** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, Definition 1, p.4:
"BR2(x) := {i ∈ N : i ∈ arg max_{j∈N} x^⊤ B e_j}").

For the payoff matrix `B` of player 2 and a vector `x`, `BR2 B x` is the set of columns `j` whose
payoff `(x^⊤ B)_j = (B^⊤ x)_j` is maximal among all columns.

**Formalization Note** `N = [n]` is `Fin n` (0-based); `x ᵥ* B` is the row vector `x^⊤ B`. -/
noncomputable def BR2 {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∀ l, (x ᵥ* B) l ≤ (x ᵥ* B) j)

end QuasiStrictNE


