-- Prove2me | Definitions.Def_FreeOrderEPTAS_IPFeasible
-- name    : FreeOrderEPTAS_IPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:20.106112+00:00
-- url     : https://prove2.me/theorems/76a8be0a-23a2-4e24-a08c-c01e97b98b72
-- title:
--   The integer program (IP)
-- statement:
--   For a binary matrix $x$ the constraints of (IP) are
--   $$\sum_{i\in[m]}x_{ij}\le1\ \ \forall j,\qquad \sum_{j\in[n]}x_{ij}\le k_i\ \ \forall i,\qquad \sum_{j\in[n]}\ell_{ijd}x_{ij}\ge1\ \ \forall i,\ d\in A_i .$$
--   `MeetsCard` is (II) and (III). `LoadAtLeast I x c` is the third family with right-hand side $c$, so $c=1$ is (IV) and $c=1-\epsilon$ is "(IV) is $\epsilon$-violated". `IPFeasible` says that (IP) has a solution.
--
--   These are the hypothesis and the conclusion of Theorem 2.1.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.1, p.8

import Mathlib
import Definitions.Def_FreeOrderEPTAS_SCInstance

namespace FreeOrderEPTAS

variable {m D n : ℕ}

/-- The load `∑_j ℓ_ijd x_ij` of machine `i` along dimension `d`. -/
noncomputable def load (I : SCInstance m D n) (x : Assignment m n) (i : Fin m) (d : Fin D) : ℝ :=
  ∑ j, I.ℓ i j d * bit (x i j)

/-- Constraints (II) and (III) of (IP) (arXiv:2007.13121v3, p.8): each job is on at most one
machine, and machine `i` has at most `k_i` jobs. Constraint (I) is the type `Assignment`. -/
def MeetsCard (I : SCInstance m D n) (x : Assignment m n) : Prop :=
  (∀ j, (Finset.univ.filter fun i => x i j = true).card ≤ 1) ∧
    ∀ i, (Finset.univ.filter fun j => x i j = true).card ≤ I.k i

/-- Constraint (IV) of (IP) with right-hand side `c`: `∑_j ℓ_ijd x_ij ≥ c` for `i ∈ [m]`, `d ∈ A_i`.
With `c = 1` it is (IV); with `c = 1 - ϵ` it is "(IV) is ϵ-violated" (Theorem 2.1, p.8). -/
def LoadAtLeast (I : SCInstance m D n) (x : Assignment m n) (c : ℝ) : Prop :=
  ∀ i, ∀ d ∈ I.A i, c ≤ load I x i d

/-- (IP) is feasible (arXiv:2007.13121v3, p.8). -/
def IPFeasible (I : SCInstance m D n) : Prop :=
  ∃ x, MeetsCard I x ∧ LoadAtLeast I x 1

end FreeOrderEPTAS


