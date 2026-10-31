-- Prove2me | Definitions.Def_PriceRobustness_Main_LinearProgram
-- name    : PriceRobustness_Main_LinearProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:38:01.562386+00:00
-- url     : https://prove2.me/theorems/2064d471-1b69-4b84-8877-40c31cf78d53
-- title:
--   Box-constrained linear maximization
-- statement:
--   A linear program has a real matrix $A$, right-hand side $b$, objective coefficients $c$, and real lower and upper bounds $l,u$. Its decision vector $x$ is unrestricted in sign. Feasibility and optimality mean
--   $$Ax\le b,\quad l\le x\le u,\qquad c^Tx'\le c^Tx\text{ for every feasible }x'.$$
--   The optimality predicate also requires $x$ itself to be feasible. No existence, uniqueness, rank or nondegeneracy assumption is bundled. Rows and columns are indexed by `Fin m` and `Fin N`, allowing zero dimensions. This general object is separate from the paper-specific robust model.
-- source:
--   Bertsimas and Sim, The Price of Robustness, authors' preprint, August 2001; revised August, 2002; PDF SHA-256 63f0bffaff9128b706a084acc869e1020ce79adf86108ac23b5b0dd598f189cb; §2.1, p. 4

import Mathlib

open scoped BigOperators

namespace PriceRobustness.Main

structure LinearProgram (m N : ℕ) where
  A : Fin m → Fin N → ℝ
  b : Fin m → ℝ
  c : Fin N → ℝ
  lower : Fin N → ℝ
  upper : Fin N → ℝ

def LinearProgram.objective {m N : ℕ} (L : LinearProgram m N) (x : Fin N → ℝ) : ℝ :=
  ∑ j, L.c j * x j

def LinearProgram.Feasible {m N : ℕ} (L : LinearProgram m N) (x : Fin N → ℝ) : Prop :=
  (∀ i, ∑ j, L.A i j * x j ≤ L.b i) ∧
  (∀ j, L.lower j ≤ x j ∧ x j ≤ L.upper j)

def LinearProgram.Optimal {m N : ℕ} (L : LinearProgram m N) (x : Fin N → ℝ) : Prop :=
  L.Feasible x ∧ ∀ x', L.Feasible x' → L.objective x' ≤ L.objective x

end PriceRobustness.Main


