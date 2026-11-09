-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_EmptyMinProblem
-- name    : SFMQueryLower_EmptyMin_EmptyMinProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:49.991297+00:00
-- url     : https://prove2.me/theorems/45cfb88b-d0ec-4c41-89dc-03ee77797e0f
-- title:
--   Empty-set minimizer testing and randomized query complexity
-- statement:
--   For a real-valued set function $f:2^{[n]}\to\mathbb R$, let $\operatorname{EmptyMin}(f)$ mean that $f(\varnothing)\le f(S)$ for every subset $S$. An algorithm's failure event includes returning the wrong Boolean answer and failing to return an answer. Correctness with error at most $\delta$ is imposed separately on each lattice-submodular input.
--
--   Writing $Q(A,f)$ for its actual query count, define
--   $$W(A)=\sup_{f\ \mathrm{submodular}}\mathbb E Q(A,f),\qquad R_\delta(\operatorname{EmptyMin}_n)=\inf_{A\ \mathrm{correct\ at\ error}\ \delta} W(A).$$
--   The definition is used for $0\le\delta<1/2$. Values, suprema and infima lie in $[0,\infty]$, without assuming finite expected cost or attainment. Exhaustive querying supplies a correct finite-cost algorithm. No normalization, range bound, monotonicity or unique minimizer is assumed.
--
--   **Formalization Note** The input ground set is `Fin n`. The model also permits unsuccessful nonreturning runs and charges them as failures. Consequently its infimum includes the ordinary almost surely halting algorithms of Definition 1.1; a lower bound in this enlarged model implies the paper's lower bound.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Definition 1.1 and Theorem 1.2 setting, printed p. 2 / PDF p. 3

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SFMQueryLower_EmptyMin_RandomizedOracle

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- No normalization, sign, monotonicity, range or uniqueness promise is present. -/
def EmptyMinimizes {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S, f ∅ ≤ f S

abbrev EmptyMinAlgorithm (n : ℕ) := RandomizedOracle (Finset (Fin n)) ℝ Bool

/-- Failure includes not returning an answer. In particular all almost surely halting
algorithms of the paper are included, without imposing finite expectation. -/
noncomputable def errorOn {n : ℕ} (A : EmptyMinAlgorithm n)
    (f : Finset (Fin n) → ℝ) : ℝ≥0∞ :=
  A.law {ω | ¬ ∃ b : Bool, Returns (A.choose ω) f b ∧ (b = true ↔ EmptyMinimizes f)}

def CorrectOn {n : ℕ} (A : EmptyMinAlgorithm n) (δ : ℝ≥0∞)
    (f : Finset (Fin n) → ℝ) : Prop := errorOn A f ≤ δ

def SolvesEmptyMin {n : ℕ} (A : EmptyMinAlgorithm n) (δ : ℝ≥0∞) : Prop :=
  ∀ f : Finset (Fin n) → ℝ, NonmonotoneSubmod.Shared.Submodular f → CorrectOn A δ f

noncomputable def expectedQueries {n : ℕ} (A : EmptyMinAlgorithm n)
    (f : Finset (Fin n) → ℝ) : ℝ≥0∞ := expectedCount A f (fun _ => True)

noncomputable def worstExpectedQueries {n : ℕ} (A : EmptyMinAlgorithm n) : ℝ≥0∞ :=
  ⨆ f : {f : Finset (Fin n) → ℝ // NonmonotoneSubmod.Shared.Submodular f},
    expectedQueries A f.val

/-- Definition 1.1: infimum of worst-case expected costs of correct algorithms.
The source uses this definition for `δ < 1/2`, including `δ = 0` and `δ = 1/3`.
The set formulation allows arbitrary seed spaces, without an infimum-attainment assumption. -/
noncomputable def randomizedComplexity (n : ℕ) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {q | ∃ A : EmptyMinAlgorithm n, SolvesEmptyMin A δ ∧ q = worstExpectedQueries A}

end SFMQueryLower.EmptyMin


