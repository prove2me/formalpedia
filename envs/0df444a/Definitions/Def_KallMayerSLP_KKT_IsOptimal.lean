-- Prove2me | Definitions.Def_KallMayerSLP_KKT_IsOptimal
-- name    : KallMayerSLP_KKT_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:25.606982+00:00
-- url     : https://prove2.me/theorems/a8484352-564e-47ea-9b53-eed7b3840564
-- title:
--   $\hat x$ solves the program (3.1)
-- statement:
--   A point $\hat x\in\mathbb R^n$ **solves** the program (3.1) $\min\{f(x)\mid g_i(x)\le 0,\ i=1,\dots,m\}$ if it is feasible, $\hat x\in\mathcal B$, and
--   $$
--   f(\hat x)=\min_{x\in\mathcal B}f(x),\qquad\text{i.e.}\qquad f(\hat x)\le f(y)\quad\forall y\in\mathcal B .
--   $$
--
--   This is the global optimality used in the regularity condition RC 0, in Proposition 3.4 and in Remark 3.1.
--
--   **Formalization Note** The book's "optimal solution", "optimum of (3.1)" and "$\hat x$ solves (3.1)" all denote this predicate.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, pp.61–62 (PDF 72–73)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_feasibleSet

namespace KallMayerSLP.KKT

/-- **`x̂` solves the program (3.1).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3, pp.61–62 (PDF 72–73):
`x̂ ∈ 𝓑` with `f(x̂) = min_{x ∈ 𝓑} f(x)`, i.e. `x̂` is a global minimum of `f` over the feasible
set `𝓑` of (3.1).

**Formalization Note.** "Optimal solution", "optimum" and "`x̂` solves (3.1)" on pp.62–64 are all
this predicate: feasibility together with `f x̂ ≤ f y` for every feasible `y`. -/
def IsOptimal {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ feasibleSet g ∧ ∀ y ∈ feasibleSet g, f x ≤ f y

end KallMayerSLP.KKT


