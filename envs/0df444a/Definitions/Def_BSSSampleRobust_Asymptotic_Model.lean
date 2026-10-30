-- Prove2me | Definitions.Def_BSSSampleRobust_Asymptotic_Model
-- name    : BSSSampleRobust_Asymptotic_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:26:54.134203+00:00
-- url     : https://prove2.me/theorems/2f872bca-02c4-46f4-9aa2-faea528ab622
-- title:
--   Multistage stochastic linear model and its stochastic value
-- statement:
--   The general linear model builds on the separate history-policy object. It contains an arbitrary finite number of inequalities, and for every stage affine functions of the entire trajectory giving the cost vector and constraint matrix, together with an affine right-hand side. The total cost sums scalar products of the stage costs with the history-dependent decisions. Feasibility is the componentwise comparison of the sum of matrix-vector products with the right-hand side. Feasibility on a set is pointwise; the stochastic program imposes it almost surely. Its value is the infimum of the extended expectation over all such feasible policies. Empty feasible sets have value $+\infty$ and unbounded-below problems have value $-\infty$. There is no hypothesis of an optimizer or of finiteness.
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; §2, problem (1), PDF/printed 6–7

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Policy
import Definitions.Def_BSSSampleRobust_Asymptotic_Transport

open MeasureTheory
noncomputable section

open scoped ENNReal Classical

namespace BSSSampleRobust.Asymptotic

/-- Multistage stochastic linear data: coefficients may depend on the whole path. -/
structure LinearModel (p : ℝ≥0∞) [Fact (1 ≤ p)] (D : Layout) where
  m : ℕ
  cost : (t : Fin D.T) → Path p D →ᵃ[ℝ] (Fin (D.n t) → ℝ)
  matrix : (t : Fin D.T) → Path p D →ᵃ[ℝ] Matrix (Fin m) (Fin (D.n t)) ℝ
  rhs : Path p D →ᵃ[ℝ] (Fin m → ℝ)

def totalCost {p : ℝ≥0∞} [Fact (1 ≤ p)] {D : Layout}
    (M : LinearModel p D) (x : Policy p D) (z : Path p D) : ℝ :=
  ∑ t, ∑ i, M.cost t z i * x.act t (historyOf t z) i

def feasibleAt {p : ℝ≥0∞} [Fact (1 ≤ p)] {D : Layout}
    (M : LinearModel p D) (x : Policy p D) (z : Path p D) : Prop :=
  ∀ k : Fin M.m, (∑ t, ∑ i, M.matrix t z k i * x.act t (historyOf t z) i) ≤ M.rhs z k

def feasibleOn {p : ℝ≥0∞} [Fact (1 ≤ p)] {D : Layout}
    (M : LinearModel p D) (x : Policy p D) (Z : Set (Path p D)) : Prop :=
  ∀ z ∈ Z, feasibleAt M x z

def stochasticValue {p : ℝ≥0∞} [Fact (1 ≤ p)] {D : Layout}
    (M : LinearModel p D) (P : Measure (Path p D)) : EReal :=
  ⨅ (x : Policy p D) (_ : ∀ᵐ z ∂P, feasibleAt M x z),
    expectation P (fun z => (totalCost M x z : EReal))

end BSSSampleRobust.Asymptotic


