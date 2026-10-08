-- Prove2me | Definitions.Def_SPHardness_FixedRecourse_Model
-- name    : SPHardness_FixedRecourse_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:57.351712+00:00
-- url     : https://prove2.me/theorems/019bf2b7-1f1f-4e84-8b9e-633b380b7a3b
-- title:
--   §1–§2, pp. 2–8 — problem (2), the expected recourse, knapsack volume, #Parity, budgets, Vandermonde matrix and thresholds
-- statement:
--   For a dimension $k$, let $C=[0,1]^k$ carry Lebesgue measure, of total mass one. Given weights $\alpha\in\mathbb R^k$ and a budget $\beta\in\mathbb R$, the knapsack polytope and its volume are
--   $$P(\alpha,\beta)=\{\xi\in C: \sum_j\alpha_j\xi_j\le\beta\},\qquad V(\alpha,\beta)=\operatorname{Vol}(P(\alpha,\beta)).$$
--   For a realization $\xi$, the second-stage value $Q(\xi;\alpha,\beta)$ maximizes $\sum_j\xi_j y_j-\beta z$ subject to $0\le y_j\le\alpha_j z$ and $0\le z\le1$. The expected recourse is $\mathcal Q(\alpha,\beta)=\int_C Q(\xi;\alpha,\beta)\,d\xi$.
--   For natural-number weights and budget, $D$ counts feasible binary vectors of even cardinality minus those of odd cardinality. The auxiliary definitions are budgets $\gamma_i=\beta+i/(k+1)$, the matrix $F_{ic}=\gamma_i^{k-c}$, and the exact accuracy thresholds (3) and (7).
--
--   These shared objects make each reduction statement refer to the actual linear program and counting problem.
--
--   **Formalization Note** Coordinates of $\alpha$ are indexed from zero in Lean; the paper's $\alpha_k$ is the last coordinate. The real supremum used for $Q$ represents its optimum whenever $\alpha\ge0$, since the feasible set is nonempty and bounded. The integral is over the unit cube, whose volume is one.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), pp. 2–8, problem (2), #Parity, (3), (5), (7) and (8)

import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

/-- The unit cube carrying the uniform probability law. -/
def cube (k : ℕ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

/-- The knapsack polytope of the paper. -/
def knapsack {k : ℕ} (α : Fin k → ℝ) (β : ℝ) : Set (Fin k → ℝ) :=
  {ξ | ξ ∈ cube k ∧ ∑ j, α j * ξ j ≤ β}

/-- Its Lebesgue volume. -/
def vol {k : ℕ} (α : Fin k → ℝ) (β : ℝ) : ℝ :=
  (volume (knapsack α β)).toReal

/-- The optimal value of the fixed-recourse second-stage maximization (2). -/
def secondStageValue {k : ℕ} (α : Fin k → ℝ) (β : ℝ) (ξ : Fin k → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (y : Fin k → ℝ) (z : ℝ),
    (∀ j, 0 ≤ y j) ∧ (∀ j, y j ≤ α j * z) ∧
    0 ≤ z ∧ z ≤ 1 ∧ v = (∑ j, ξ j * y j) - β * z}

/-- Expected recourse under the uniform distribution on the cube. -/
def expRecourse {k : ℕ} (α : Fin k → ℝ) (β : ℝ) : ℝ :=
  ∫ ξ in cube k, secondStageValue α β ξ

/-- The even-minus-odd #Parity count of feasible binary vectors. -/
def parityD {k : ℕ} (α : Fin k → ℕ) (β : ℕ) : ℤ :=
  ((Finset.univ.powerset.filter (fun s : Finset (Fin k) =>
    (∑ j ∈ s, α j) ≤ β ∧ Even s.card)).card : ℤ) -
  ((Finset.univ.powerset.filter (fun s : Finset (Fin k) =>
    (∑ j ∈ s, α j) ≤ β ∧ Odd s.card)).card : ℤ)

/-- The spaced budgets γ₀,...,γₖ. -/
def budget (k : ℕ) (β : ℝ) (i : Fin (k + 1)) : ℝ :=
  β + (i : ℝ) / (k + 1)

/-- The printed Vandermonde matrix, with descending powers. -/
def vandermondeF (k : ℕ) (β : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  fun i c => budget k β i ^ (k - (c : ℕ))

/-- The right-hand side of threshold (3). -/
def eps3 {k : ℕ} (α : Fin k → ℝ) : ℝ :=
  1 / (2 * (k.factorial : ℝ) * ((∑ j, |α j|) + 2) ^ k *
    ((k + 1 : ℕ) : ℝ) ^ (k + 1) * ∏ j, α j)

/-- The right-hand side of threshold (7), with αₖ supplied explicitly. -/
def delta7 {k : ℕ} (α : Fin k → ℝ) (αk : ℝ) : ℝ :=
  (αk / (2 * (k.factorial : ℝ) * (1 + αk) * ((∑ j, |α j|) + 2) ^ k *
    ((k + 1 : ℕ) : ℝ) ^ (k + 1) * ∏ j, α j)) ^ 2

/-- The paper’s final coordinate αₖ (with one-based mathematical indexing). -/
def lastWeight {k : ℕ} (hk : 0 < k) (α : Fin k → ℝ) : ℝ :=
  α ⟨k - 1, by omega⟩

end SPHardness.FixedRecourse


