-- Prove2me | Definitions.Def_AvgCostLP_IsDualFeasible
-- name    : AvgCostLP_IsDualFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:19.814703+00:00
-- url     : https://prove2.me/theorems/6c031db4-c3a3-499a-9154-712be03a9e83
-- title:
--   (3.9), (3.11) — the dual program (P*) over $\mathbb R\times F_b(\mathbb X)$
-- statement:
--   The **dual program** (P*) maximizes $\rho$ over $\rho\in\mathbb R$ and $h\in\mathbb F_b(\mathbb X)$, the bounded Borel measurable real functions on $\mathbb X$, subject to
--   $$\rho+h(x)-\int_{\mathbb X}h(y)\,q(dy\mid x,a)\le c(x,a)\qquad\forall(x,a)\in\Gamma. \tag{3.9}$$
--   `dualValues` is the set of feasible $\rho$; its supremum is $\sup(\mathrm P^*)$, and (P*) is **consistent** when it is nonempty.
--
--   The dual variables are bounded on purpose (Remark 3.3): with this choice (P*) need not be solvable.
--
--   **Formalization Note** $c$ is finite on $\Gamma$, so the constraint compares real numbers.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §3.1, (3.9) and (3.11), p.11

import Mathlib
import Definitions.Def_AvgCostLP_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AvgCostLP

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- Yu, arXiv:1905.12095v3, §3.1, p.10: `h ∈ F_b(X)`, i.e. `h` is a bounded Borel measurable
real-valued function on `X`. -/
def IsBoundedBorel (h : X → ℝ) : Prop :=
  Measurable h ∧ ∃ C : ℝ, ∀ x, |h x| ≤ C

/-- Yu, arXiv:1905.12095v3, (3.9) and (3.11), p.11: `(ρ, h) ∈ ℝ × F_b(X)` is a feasible
solution of the dual program (P*), i.e. `h` is bounded Borel and
`ρ + h(x) − ∫_X h(y) q(dy | x, a) ≤ c(x, a)` for all `(x, a) ∈ Γ`.

**Formalization Note** `c` is finite on `Γ`, so `(c p).toReal` is its exact value there. The
integral is a Bochner integral of a bounded measurable function against a probability measure. -/
def IsDualFeasible (M : Model X A) (ρ : ℝ) (h : X → ℝ) : Prop :=
  IsBoundedBorel h ∧ ∀ p ∈ M.graph, ρ + h p.1 - ∫ y, h y ∂(M.q p) ≤ (M.c p).toReal

/-- Yu, arXiv:1905.12095v3, (3.11), p.11: the set of objective values `ρ` of the feasible
solutions of (P*). Its supremum is `sup(P*)`; (P*) is *consistent* when it is nonempty. -/
def dualValues (M : Model X A) : Set ℝ :=
  {ρ | ∃ h : X → ℝ, IsDualFeasible M ρ h}

end AvgCostLP


