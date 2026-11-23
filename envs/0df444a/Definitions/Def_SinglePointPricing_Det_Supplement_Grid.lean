-- Prove2me | Definitions.Def_SinglePointPricing_Det_Supplement_Grid
-- name    : SinglePointPricing_Det_Supplement_Grid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:28:50.060502+00:00
-- url     : https://prove2.me/theorems/9435e1c4-d0b8-4c8a-838c-48f7f10c0fd5
-- title:
--   §5.1, p. 25 — finite grids, probability weights, price laws, and mesh size
-- statement:
--   Let $A=(a_0,\ldots,a_{n-1})$ be a finite price grid and let $p_0,\ldots,p_{n-1}$ be nonnegative weights with total mass one. The discrete price law and its class are
--   $$
--   \Psi_{A,p}=\sum_{j=0}^{n-1}p_j\delta_{a_j},\qquad
--   \mathcal P_A=\{\Psi_{A,p}\in\mathcal P:p_j\ge0,\ \sum_jp_j=1\}.
--   $$
--   The grid predicates assert strict increase and positivity on precisely these $n$ indices. For a grid $a_0,\ldots,a_N$, $\Delta(A)=\max_{0\le i<N}(a_{i+1}-a_i)$ is its mesh size.
--
--   These objects express finite price distributions independently of the paper's particular LP. They use the existing measure and mechanism interfaces. A grid with zero gaps is not used in the theorem domains; $\Delta(A)=0$ at $N=0$ is an unused total-function convention. Only the finite initial segment of each sequence is read. The printed $a_i$ inside the sum over $j$ is read as $a_j$.
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, §5.1, p. 25; Proposition F-2, p. App-40

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting

namespace SinglePointPricing.Det.Supplement

noncomputable section
open MeasureTheory

/-- A strictly increasing finite list, read on indices `0, ..., n-1`. -/
def IncreasingGrid (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i j : ℕ, i < j → j < n → a i < a j

/-- Positivity is required only on the finite list. -/
def PositiveGrid (a : ℕ → ℝ) (n : ℕ) : Prop := ∀ i < n, 0 < a i

/-- Probability weights on precisely the first `n` indices. -/
def GridWeights (p : ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ j < n, 0 ≤ p j) ∧ ∑ j ∈ Finset.range n, p j = 1

/-- §5.1, p. 25: the price law with finite support and weights `p`. -/
def gridMech (a p : ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  ∑ j ∈ Finset.range n, ENNReal.ofReal (p j) • Measure.dirac (a j)

/-- The set `P_A` of price laws on the finite grid. -/
def GridClass (a : ℕ → ℝ) (n : ℕ) : Set (Measure ℝ) :=
  {Ψ | IsMech Ψ ∧ ∃ p : ℕ → ℝ, GridWeights p n ∧ Ψ = gridMech a p n}

/-- Largest gap of the grid `a₀, ..., a_N`; `0` if `N = 0` (unused). -/
def gridGap (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup ((fun i : Fin N => a (i.val + 1) - a i.val) '' Set.univ)

end
end SinglePointPricing.Det.Supplement


