-- Prove2me | Definitions.Def_LostSalesRQ_poisson_functions
-- name    : LostSalesRQ_poisson_functions
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-17T18:22:22.410359+00:00
-- url     : https://prove2.me/theorems/c958cbe1-249b-4eac-a1a6-9deae76c442f
-- title:
--   Poisson, Erlang and base-stock cost functions
-- statement:
--   Deterministic functions of a lead-time demand mean $\mu\ge0$ used throughout the paper.
--
--   1. Poisson mass $p_j(t)=e^{-t}t^j/j!$, distribution function $F_j(t)=\sum_{i=0}^{j}p_i(t)$, upper tail $\mathbb P(N(t)\ge l)=1-\sum_{i<l}p_i(t)$ and expected shortfall $G_l(t)=\mathbb E(l-N(t))^+=\sum_{i=0}^{l}(l-i)p_i(t)$, where $N(t)$ is Poisson with mean $t$.
--   2. For base stock $j$: the loss fraction $e_j=p_j(\mu)/F_j(\mu)$, the Erlang normalizer $A_j=F_j(\mu)/p_j(\mu)$, the mean on-hand inventory $H_j=j-\mu+\mu e_j$, and the variance $v_j$ of the on-hand inventory $I_j$, whose law is $\mathbb P(I_j=l)=p_{j-l}(\mu)/F_j(\mu)$ for $0\le l\le j$.
--   3. The zero-setup normalized cost of base stock $j$ and its minimum over integer levels,
--   $$L_j(a)=H_j+a\,e_j,\qquad U_\mu(a)=\min_{j\ge0}L_j(a).$$
--   4. The intersection penalty $a_j=(e_j-e_{j+1})^{-1}-\mu$ of the cost lines of base stocks $j$ and $j+1$.
--   5. The integer lot $Q_k=\max\{1,\lfloor\sqrt{2k}\rfloor\}$ and the batching surcharge $b_k=(Q_k-1)/2+k/Q_k$.
--
--   These are the closed-form quantities that the selection algorithm computes and that the analytic comparisons manipulate.
--
--   **Formalization Note** $U_\mu(a)$ is the real infimum over all $j\in\mathbb N$; the family is bounded below, so it is the true infimum (attained, by the paper's argument). Divisions are Lean's total divisions; for $\mu\ge0$ every $F_j(\mu)$ is positive.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 3.4 (p. 8), Appendix A (pp. A1-A2), eq. (15) (p. 16), Section 4.6.1 (p. 21).

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Poisson, Erlang and base-stock functions

Deterministic functions of the lead-time demand mean `μ` used in
M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales
Inventory Systems" (Section 3.4, Appendix A, Section 4.6).
-/

namespace LostSalesRQ

open Finset

/-- Poisson probability mass `p_j(t) = e^{-t} t^j / j!`. -/
noncomputable def poisMass (t : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-t) * t ^ j / (Nat.factorial j : ℝ)

/-- Poisson distribution function `F_j(t) = ∑_{i=0}^{j} p_i(t)`. -/
noncomputable def poisCdf (t : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j + 1), poisMass t i

/-- Poisson upper tail `P(N(t) ≥ l) = 1 - ∑_{i<l} p_i(t)` (equal to `1` when `l = 0`). -/
noncomputable def poisTail (t : ℝ) (l : ℕ) : ℝ :=
  1 - ∑ i ∈ range l, poisMass t i

/-- Expected shortfall `G_l(t) = E (l - N(t))^+ = ∑_{i=0}^{l} (l - i) p_i(t)`. -/
noncomputable def expectedShortfall (t : ℝ) (l : ℕ) : ℝ :=
  ∑ i ∈ range (l + 1), ((l : ℝ) - (i : ℝ)) * poisMass t i

/-- Loss fraction `e_j = p_j / F_j` of base stock `j` (Erlang loss probability) at lead-time
demand mean `μ`. -/
noncomputable def lossFraction (μ : ℝ) (j : ℕ) : ℝ :=
  poisMass μ j / poisCdf μ j

/-- Erlang normalizer `A_j = F_j / p_j` (the reciprocal of `e_j`). -/
noncomputable def erlangNormalizer (μ : ℝ) (j : ℕ) : ℝ :=
  poisCdf μ j / poisMass μ j

/-- Mean on-hand inventory of base stock `j`: `H_j = j - μ + μ e_j`. -/
noncomputable def meanOnHand (μ : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) - μ + μ * lossFraction μ j

/-- Variance `v_j = Var(I_j)` of the stationary on-hand inventory `I_j` of base stock `j`,
where `P(I_j = l) = p_{j-l}(μ) / F_j(μ)` for `0 ≤ l ≤ j`. -/
noncomputable def onHandVariance (μ : ℝ) (j : ℕ) : ℝ :=
  ∑ l ∈ range (j + 1), ((l : ℝ) - meanOnHand μ j) ^ 2 * (poisMass μ (j - l) / poisCdf μ j)

/-- Normalized zero-setup cost of base stock `j`: `L_j(a) = H_j + a e_j`. -/
noncomputable def baseStockCost (μ a : ℝ) (j : ℕ) : ℝ :=
  meanOnHand μ j + a * lossFraction μ j

/-- Minimum base-stock cost `U_μ(a) = min_{j ≥ 0} L_j(a)` (infimum over all integer levels). -/
noncomputable def minBaseStockCost (μ a : ℝ) : ℝ :=
  ⨅ j : ℕ, baseStockCost μ a j

/-- Intersection penalty `a_j = (e_j - e_{j+1})^{-1} - μ` of the cost lines of base stocks
`j` and `j + 1`. -/
noncomputable def intersectionPenalty (μ : ℝ) (j : ℕ) : ℝ :=
  (lossFraction μ j - lossFraction μ (j + 1))⁻¹ - μ

/-- Integer lot size `Q_k = max{1, ⌊√(2k)⌋}`. -/
noncomputable def lotSize (k : ℝ) : ℕ :=
  max 1 ⌊Real.sqrt (2 * k)⌋₊

/-- Batching surcharge `b_k = (Q_k - 1)/2 + k / Q_k`. -/
noncomputable def batchSurcharge (k : ℝ) : ℝ :=
  ((lotSize k : ℝ) - 1) / 2 + k / (lotSize k : ℝ)

end LostSalesRQ


