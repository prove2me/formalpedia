-- Prove2me | Definitions.Def_OrderedSearchExact_Exact_Greedy
-- name    : OrderedSearchExact_Exact_Greedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:51.72321+00:00
-- url     : https://prove2.me/theorems/72c845b1-90d8-43b9-920e-2659b692ccb1
-- title:
--   Extended-rate greedy recurrence and exact query budget
-- statement:
--   For fixed $n$ and a single density $h$, the greedy maps are
--
--   $$\Gamma_S(\alpha)=\sup\{\beta\in[\alpha,\infty):q_{S_{\beta e^Y}+A_{\alpha e^Y}}\ge0\},\quad \Gamma_A(\alpha)=\sup\{\beta\in[\alpha,\infty):q_{S_{\alpha e^Y}+A_{\beta e^Y}}\ge0\}.$$
--
--   Candidate centers are finite, while the supremum is taken in $[0,\infty]$. At an infinite center the next map is infinity, completing the other parity update. Starting at $\alpha_0=0$, odd steps use $\Gamma_S$ and even steps use $\Gamma_A$. The corresponding hybrid uses the new center in the allowed component and the preceding center in the other. Once both centers are infinite the coefficient vector remains zero.
--
--   The integer budget is $1+\lceil(2W+\ln M)/\ln3\rceil+\lceil\ln(Dn/M)/d\rceil+3$. Neither attainment of the suprema nor positivity of the resulting path is assumed by these operational definitions.
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), (16)–(19), (43), p.14–15, 23 (PDF p.14–15, 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Analysis

open Classical

namespace OrderedSearchExact.Exact

/-- Suprema are in the complete lattice [0,∞]. Feasibility/attainment is a theorem,
not part of this definition. The ∞ branch performs the remaining parity update. -/
noncomputable def gammaS (n : ℕ) (h : ℝ → ℝ) (α : Rate) : Rate :=
  if α = ⊤ then ⊤ else sSup {β | α ≤ β ∧ β ≠ ⊤ ∧ Nonnegative (hybrid n h β α)}

noncomputable def gammaA (n : ℕ) (h : ℝ → ℝ) (α : Rate) : Rate :=
  if α = ⊤ then ⊤ else sSup {β | α ≤ β ∧ β ≠ ⊤ ∧ Nonnegative (hybrid n h α β)}

noncomputable def greedyRate (n : ℕ) (h : ℝ → ℝ) : ℕ → Rate
  | 0 => 0
  | t + 1 => if Odd (t + 1) then gammaS n h (greedyRate n h t)
              else gammaA n h (greedyRate n h t)

noncomputable def greedyPath (n : ℕ) (h : ℝ → ℝ) : ℕ → Coeff n
  | 0 => fejer n
  | t + 1 => if Odd (t + 1) then hybrid n h (greedyRate n h (t + 1)) (greedyRate n h t)
              else hybrid n h (greedyRate n h t) (greedyRate n h (t + 1))

/-- Equation (43), with both ceilings and all four additive queries. -/
noncomputable def queryBudget (n : ℕ) (W d M D : ℝ) : ℕ :=
  1 + ⌈(2 * W + Real.log M) / Real.log 3⌉₊ + ⌈Real.log (D * n / M) / d⌉₊ + 3

end OrderedSearchExact.Exact


