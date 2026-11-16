-- Prove2me | Definitions.Def_SwitchingStable_Universal_Supplement_Costs
-- name    : SwitchingStable_Universal_Supplement_Costs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:35:07.832416+00:00
-- url     : https://prove2.me/theorems/0755d3d6-8148-4944-94ee-8528a5bab022
-- title:
--   Capped geometric costs and the complete private-witness series
-- statement:
--   For $0<x\le1$, let $G_x,G'_x$ be independent geometric variables on the positive integers, with probability $x(1-x)^{t-1}$ at $t$. For positive caps $a,b$, set $Z_{a,b}=\min(G_x,a)+\min(G'_x,b)-1$. Its expected logarithm is represented by the finite sum over the two capped distributions. The terminal mass at $a$ is $(1-x)^{a-1}$; all masses before $a$ are $x(1-x)^{t-1}$. Thus the finite representation includes the limit at $x=0$.
--
--   $$f_{d,q}=\int_0^1\mathbb E\log Z_{q+1,d-q}(x)\,dx,\qquad c_d=\max_{0\le q<d}f_{d,q}\quad(d\ge1).$$
--
--   The finite maximum is taken from this experiment, not defined by the formulas to be proved in Lemma 20. The helpers `oddFormula` and `evenFormula` are the two displayed finite sums in that lemma; their equality to $c_d$ is a theorem.
--
--   For an integer $r\ge1$, define
--
--   $$C_r=\sum_{k=2}^{\infty}k\log k\left[\frac1{r(k-1)+1}-\frac2{rk+1}+\frac1{r(k+1)+1}\right].$$
--
--   The geometric logarithm helper sums $k\log k\,y^2(1-y)^{k-1}$ over all $k\ge2$, and the private integrand substitutes $y=1-(1-x)^r$. These functions give the exact constants used in Theorem 3, with no truncation or rounded replacement. Convergence, integrability, $C_1=C$, and $C_2$ equal to the published constant are conclusions there.
--
--   **Formalization Note** All arithmetic in series coefficients and logarithms is real. Natural indices start at $k=2$ via a shift; inclusive finite sums with reversed bounds are empty. The private integrand is assigned the null value zero at $x=0$, where the unbounded geometric expectation has no finite limit; this changes no integral. On invalid zero domain sizes, $c_0$ is defined as zero, and no theorem uses it for a genuine coordinate.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), pp. 36–37, PDF pp. 37–38, Appendix H, capped geometric variables, Lemma 20 formulas and private constants

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Constants
import Definitions.Def_SwitchingStable_Universal_Reveal

namespace SwitchingStable.Universal.Supplement

open MeasureTheory

/-- Distribution of min(G_x,a), including its limiting value at x=0. -/
noncomputable def cappedMass (a t : ℕ) (x : ℝ) : ℝ :=
  if t = a then (1 - x) ^ (a - 1)
  else if 1 ≤ t ∧ t < a then x * (1 - x) ^ (t - 1) else 0

noncomputable def cappedLog (a b : ℕ) (x : ℝ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 a, ∑ t ∈ Finset.Icc 1 b,
    cappedMass a s x * cappedMass b t x * Real.log ((s : ℝ) + t - 1)

noncomputable def f (d q : ℕ) : ℝ :=
  ∫ x, cappedLog (q + 1) (d - q) x ∂unitLaw

/-- The maximum is defined from the experiment, not from Lemma 20's answer. -/
noncomputable def finiteCost (d : ℕ) : ℝ := by
  classical
  exact if h : 0 < d then
    ((Finset.range d).image (f d)).max'
      ((Finset.nonempty_range_iff.mpr (Nat.ne_of_gt h)).image (f d))
    else 0

noncomputable def oddFormula (m : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 2 (m - 1), 2 * Real.log k / ((k + 1 : ℝ) * (k + 2))) +
  (∑ k ∈ Finset.Icc m (2 * m - 2),
    4 * m * Real.log k / ((k : ℝ) * (k + 1) * (k + 2))) +
  Real.log (2 * m - 1 : ℕ) / (2 * (m : ℝ) - 1)

noncomputable def evenFormula (m : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 2 (m - 1), 2 * Real.log k / ((k + 1 : ℝ) * (k + 2))) +
  3 * Real.log m / ((m + 1 : ℝ) * (m + 2)) +
  (∑ k ∈ Finset.Icc (m + 1) (2 * m - 1),
    2 * (2 * m + 1) * Real.log k / ((k : ℝ) * (k + 1) * (k + 2))) +
  Real.log (2 * m) / (2 * (m : ℝ))

noncomputable def privateSeriesTerm (r k : ℕ) : ℝ :=
  let t : ℝ := k + 2
  t * Real.log t *
    (1 / ((r : ℝ) * (t - 1) + 1) - 2 / ((r : ℝ) * t + 1) +
      1 / ((r : ℝ) * (t + 1) + 1))

noncomputable def privateCost (r : ℕ) : ℝ := ∑' k : ℕ, privateSeriesTerm r k

noncomputable def geometricTerm (y : ℝ) (k : ℕ) : ℝ :=
  (k + 2 : ℝ) * Real.log (k + 2) * y ^ 2 * (1 - y) ^ (k + 1)

noncomputable def geometricLog (y : ℝ) : ℝ := ∑' k : ℕ, geometricTerm y k

noncomputable def privateIntegrand (r : ℕ) (x : ℝ) : ℝ :=
  geometricLog (1 - (1 - x) ^ r)

end SwitchingStable.Universal.Supplement


