-- Prove2me | Definitions.Def_InventoryControl_newsboy
-- name    : InventoryControl_newsboy
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T07:26:21.423785+00:00
-- url     : https://prove2.me/theorems/1c16aba1-53a0-4b6e-81c8-a657057c0864
-- title:
--   The newsboy model with normally distributed demand
-- statement:
--   The classical single-period stochastic inventory problem, in the notation of Axsäter,
--   *Inventory Control*, Sect. 5.13.
--
--   A quantity $S$ must be committed before a single selling period begins, while the period
--   demand $x$ is random and is assumed normally distributed with mean $m$ and standard deviation
--   $s$. Both directions of error are penalized. The **overage cost** $c_o$ is charged per unit
--   left in stock at the end of the period; the **underage cost** $c_u$ is charged per unit of
--   demand that could not be satisfied. In the situation that named the model, a newsboy buys
--   copies at 25 cents and sells them at 75 cents with no salvage value, so $c_o = 25$ and
--   $c_u = 75 - 25 = 50$.
--
--   For a realized demand $x$ the cost is $(S - x)c_o$ when $x < S$ and $(x - S)c_u$ when $x > S$,
--   which is
--
--   $$ \ell(S, x) \;=\; c_o (S-x)^{+} + c_u (x-S)^{+} , $$
--
--   the function `newsboyLoss`. The quantity to be minimized is its expectation under the demand
--   distribution,
--
--   $$ C(S) \;=\; \mathbb{E}\!\left[\ell(S, x)\right] , $$
--
--   which is `newsboyCost`. The demand law itself is `newsboyDemand m s`, the normal distribution
--   with mean $m$ and variance $s^{2}$, and `newsboyCDF m s S` is its distribution function
--   $\Phi\!\left((S-m)/s\right)$ evaluated at $S$. The file also records that `newsboyDemand m s`
--   unfolds to Mathlib's Gaussian and that it is a probability measure, so that measure-theoretic
--   typeclass search sees through the abbreviation.
--
--   One auxiliary function carries the closed-form evaluation of $C$. The **standard normal loss
--   function**
--
--   $$ G(x) \;=\; \int_{x}^{\infty} (v - x)\,\varphi(v)\,\mathrm{d}v $$
--
--   measures the expected shortfall of a standard normal variable beyond the level $x$; it is
--   tabulated in the book's Appendix 2 and recurs throughout its treatment of reorder points.
--
--   **Formalization Note** The demand law is Mathlib's `gaussianReal m (s^2).toNNReal`, which is
--   the Dirac mass at $m$ when $s = 0$; every statement below assumes $s > 0$. `newsboyCDF` is
--   Mathlib's `cdf`, that is $\Pr[x \le S]$, which for a nondegenerate normal law agrees with
--   $\Pr[x < S]$. The costs $c_o$ and $c_u$ are not constrained in the definitions; positivity is
--   a hypothesis of each theorem.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, Sect. 5.13 'The Newsboy Model', pp. 95-96 (Eq. 5.87-5.89); the standard normal loss function is Eq. (5.40) p. 77 and Appendix 2 p. 242

import Mathlib

open MeasureTheory ProbabilityTheory

namespace InventoryControl

/-- The realized cost of the newsboy model: having ordered `S` and seen period demand `x`, the
cost is `co` per unit left unsold and `cu` per unit of demand that could not be met.
Axsäter, *Inventory Control*, Eq. (5.87)-(5.88). -/
noncomputable def newsboyLoss (co cu S x : ℝ) : ℝ := co * max (S - x) 0 + cu * max (x - S) 0

/-- The period demand: normally distributed with mean `m` and standard deviation `s`.
Axsäter, *Inventory Control*, Sect. 5.13. -/
noncomputable def newsboyDemand (m s : ℝ) : Measure ℝ := gaussianReal m (Real.toNNReal (s ^ 2))

@[simp] lemma newsboyDemand_eq (m s : ℝ) :
    newsboyDemand m s = gaussianReal m (Real.toNNReal (s ^ 2)) := rfl

instance instIsProbabilityMeasureNewsboyDemand (m s : ℝ) :
    IsProbabilityMeasure (newsboyDemand m s) := by
  rw [newsboyDemand_eq]; infer_instance

/-- The expected cost of ordering `S`. Axsäter, *Inventory Control*, Eq. (5.89). -/
noncomputable def newsboyCost (co cu m s S : ℝ) : ℝ :=
  ∫ x, newsboyLoss co cu S x ∂(newsboyDemand m s)

/-- The demand distribution function, i.e. `Φ((S - m)/s)`, the left-hand side of Eq. (5.91). -/
noncomputable def newsboyCDF (m s S : ℝ) : ℝ := cdf (newsboyDemand m s) S

/-- The standard normal loss function `G(x) = ∫_x^∞ (v - x) φ(v) dv`.
Axsäter, *Inventory Control*, Eq. (5.40) and Appendix 2. -/
noncomputable def normalLoss (x : ℝ) : ℝ :=
  ∫ v in Set.Ioi x, (v - x) * gaussianPDFReal 0 1 v

end InventoryControl


