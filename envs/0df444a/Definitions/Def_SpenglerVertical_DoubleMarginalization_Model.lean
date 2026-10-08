-- Prove2me | Definitions.Def_SpenglerVertical_DoubleMarginalization_Model
-- name    : SpenglerVertical_DoubleMarginalization_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:50.252582+00:00
-- url     : https://prove2.me/theorems/1b79bec9-5361-46ce-aa1c-b9e55d107cec
-- title:
--   Sections I–III and footnote 6 — monopoly profit (p − c)D(p), profit-maximizing price at unit cost c, price elasticity, marginal revenue, straight-line demand
-- statement:
--   This file fixes the objects of Spengler's model of a chain of successive monopolies. Throughout, $D:\mathbb R\to\mathbb R$ is a demand curve: $D(p)$ is the quantity of a product bought at price $p$. Every firm in the model has a constant unit variable cost (marginal cost equal to average variable cost at all relevant outputs).
--
--   1. **Profit.** A firm with constant unit cost $c$ that sells at price $p$ earns the return above variable outlay
--   $$\pi_c(p)=(p-c)\,D(p).$$
--   2. **Profit-maximizing price.** A price $p$ is profit-maximizing at unit cost $c$ when no price does better:
--   $$\pi_c(x)\le \pi_c(p)\qquad\text{for every } x\in\mathbb R.$$
--   3. **Price elasticity of demand** at $p$, taken as a positive number for a downward-sloping curve (so that "unitarily elastic" means $e=1$):
--   $$e(p)=-\frac{p\,D'(p)}{D(p)}.$$
--   4. **Marginal revenue** at price $p$, the derivative of revenue with respect to quantity along the demand curve:
--   $$r(p)=p+\frac{D(p)}{D'(p)}.$$
--   5. **Straight-line demand** with price intercept $a$ and slope $b$: $D(p)=b\,(a-p)$.
--
--   These are the notions the paper uses in Sections II–III (marginal revenue meeting a horizontal marginal-cost line, the resulting price on the demand curve) and in footnote 6 (the elasticity $e$, the marginal revenue $r$, the straight-line demand curve).
--
--   **Formalization Note** Prices range over all of $\mathbb R$, so a maximizer is an interior point. The elasticity and marginal revenue use Mathlib's `deriv`, which returns $0$ where $D$ is not differentiable, and real division, which returns $0$ on a zero denominator; every theorem that mentions them carries differentiability of $D$ and positivity of $D(p)$ as hypotheses.
-- source:
--   Spengler, Vertical integration and antitrust policy, J. Polit. Econ. 58 (1950), pp. 347–350, Sections I–III and footnote 3; p. 350, footnote 6; https://doi.org/10.1086/256964

import Mathlib

namespace SpenglerVertical.DoubleMarginalization

/-- Return above variable outlay ("profit") of a firm with constant unit variable cost `c` that sells
at price `p` against the demand curve `D` (quantity bought at price `p`): `(p - c) * D p`. -/
noncomputable def profit (D : ℝ → ℝ) (c p : ℝ) : ℝ := (p - c) * D p

/-- `p` is a profit-maximizing price for a firm with constant unit cost `c` facing demand `D`:
no price `x : ℝ` yields a larger profit. -/
def IsProfitMax (D : ℝ → ℝ) (c p : ℝ) : Prop := ∀ x : ℝ, profit D c x ≤ profit D c p

/-- Price elasticity of demand at price `p`, as a positive number for a downward-sloping demand
curve: `e = -(p * D'(p)) / D(p)`. Meaningful only where `D` is differentiable at `p` and
`D p ≠ 0` (otherwise `deriv` and division return the junk value `0`). -/
noncomputable def elasticity (D : ℝ → ℝ) (p : ℝ) : ℝ := -(p * deriv D p) / D p

/-- Marginal revenue at price `p`, i.e. the derivative of revenue with respect to quantity along the
demand curve: `r = p + D(p) / D'(p)`. Meaningful only where `D` is differentiable at `p` with
`D'(p) ≠ 0`. -/
noncomputable def marginalRevenue (D : ℝ → ℝ) (p : ℝ) : ℝ := p + D p / deriv D p

/-- The straight-line demand curve `D(p) = b * (a - p)`: quantity `b * (a - p)` is bought at
price `p`; `a` is the price-axis intercept and `b` the (absolute) slope of quantity in price. -/
def linearDemand (a b : ℝ) : ℝ → ℝ := fun p => b * (a - p)

end SpenglerVertical.DoubleMarginalization


