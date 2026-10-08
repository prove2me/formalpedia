-- Prove2me | Definitions.Def_CachonCoord_TwoLocation_Model
-- name    : CachonCoord_TwoLocation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:43:11.031854+00:00
-- url     : https://prove2.me/theorems/06a36384-5a0f-470a-9110-2af790c73848
-- title:
--   §6.8.1–6.8.2, pp. 77–79 — the two-location base-stock model: D_r, D_s, costs c_i(s_r, s_s), I_s, B_s, π_r, π_s, Π
-- statement:
--   The two-location base-stock model of Cachon and Zipkin (1999) as presented in Cachon (2003), §6.8.
--
--   A supplier replenishes a retailer, and the retailer serves customer demand. Both firms use base stock policies with base stock levels $s_r$ (retailer) and $s_s$ (supplier); base stocks are real numbers, and a negative $s_s$ means planned supplier backorders. Let $D_r$ be demand during the retailer's lead time and $D_s$ demand during the supplier's lead time, with distribution functions $F_r$, $F_s$ and means $\mu_r$, $\mu_s$. Both are nonnegative random variables with finite means whose distribution functions are continuous, vanish at $0$, are strictly increasing on $[0,\infty)$ and differentiable on $(0,\infty)$. The cost rates are the holding costs $h_r$, $h_s$ with $0 < h_s < h_r$ and the backorder costs $\beta_r > 0$ (charged to the retailer) and $\beta_s > 0$ (charged to the supplier) for backorders at the retailer; $\beta = \beta_r + \beta_s$.
--
--   **Single-location costs (§6.7.1).** At retailer inventory level $y$, expected on-hand inventory and backorders are $I_r(y) = E[(y - D_r)^+]$ and $B_r(y) = E[(D_r - y)^+]$; the retail-level cost rates are
--   $$c_r(y) = h_r I_r(y) + \beta_r B_r(y), \qquad c_s(y) = \beta_s B_r(y), \qquad c(y) = c_r(y) + c_s(y),$$
--   and $c'(y) = (h_r + \beta)F_r(y) - \beta$ is recorded as an explicit function.
--
--   **Two-location costs (§6.8.2).** Because the supplier may stock out, the retailer's inventory level is $s_r - (D_s - s_s)^+$. For any single-location function $g$ define
--   $$g(s_r, s_s) = E\big[g(s_r - (D_s - s_s)^+)\big] = F_s(s_s)\,g(s_r) + \int_{s_s}^{\infty} g(s_r + s_s - x)f_s(x)\,dx .$$
--   This gives $I_r(s_r,s_s)$, $B_r(s_r,s_s)$, $c_r(s_r,s_s)$, $c_s(s_r,s_s)$ and $c(s_r,s_s) = c_r(s_r,s_s) + c_s(s_r,s_s)$. The supplier's average inventory is $I_s(y) = E[(y - D_s)^+] = \int_0^y F_s(x)\,dx$ and its average backorder is $B_s(y) = \mu_s - y + I_s(y)$. The firms' total average cost rates and the chain's cost are
--   $$\pi_r(s_r,s_s) = c_r(s_r,s_s), \qquad \pi_s(s_r,s_s) = h_s I_s(s_s) + c_s(s_r,s_s), \qquad \Pi = \pi_r + \pi_s .$$
--
--   These are the objects on which every result of §6.8 is stated.
--
--   **Formalization Note** The two demand laws are probability measures on $\mathbb R$ with no mass on $(-\infty,0)$. Every expectation is defined directly as a Lebesgue integral, and the page's integral forms ($F_s(s_s)g(s_r) + \int_{s_s}^\infty\cdots$ and $I_s(y) = \int_0^y F_s$) are consequences of that definition. Under the finite-mean assumptions every integrand is integrable. The positivity of $\beta_r$ and $\beta_s$ is the section's standing assumption (footnote 34 excludes $\beta_s = 0$ and $\beta_r = 0$). The single-location functions duplicate those of the companion mission on §6.7, because drafts cannot import drafts.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.1–6.8.2, pp. 77–79 (model, c_i(s_r, s_s), I_r(s_r, s_s), B_r(s_r, s_s), π_r, I_s, π_s, Π); §6.8.4, p. 82 (B_s); §6.7.1, Eqs. (28)–(30), pp. 72–73 (I_r, B_r, c_r, c_s, c)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CachonCoord.TwoLocation

/-- The two-location base-stock model of Cachon (2003), §6.8.1–6.8.2, pp. 77–79 (after Cachon
and Zipkin 1999), with the single-location objects of §6.7.1, pp. 71–73, that it is built on.

`lawR` is the law of the retailer's lead-time demand `D_r` (over the retailer's lead time `L_r`),
`lawS` the law of the supplier's lead-time demand `D_s` (over `L_s`). Both are probability laws on
nonnegative demand with finite mean whose distribution functions `F_r`, `F_s` are continuous,
vanish at `0` (`D > 0`), are strictly increasing on `[0, ∞)` and differentiable on `(0, ∞)`
("assume F_s is increasing and differentiable", p. 77, and the analogue for `F_r` in §6.7.1).
`hr`, `hs` are the holding cost rates `h_r`, `h_s` with `0 < h_s < h_r` (p. 77); `br`, `bs` are
the backorder cost rates `β_r`, `β_s` charged to the retailer and to the supplier for backorders
at the retailer, both positive (footnote 34: the cases `β_s = 0` or `β_r = 0` "are not treated
here"). -/
structure Model where
  lawR : Measure ℝ
  probR : IsProbabilityMeasure lawR
  nonnegR : lawR (Set.Iio 0) = 0
  meanR : Integrable (id : ℝ → ℝ) lawR
  cdfR_zero : cdf lawR 0 = 0
  cdfR_strict : StrictMonoOn (cdf lawR) (Set.Ici 0)
  cdfR_cont : Continuous (cdf lawR)
  cdfR_diff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (cdf lawR) y
  lawS : Measure ℝ
  probS : IsProbabilityMeasure lawS
  nonnegS : lawS (Set.Iio 0) = 0
  meanS : Integrable (id : ℝ → ℝ) lawS
  cdfS_zero : cdf lawS 0 = 0
  cdfS_strict : StrictMonoOn (cdf lawS) (Set.Ici 0)
  cdfS_cont : Continuous (cdf lawS)
  cdfS_diff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (cdf lawS) y
  hr : ℝ
  hs : ℝ
  br : ℝ
  bs : ℝ
  hs_pos : 0 < hs
  hs_lt_hr : hs < hr
  br_pos : 0 < br
  bs_pos : 0 < bs

namespace Model

variable (M : Model)

/-! ### Single-location objects (§6.7.1, pp. 72–73), at retailer inventory level `y` -/

/-- `F_r(y)`, the distribution function of the retailer's lead-time demand. -/
noncomputable def FR (y : ℝ) : ℝ := cdf M.lawR y

/-- `F_s(y)`, the distribution function of the supplier's lead-time demand. -/
noncomputable def FS (y : ℝ) : ℝ := cdf M.lawS y

/-- `μ_r = E[D_r]`. -/
noncomputable def muR : ℝ := ∫ x, x ∂M.lawR

/-- `μ_s = E[D_s]` (p. 77). -/
noncomputable def muS : ℝ := ∫ x, x ∂M.lawS

/-- `I_r(y) = E[(y − D_r)⁺]`, the retailer's expected on-hand inventory at level `y` (28). -/
noncomputable def IR (y : ℝ) : ℝ := ∫ x, max (y - x) 0 ∂M.lawR

/-- `B_r(y) = E[(D_r − y)⁺]`, the retailer's expected backorders at level `y` (29). -/
noncomputable def BR (y : ℝ) : ℝ := ∫ x, max (x - y) 0 ∂M.lawR

/-- `β = β_r + β_s`. -/
def beta : ℝ := M.br + M.bs

/-- `c_r(y) = h_r I_r(y) + β_r B_r(y)`, the retailer's retail-level cost rate (p. 73). -/
noncomputable def cR (y : ℝ) : ℝ := M.hr * M.IR y + M.br * M.BR y

/-- `c_s(y) = β_s B_r(y)`, the supplier's retail-level cost rate (p. 73). -/
noncomputable def cS (y : ℝ) : ℝ := M.bs * M.BR y

/-- `c(y) = c_r(y) + c_s(y)`, the chain's retail-level cost rate (30). -/
noncomputable def c (y : ℝ) : ℝ := M.cR y + M.cS y

/-- `c'(y) = (h_r + β) F_r(y) − β`, the derivative of `c` written out (the expression whose
equation `c'(y) = h_s` is (37) and whose root is (31)). It is a plain function here; that it
is the derivative of `c` is a theorem, not part of the definition. -/
noncomputable def cDeriv (y : ℝ) : ℝ := (M.hr + M.beta) * M.FR y - M.beta

/-! ### Two-location objects (§6.8.2, pp. 78–79) -/

/-- The retail-level average of a single-location function `g` under base stocks
`(s_r, s_s)`: the retailer's inventory level is `s_r − (D_s − s_s)⁺`, so
`g(s_r, s_s) = E[g(s_r − (D_s − s_s)⁺)] = F_s(s_s) g(s_r) + ∫_{s_s}^∞ g(s_r + s_s − x) f_s(x) dx`
(p. 78). Defined by the expectation. -/
noncomputable def atRetail (g : ℝ → ℝ) (sr ss : ℝ) : ℝ :=
  ∫ x, g (sr - max (x - ss) 0) ∂M.lawS

/-- `I_r(s_r, s_s)`, the retailer's average inventory (p. 79). -/
noncomputable def IR2 (sr ss : ℝ) : ℝ := M.atRetail M.IR sr ss

/-- `B_r(s_r, s_s)`, the retailer's average backorders (p. 79). -/
noncomputable def BR2 (sr ss : ℝ) : ℝ := M.atRetail M.BR sr ss

/-- `c_r(s_r, s_s)`, the rate at which the retailer incurs costs at the retail level (p. 78). -/
noncomputable def cR2 (sr ss : ℝ) : ℝ := M.atRetail M.cR sr ss

/-- `c_s(s_r, s_s)`, the rate at which the supplier incurs costs at the retail level (p. 78). -/
noncomputable def cS2 (sr ss : ℝ) : ℝ := M.atRetail M.cS sr ss

/-- `c(s_r, s_s) = c_r(s_r, s_s) + c_s(s_r, s_s)` (p. 78). -/
noncomputable def c2 (sr ss : ℝ) : ℝ := M.cR2 sr ss + M.cS2 sr ss

/-- `I_s(y)`, the supplier's average on-hand inventory at base stock `y`, `E[(y − D_s)⁺]`;
it equals `∫_0^y F_s(x) dx` (p. 79). -/
noncomputable def IS (y : ℝ) : ℝ := ∫ x, max (y - x) 0 ∂M.lawS

/-- `B_s(y) = μ_s − y + I_s(y)`, the supplier's average backorder (p. 82). -/
noncomputable def BS (y : ℝ) : ℝ := M.muS - y + M.IS y

/-- `π_r(s_r, s_s) = c_r(s_r, s_s)`, the retailer's total average cost rate (p. 79). -/
noncomputable def piR (sr ss : ℝ) : ℝ := M.cR2 sr ss

/-- `π_s(s_r, s_s) = h_s I_s(s_s) + c_s(s_r, s_s)`, the supplier's average cost (p. 79). -/
noncomputable def piS (sr ss : ℝ) : ℝ := M.hs * M.IS ss + M.cS2 sr ss

/-- `Π(s_r, s_s) = π_r(s_r, s_s) + π_s(s_r, s_s)`, the supply chain's total cost (p. 79). -/
noncomputable def Pi (sr ss : ℝ) : ℝ := M.piR sr ss + M.piS sr ss

end Model
end CachonCoord.TwoLocation


