-- Prove2me | Definitions.Def_VerticalOwnership_CompleteInfo_Setting
-- name    : VerticalOwnership_CompleteInfo_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:50.56973+00:00
-- url     : https://prove2.me/theorems/ece55efe-59f7-42d0-a365-a650a8e7ec59
-- title:
--   §3–§4 — the PVO capacity model: demand μ_i + ε, profits (2)–(3), accounting payoff (4), fractiles (10)–(11), K^CI (5), q^CI (7), the (9) expression and G(β)
-- statement:
--   A single retailer sources a component from a supplier. Before the season the supplier builds a capacity $K$ at unit cost $c$; after demand is realized, the retailer orders from the supplier at the wholesale price $w$ and sells at the retail price $r$, with $r > w > c$. Unmet demand is lost and unsold units have no salvage value.
--
--   **Demand.** In market state $i \in \{L, H\}$ demand is $D_i = \mu_i + \varepsilon$ with $0 < \mu_L < \mu_H$, where $\varepsilon$ is a zero-mean continuous random variable with law $P$, cumulative distribution function $F$ and a density, supported on $(\underline{\varepsilon}, \bar\varepsilon)$ with $\underline{\varepsilon} < 0$ and $\mu_L + \underline{\varepsilon} \ge 0$. The quantile function is
--   $$F^{-1}(z) = \inf\{x : F(x) \ge z\}.$$
--
--   **Fractiles.** The supplier's critical fractile is $z_s = 1 - c/w$, the retailer's (without financial holdings) is $z_r = 1 - w/r$, the chain's is $z_{sc} = 1 - c/r$, and for an ownership share $\beta$
--   $$z_r(\beta) = 1 - (1 - z_r)(1 - \beta z_s).$$
--
--   **Payoffs.** Given an advance order $q^{adv}$ and a capacity $K$, the retailer orders $\min(K, \max(q^{adv}, D))$. The expected profits are the expectations
--   $$\pi_s(K \mid \mu_i, q^{adv}) = \mathbb E\big[w\min(K, \max(\mu_i + \varepsilon, q^{adv})) - cK\big],$$
--   $$\pi_r(q^{adv}, K \mid \mu_i) = \mathbb E\big[(r - w)\min(\mu_i + \varepsilon, K) - w\max(q^{adv} - \mu_i - \varepsilon, 0)\big],$$
--   and the retailer, who holds a share $\beta \in [0,1]$ of the supplier, maximizes the accounting payoff
--   $$v_r(q^{adv}, K \mid \mu_i) = \pi_r(q^{adv}, K \mid \mu_i) + \beta\,\pi_s(K \mid \mu_i, q^{adv}).$$
--
--   **Complete-information objects.** The capacity of (5) is $K_i^{CI}(q^{adv}) = \mu_i + F^{-1}(z_s)$ if $q^{adv} \le \mu_i + F^{-1}(z_s)$ and $q^{adv}$ otherwise. For a candidate optimal advance order $q^*$, the order of (7) is $q^{CI} = 0$ if $v_r(0, \mu_i + F^{-1}(z_s) \mid \mu_i) > v_r(q^*, q^* \mid \mu_i)$ and $q^*$ otherwise. The expression inside the braces of (9) is
--   $$G_9(\beta) = z_r(\beta)\big(F^{-1}(z_r(\beta)) - F^{-1}(z_s)\big) + \big(z_r + \beta(1 - z_r)\big)\int_{\underline{\varepsilon}}^{F^{-1}(z_s)} F(x)\,dx - \int_{\underline{\varepsilon}}^{F^{-1}(z_r(\beta))} F(x)\,dx,$$
--   and the retailer's accounting payoff gain (Appendix E, p. 43) is
--   $$G(\beta) = \frac1r\Big(v_r(q^*, q^* \mid \mu_i) - v_r\big(0, \mu_i + F^{-1}(z_s) \mid \mu_i\big)\Big).$$
--
--   These are the objects of Theorem 1 and of the steps of its proof.
--
--   **Formalization Note** The primitives $c, w, r, \mu_L, \mu_H, P, \underline\varepsilon$ form a structure `Model`; $\beta$ and the mean $\mu$ are explicit arguments, in the order `πs μ q K`, `πr μ q K`, `vr β μ q K`. The standing assumptions are the structure `Model.Standing`: $P$ is a probability measure; $\varepsilon$ is integrable with mean $0$; $P$ is absolutely continuous; $\underline\varepsilon < 0$ and $F(\underline\varepsilon) = 0$; $0 < \mu_L < \mu_H$ and $\mu_L + \underline\varepsilon \ge 0$; $c < w < r$. Three are disclosed additions the paper uses without stating: $c > 0$, integrability of $\varepsilon$, and strict increase of $F$ on the support $\{x \ge \underline\varepsilon : F(x) < 1\}$, so that $F^{-1}$ is a genuine inverse on $(0,1)$. The profits are Bochner integrals of the realized profits, not their closed forms; $G$ and $q^{CI}$ take the candidate $q^*$ as an argument; integrals of $F$ are oriented interval integrals.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), pp. 5–10 and 43, (1)–(5), (7), (9)–(11), Appendix E Proof of Theorem 1

import Mathlib

namespace VerticalOwnership.CompleteInfo

open MeasureTheory ProbabilityTheory

/-- The primitives of the partial-vertical-ownership capacity model (§3, pp. 5–6):
capacity cost `c`, wholesale price `w`, retail price `r`, the two mean demands `μL < μH`,
the law `P` of the zero-mean demand shock `ε`, and the lower end `εlo` (ε̲) of its support.
Demand in market state `i ∈ {L, H}` is `D_i = μ_i + ε` (1). -/
structure Model where
  /-- marginal cost of capacity -/
  c : ℝ
  /-- wholesale price -/
  w : ℝ
  /-- retail price -/
  r : ℝ
  /-- mean demand in the low market state -/
  μL : ℝ
  /-- mean demand in the high market state -/
  μH : ℝ
  /-- the law of the demand shock `ε` -/
  P : Measure ℝ
  /-- the lower end ε̲ of the support of `ε` -/
  εlo : ℝ

namespace Model

variable (M : Model)

/-- The standing assumptions of §3 (pp. 5–6), with the disclosed additions `0 < c`,
integrability of `ε`, and strict increase of the CDF `F` on the support `{x ≥ ε̲ : F x < 1}`. -/
structure Standing : Prop where
  /-- `P` is a probability measure -/
  prob : IsProbabilityMeasure M.P
  /-- `ε` is integrable (presupposed by "zero-mean") -/
  integrable : Integrable id M.P
  /-- `ε` has zero mean -/
  mean_zero : ∫ x, x ∂M.P = 0
  /-- `ε` has a probability density -/
  density : M.P ≪ volume
  /-- `ε̲ < 0` -/
  εlo_neg : M.εlo < 0
  /-- `ε̲` is the lower end of the support: `F(ε̲) = 0` -/
  cdf_εlo : cdf M.P M.εlo = 0
  /-- `F` is strictly increasing on the support `{x ≥ ε̲ : F x < 1}` -/
  strictMono_support : ∀ x y : ℝ, M.εlo ≤ x → x < y → cdf M.P x < 1 → cdf M.P x < cdf M.P y
  /-- `0 < μ_L` -/
  μL_pos : 0 < M.μL
  /-- `μ_L < μ_H` -/
  μL_lt_μH : M.μL < M.μH
  /-- demand is nonnegative: `μ_L + ε̲ ≥ 0` -/
  demand_nonneg : 0 ≤ M.μL + M.εlo
  /-- capacity is costly: `0 < c` -/
  c_pos : 0 < M.c
  /-- `c < w` -/
  c_lt_w : M.c < M.w
  /-- `w < r` -/
  w_lt_r : M.w < M.r

/-- The quantile function `F⁻¹(z) = inf {x | z ≤ F x}` of the shock `ε`. It is only applied to
levels `z ∈ (0, 1)`. -/
noncomputable def Finv (z : ℝ) : ℝ := sInf {x : ℝ | z ≤ cdf M.P x}

/-- The supplier's critical fractile `z_s = 1 − c/w` (p. 8). -/
noncomputable def zs : ℝ := 1 - M.c / M.w

/-- The retailer's critical fractile without financial holdings `z_r = 1 − w/r` (11). -/
noncomputable def zr : ℝ := 1 - M.w / M.r

/-- The retailer's effective critical fractile `z_r(β) = 1 − (1 − z_r)(1 − β z_s)` (10). -/
noncomputable def zrβ (β : ℝ) : ℝ := 1 - (1 - M.zr) * (1 - β * M.zs)

/-- The supply chain's critical fractile `z_sc = 1 − c/r` (p. 8). -/
noncomputable def zsc : ℝ := 1 - M.c / M.r

/-- The supplier's expected profit `π_s(K | μ, q^adv) = E[w min(K, max(μ + ε, q^adv)) − cK]` (2). -/
noncomputable def πs (μ q K : ℝ) : ℝ :=
  ∫ ε, (M.w * min K (max (μ + ε) q) - M.c * K) ∂M.P

/-- The retailer's expected operational profit
`π_r(q^adv, K | μ) = E[(r − w) min(μ + ε, K) − w max(q^adv − μ − ε, 0)]` (3). -/
noncomputable def πr (μ q K : ℝ) : ℝ :=
  ∫ ε, ((M.r - M.w) * min (μ + ε) K - M.w * max (q - μ - ε) 0) ∂M.P

/-- The retailer's accounting payoff `v_r(q^adv, K | μ) = π_r(q^adv, K | μ) + β π_s(K | μ, q^adv)` (4). -/
noncomputable def vr (β μ q K : ℝ) : ℝ := M.πr μ q K + β * M.πs μ q K

/-- The capacity `K^CI(q^adv)` of (5): `μ + F⁻¹(z_s)` if `q^adv ≤ μ + F⁻¹(z_s)`, else `q^adv`. -/
noncomputable def KCI (μ q : ℝ) : ℝ := if q ≤ μ + M.Finv M.zs then μ + M.Finv M.zs else q

/-- The advance order `q^CI` of (7), for a given candidate `q* = qs`: `0` if
`v_r(0, μ + F⁻¹(z_s) | μ) > v_r(q*, q* | μ)`, else `q*`. -/
noncomputable def qCI (β μ qs : ℝ) : ℝ :=
  if M.vr β μ 0 (μ + M.Finv M.zs) > M.vr β μ qs qs then 0 else qs

/-- The expression inside the braces of (9):
`z_r(β)(F⁻¹(z_r(β)) − F⁻¹(z_s)) + (z_r + β(1 − z_r)) ∫_ε̲^{F⁻¹(z_s)} F − ∫_ε̲^{F⁻¹(z_r(β))} F`. -/
noncomputable def G9 (β : ℝ) : ℝ :=
  M.zrβ β * (M.Finv (M.zrβ β) - M.Finv M.zs)
    + (M.zr + β * (1 - M.zr)) * (∫ x in M.εlo..M.Finv M.zs, cdf M.P x)
    - (∫ x in M.εlo..M.Finv (M.zrβ β), cdf M.P x)

/-- The retailer's accounting payoff gain (Appendix E, Proof of Theorem 1, p. 43)
`G(β) = (1/r)(v_r(q*, q* | μ) − v_r(0, μ + F⁻¹(z_s) | μ))`, for a given advance order `q* = qs`. -/
noncomputable def G (β μ qs : ℝ) : ℝ :=
  (1 / M.r) * (M.vr β μ qs qs - M.vr β μ 0 (μ + M.Finv M.zs))

end Model

end VerticalOwnership.CompleteInfo


