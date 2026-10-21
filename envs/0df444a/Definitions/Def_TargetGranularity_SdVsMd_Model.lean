-- Prove2me | Definitions.Def_TargetGranularity_SdVsMd_Model
-- name    : TargetGranularity_SdVsMd_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:53.171659+00:00
-- url     : https://prove2.me/theorems/4d56155f-2d60-4af8-ad3d-ebfb28485b65
-- title:
--   §2–§3, pp. 9–18 — targeted advertising with consumer inference: posterior expected surplus, click sets, ad values, sd and md equilibria, class S (6), c^max_click (7), c̄_ad
-- statement:
--   This file sets up the targeted-advertising model of Despotakis and Yu in its single-dimensional (sd) and multidimensional (md) environments.
--
--   **Consumers.** A consumer's utility from the product is
--   $$u=\omega\alpha+(1-\omega)\beta,$$
--   where $\alpha,\beta\in[0,1]$ are her matching values on two components and $\omega\in[0,1]$ is her private weight; $\alpha,\beta,\omega$ are independent and uniform on $[0,1]$, and there is a unit mass of consumers. The price $p$ is exogenous. A consumer who clicks learns $u$ and buys if and only if $u\ge p$.
--
--   **Targeting.** Under sd targeting the firm knows $\alpha$ and sends an ad (unit cost $c_{ad}>0$) to a set $\Sigma\subseteq[0,1]$ of $\alpha$-values; under md targeting it knows $(\alpha,\beta)$ and targets a set $\Sigma\subseteq[0,1]^2$.
--
--   **Inference and clicks.** A targeted consumer expects the targeting set $\widetilde\Sigma$. Her posterior is uniform: in the sd environment $\alpha$ is uniform on $\widetilde\Sigma$ and $\beta$ uniform on $[0,1]$ (Equation (2)); in the md environment $(\alpha,\beta)$ is uniform on $\widetilde\Sigma$ (Equation (5)). Her posterior expected surplus is
--   $$E[\max\{u-p,0\};\widetilde\Sigma]=\frac{1}{|\widetilde\Sigma|}\int_{\widetilde\Sigma}\max\{\omega\alpha+(1-\omega)\beta-p,0\},$$
--   (the integral running over $\widetilde\Sigma\times[0,1]$ in the sd case), and she clicks at effort cost $c_{click}>0$ if and only if it is at least $c_{click}$. The click set is $\Omega(\widetilde\Sigma)=\{\omega\in[0,1]: E[\max\{u-p,0\};\widetilde\Sigma]\ge c_{click}\}$ (Equation (3)).
--
--   **Ad values and profit.** Against a click set $\Omega$, the md ad value of the consumer $(\alpha,\beta)$ is
--   $$\pi^{md}(\alpha,\beta;\Omega)=p\cdot|\{\omega\in\Omega:\omega\alpha+(1-\omega)\beta\ge p\}|-c_{ad},$$
--   and the sd ad value of $\alpha$ is $\pi^{sd}(\alpha;\Omega)=p\cdot P(\omega\in\Omega,\ \omega\alpha+(1-\omega)\beta\ge p)-c_{ad}$ with $(\omega,\beta)$ uniform on $[0,1]^2$ (Equation (4)). The firm's profit from targeting $T$ is $\int_T\pi$.
--
--   **Equilibrium.** A non-trivial equilibrium is a measurable targeting set $\Sigma$ of positive measure, inside $[0,1]$ (sd) or $[0,1]^2$ (md), that maximizes the profit over all measurable targeting sets against the click set $\Omega(\Sigma)$ induced by consumers who correctly expect $\Sigma$ (p. 11, (i)–(iii)). An md equilibrium is symmetric if $\Sigma$ is symmetric about the 45-degree line. $\Pi^{sd}$ and $\Pi^{md}$ denote the equilibrium profits.
--
--   **Thresholds.** The file also defines the strategy $\Sigma^{md}(\gamma_1,\gamma_2)=[0,1]^2\cap(\{\beta\ge\gamma_1\alpha+p(1-\gamma_1),\ \alpha\le p\}\cup\{\beta\ge\gamma_2\alpha+p(1-\gamma_2),\ \alpha>p\})$ of the class $\mathcal S$ (Equation (6)), the click-cost threshold $c^{max}_{click}(c_{ad},p)$ of Equation (7) with its five cases, and the ad-cost threshold $\overline{c_{ad}}(c_{click},p)$ of the proof of Proposition 1, with its three cases:
--   $$\overline{c_{ad}}=\begin{cases}p(1-p)(1-\log(1-p)) & c_{click}\le\frac{(1-p)^2}{2},\\ p(1-p)\left(1+\log\frac{1-p}{2c_{click}}\right) & \frac{(1-p)^2}{2}<c_{click}\le\frac{1-p}{2},\\ 2p(1-p-c_{click}) & \frac{1-p}{2}<c_{click}.\end{cases}$$
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Measures are Lebesgue `volume` on $\mathbb R$ and $\mathbb R^2$ (a unit mass of uniformly distributed consumers), so probabilities are lengths and areas. Non-trivial means positive measure (the page says $\Sigma\ne\emptyset$; a null set has no posterior). Ties follow the page: buy at $u=p$, click at equality, and the equilibrium condition allows indifference. The third case of $\overline{c_{ad}}$ is printed for $c_{click}\le 1-p$; the same formula is used for larger $c_{click}$. Equilibria are defined as fixed points, never by the paper's closed forms.
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), pp. 9–18 (PDF 10–19), §2, §3, Equations (1)–(6); p. 41 (PDF 42), Equation (7); p. 35 (PDF 36), proof of Proposition 1, c̄_ad

import Mathlib

namespace TargetGranularity.SdVsMd

/-- Equation (1), p. 9: realized utility `u = ω·α + (1 − ω)·β` of a consumer with weight `ω`
and matching values `α`, `β`. -/
def util (ω α β : ℝ) : ℝ := ω * α + (1 - ω) * β

/-- The unit square `[0,1] × [0,1]` of matching values `(α, β)`. -/
def unitSq : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- Equations (5) and (3), md environment: the posterior expected surplus
`E[max{u − p, 0}; Σ̃]` of a targeted consumer of weight `ω` whose posterior on `(α, β)` is uniform
on the expected targeting set `S = Σ̃ ⊆ [0,1]²` (density `1/|Σ̃|` on `Σ̃`). -/
noncomputable def mdSurplus (p : ℝ) (S : Set (ℝ × ℝ)) (ω : ℝ) : ℝ :=
  (MeasureTheory.volume S).toReal⁻¹ * ∫ x in S, max (util ω x.1 x.2 - p) 0

/-- Equations (2) and (3), sd environment: the posterior expected surplus
`E[max{u − p, 0}; Σ̃]` of a targeted consumer of weight `ω`, whose posterior is `α` uniform on the
expected targeting set `S = Σ̃ ⊆ [0,1]` and `β` uniform on `[0,1]` (density `1/|Σ̃|` on `Σ̃ × [0,1]`). -/
noncomputable def sdSurplus (p : ℝ) (S : Set ℝ) (ω : ℝ) : ℝ :=
  (MeasureTheory.volume S).toReal⁻¹ *
    ∫ x in S ×ˢ Set.Icc (0 : ℝ) 1, max (util ω x.1 x.2 - p) 0

/-- Equation (3), md environment: the click set `Ω^md(Σ̃)`, the weights `ω ∈ [0,1]` whose
posterior expected surplus is at least the click cost (click iff `E[…] ≥ c_click`). -/
def mdClick (p cclick : ℝ) (S : Set (ℝ × ℝ)) : Set ℝ :=
  {ω ∈ Set.Icc (0 : ℝ) 1 | cclick ≤ mdSurplus p S ω}

/-- Equation (3), sd environment: the click set `Ω^sd(Σ̃)`. -/
def sdClick (p cclick : ℝ) (S : Set ℝ) : Set ℝ :=
  {ω ∈ Set.Icc (0 : ℝ) 1 | cclick ≤ sdSurplus p S ω}

/-- md ad value of the consumer `x = (α, β)` against the click set `Ω` (p. 18; proof of Claim 3,
p. 38): `π(α, β; Ω) = p · |{ω ∈ Ω : ω·α + (1 − ω)·β ≥ p}| − c_ad`, the expectation being over
`ω ~ U[0,1]` only (buy iff `u ≥ p`). -/
noncomputable def mdAdValue (p cad : ℝ) (Ω : Set ℝ) (x : ℝ × ℝ) : ℝ :=
  p * (MeasureTheory.volume (Ω ∩ {ω : ℝ | p ≤ util ω x.1 x.2})).toReal - cad

/-- Equation (4), sd ad value of the consumer with matching value `α` against the click set `Ω`:
`π^sd(α; p, Ω) = p · P(ω ∈ Ω and ω·α + (1 − ω)·β ≥ p) − c_ad`, the probability being over
`(ω, β) ~ U[0,1]²` (pairs `y = (ω, β)`). -/
noncomputable def sdAdValue (p cad : ℝ) (Ω : Set ℝ) (α : ℝ) : ℝ :=
  p * (MeasureTheory.volume
      ((Ω ×ˢ Set.Icc (0 : ℝ) 1) ∩ {y : ℝ × ℝ | p ≤ util y.1 α y.2})).toReal - cad

/-- The firm's md expected profit from targeting the set `T ⊆ [0,1]²` when consumers click
according to `Ω` (p. 11; §5.1 with `mc = 0`): the integral of the ad value over `T`. -/
noncomputable def mdProfitAgainst (p cad : ℝ) (Ω : Set ℝ) (T : Set (ℝ × ℝ)) : ℝ :=
  ∫ x in T, mdAdValue p cad Ω x

/-- The firm's sd expected profit from targeting the set `T ⊆ [0,1]` when consumers click
according to `Ω`. -/
noncomputable def sdProfitAgainst (p cad : ℝ) (Ω : Set ℝ) (T : Set ℝ) : ℝ :=
  ∫ α in T, sdAdValue p cad Ω α

/-- Non-trivial md equilibrium (p. 11, (i)–(iii), with expectation `Σ̃ = Σ`): `S` is a measurable
subset of the unit square of positive area, and it maximizes the firm's profit over every
measurable targeting set `T ⊆ [0,1]²`, against the click set that the uniform posterior on `S`
induces. -/
def IsMdEq (p cad cclick : ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  MeasurableSet S ∧ S ⊆ unitSq ∧ 0 < MeasureTheory.volume S ∧
    ∀ T : Set (ℝ × ℝ), MeasurableSet T → T ⊆ unitSq →
      mdProfitAgainst p cad (mdClick p cclick S) T ≤ mdProfitAgainst p cad (mdClick p cclick S) S

/-- Non-trivial symmetric md equilibrium: an md equilibrium whose targeting set is symmetric
about the 45-degree line (p. 17). -/
def IsSymMdEq (p cad cclick : ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  IsMdEq p cad cclick S ∧ Prod.swap ⁻¹' S = S

/-- Non-trivial sd equilibrium (p. 11, (i)–(iii), with expectation `Σ̃ = Σ`): `S` is a measurable
subset of `[0,1]` of positive length that maximizes the firm's profit over every measurable
`T ⊆ [0,1]`, against the click set that its own posterior induces. -/
def IsSdEq (p cad cclick : ℝ) (S : Set ℝ) : Prop :=
  MeasurableSet S ∧ S ⊆ Set.Icc (0 : ℝ) 1 ∧ 0 < MeasureTheory.volume S ∧
    ∀ T : Set ℝ, MeasurableSet T → T ⊆ Set.Icc (0 : ℝ) 1 →
      sdProfitAgainst p cad (sdClick p cclick S) T ≤ sdProfitAgainst p cad (sdClick p cclick S) S

/-- The firm's equilibrium profit `Π^md` at the md targeting set `S`. -/
noncomputable def mdProfit (p cad cclick : ℝ) (S : Set (ℝ × ℝ)) : ℝ :=
  mdProfitAgainst p cad (mdClick p cclick S) S

/-- The firm's equilibrium profit `Π^sd` at the sd targeting set `S`. -/
noncomputable def sdProfit (p cad cclick : ℝ) (S : Set ℝ) : ℝ :=
  sdProfitAgainst p cad (sdClick p cclick S) S

/-- Equation (6), p. 16: the strategy `Σ^md(γ₁, γ₂)` of the class `𝒮`,
`[0,1]² ∩ ({β ≥ γ₁·α + p(1 − γ₁), α ≤ p} ∪ {β ≥ γ₂·α + p(1 − γ₂), α > p})`. -/
def mdSet (p γ₁ γ₂ : ℝ) : Set (ℝ × ℝ) :=
  unitSq ∩ ({x : ℝ × ℝ | γ₁ * x.1 + p * (1 - γ₁) ≤ x.2 ∧ x.1 ≤ p} ∪
    {x : ℝ × ℝ | γ₂ * x.1 + p * (1 - γ₂) ≤ x.2 ∧ p < x.1})

/-- Equation (7), proof of Lemma 5, p. 41: the click-cost threshold `c^max_click(c_ad, p)`,
all five cases as printed. -/
noncomputable def cmaxClick (cad p : ℝ) : ℝ :=
  if p * (1 - p) < cad then
    (if p / 2 < cad then (1 - p) * (4 * cad - p) / (6 * cad)
     else (1 - p) * p / (6 * (p - cad)))
  else if cad ≤ p ^ 2 then
    (cad ^ 2 - 3 * cad * (1 - p) * p + 3 * (1 - p) ^ 2 * p ^ 2) /
      (6 * p * (p * (1 - p) * (1 + p) - cad))
  else if cad ≤ p / 2 then
    (3 * cad * (1 - 2 * p) * (p - cad) + p ^ 5) /
      (6 * cad * (p * (1 - p) * (1 + p) - cad))
  else
    (3 * cad ^ 2 * (1 - 2 * p) - 2 * cad * p * (2 * p ^ 3 - 6 * p + 3) +
        3 * p ^ 2 * (p ^ 3 - 2 * p + 1)) /
      (6 * (p - cad) * (p * (1 - p) * (1 + p) - cad))

/-- The ad-cost threshold `c̄_ad(c_click, p)` of the proof of Proposition 1, p. 35, all three
cases as printed (the third case is printed for `(1−p)/2 < c_click ≤ 1 − p`; its formula is used
for every larger `c_click`). -/
noncomputable def cadBar (cclick p : ℝ) : ℝ :=
  if cclick ≤ (1 - p) ^ 2 / 2 then p * (1 - p) * (1 - Real.log (1 - p))
  else if cclick ≤ (1 - p) / 2 then p * (1 - p) * (1 + Real.log ((1 - p) / (2 * cclick)))
  else 2 * p * (1 - p - cclick)

end TargetGranularity.SdVsMd


