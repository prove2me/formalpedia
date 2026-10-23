-- Prove2me | Definitions.Def_Sherlocking_InfoPolicy_Model
-- name    : Sherlocking_InfoPolicy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:36.999873+00:00
-- url     : https://prove2.me/theorems/2203e18c-52d8-418f-872b-1f52b951ba85
-- title:
--   §2–§5.1, pp. 8–15 — platform/seller entry game: cutoffs θ_S, θ_P, commitment policy α, Π^C_P, signals, weak-PBE equilibrium, (OC0), (OC1), (4), signal (3)
-- statement:
--   This file sets up the model of Choi, Kim & Mukherjee, *“Sherlocking” and Platform Information Policy*, §2–§5.1.
--
--   **Primitives.** A platform $P$ hosts a seller $S$ for two periods of lengths $1-\delta$ and $\delta$. The platform posts an ad valorem referral fee $r \in [0,1]$. The seller's type $\theta$, his monopoly profit per unit time, is uniform on $[0,1]$ and privately known; entry costs him $K$. After the first period the platform observes (a signal about) $\theta$ and may imitate the product at the same cost $K$, taking the whole second-period profit. The standing restriction is Assumption 1,
--   $$1-\delta < K < \delta .$$
--
--   **Payoffs.** If the seller enters and the platform enters with probability $q$, the seller's expected net gain is
--   $$g_S(q,\theta) = \big[(1-\delta)+\delta(1-q)\big](1-r)\theta - K,$$
--   and the platform's payoff from entering with probability $b$ against type $\theta$ is
--   $$\pi_P(r,\theta;b) = (1-\delta)r\theta + (1-b)\,\delta r\theta + b\,(\delta\theta-K),$$
--   the paper's $\pi_P$ with the indicator $\mathbf 1_E$ replaced by $b$. A seller who stays out gives both players $0$.
--
--   **Cutoffs (1), (2).** $\theta_S(r) = \min\{K/(1-r),1\}$, the lowest type that enters when the platform never enters, and $\theta_P(r) = \min\{K/(\delta(1-r)),1\}$, the lowest type against which the platform gains from entering.
--
--   **Full commitment (§4).** The binding entry probability is
--   $$\alpha(\theta;r) = \frac1\delta\Big(1-\frac{K}{(1-r)\theta}\Big),$$
--   and the full-commitment policy enters with probability $\alpha(\theta;r)$ for $\theta\in[\theta_P(r),1]$ and $0$ otherwise. For a commitment policy $a$ (type $\mapsto$ entry probability) the platform's objective is
--   $$\int_{\Theta_E}\big[(1-a(\theta))r\theta + a(\theta)\big((1-\delta)r\theta+\delta\theta-K\big)\big]\,d\theta,\qquad \Theta_E=\{\theta\in[0,1] : [(1-\delta)+\delta(1-a(\theta))](1-r)\theta\ge K\},$$
--   and the reduced objective of $\mathcal P_C$ is
--   $$\Pi^C_P(r) = \int_{\theta_S(r)}^{\theta_P(r)} r\theta\,d\theta + \int_{\theta_P(r)}^{1}\Big[(1-\delta)r\theta + \alpha(\theta;r)(\delta\theta-K) + (1-\alpha(\theta;r))\delta r\theta\Big]d\theta .$$
--
--   **Information policies and equilibrium (§5).** An information policy is a set $X$ of realizations with a measurable family $\sigma(\theta)$ of probability distributions on $X$. A platform strategy $\beta : X\to[0,1]$ gives the entry probability after each realization, so type $\theta$ faces entry probability $q(\theta)=\int\beta\,d\sigma(\theta)$. Given a set $E$ of entering types, the platform's expected payoff is $\int_{E\cap[0,1]}\int\pi_P(r,\theta;\beta(x))\,d\sigma(\theta)(x)\,d\theta$. The triple $(\sigma,\beta,E)$ is an **equilibrium** at fee $r$ when (i) every type $\theta\in[0,1]$ in $E$ has $g_S(q(\theta),\theta)\ge0$ and every type in $[0,1]$ outside $E$ has $g_S(q(\theta),\theta)\le0$ (either action at indifference), and (ii) $\beta$ maximizes the platform's expected payoff over all measurable strategies $\beta' : X\to[0,1]$. The equilibrium **implements the full commitment outcome** when the entering types in $[0,1]$ are exactly $[\theta_S(r),1]$ and every such type faces entry probability equal to the full-commitment policy. The full commitment outcome is **implementable by an information policy** when some $X$, $\sigma$, $\beta$, $E$ form such an equilibrium.
--
--   **Signal (3) and the constraints.** Signal (3) sends $x=1$ with the full-commitment probability and $x=0$ otherwise; the obedient strategy enters iff $x=1$. Under (3), with types uniform on $[\theta_S(r),1]$,
--   $$\text{(OC0)}\quad \mathbb E[\theta\mid x=0;\ \theta\ge\theta_S(r)]\le\theta_P(r),\qquad \text{(OC1)}\quad \mathbb E[\theta\mid x=1;\ \theta\ge\theta_S(r)]>\theta_P(r),$$
--   each written as a ratio of integrals over $[\theta_S(r),1]$, and inequality (4) at fee $r$ is
--   $$\int_{\theta_P(r)}^{1}(\theta-\theta_P(r))(1-\alpha(\theta;r))\,d\theta \le \int_{\theta_S(r)}^{\theta_P(r)}(\theta_P(r)-\theta)\,d\theta .$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Everything is real-valued, and $K,\delta$ come first as explicit arguments. The cutoffs are written in guarded form, $K/(1-r)$ if $K<1-r$ and $1$ otherwise (likewise for $\theta_P$); this equals the printed minimum for every $r<1$ and gives $1$ at $r=1$, where Lean's convention $K/0=0$ would otherwise produce the junk value $0$. The full-commitment probability is cut off at $\theta>1$ as well as below $\theta_P(r)$. Signals are unbundled: a measurable map $\sigma:\mathbb R\to\mathrm{Measure}(X)$ into probability measures, for any `X : Type` with a σ-algebra (equivalent to a Markov kernel). The platform's sequential rationality is stated in ex-ante form, optimality against every measurable $[0,1]$-valued deviation; this is equivalent to Bayes-rational play after almost every on-path realization, with off-path beliefs free. The conditional expectations in (OC0), (OC1) are ratios of integrals, because the uniform density cancels; such a ratio is $0/0=0$ in Lean when its denominator vanishes, so statements using them assume the denominator positive (through $r<1-K$). Signal (3) is the measure $\mathrm{ofReal}(p)\,\delta_{1} + \mathrm{ofReal}(1-p)\,\delta_{0}$ on `Bool`.
-- source:
--   Choi, Kim & Mukherjee, “Sherlocking” and Platform Information Policy, CESifo Working Paper No. 10769 / SSRN 4643950 (version of November 13, 2023), pp. 8–15 (PDF 10–17), §2 (payoffs, Assumption 1, weak PBE), §3 Eqs. (1)–(2), §4 Eq. (E), α, Π^C_P, §5 Lemma 1, §5.1 Eqs. (3), (OC0), (OC1), (4)

import Mathlib

namespace Sherlocking.InfoPolicy

open MeasureTheory

/-- Cutoff (1): `θ_S(r) = min{K/(1-r), 1}`, written in guarded form. For `r < 1` it equals the
printed minimum; at `r = 1` it is `1` (Lean's `K / 0 = 0` would otherwise give the junk value `0`). -/
noncomputable def thetaS (K r : ℝ) : ℝ := if K < 1 - r then K / (1 - r) else 1

/-- Cutoff (2): `θ_P(r) = min{K/(δ(1-r)), 1}`, guarded in the same way. -/
noncomputable def thetaP (K δ r : ℝ) : ℝ := if K < δ * (1 - r) then K / (δ * (1 - r)) else 1

/-- §4: the entry probability that makes the seller's entry constraint (E) bind,
`α(θ; r) = (1/δ)(1 - K/((1-r)θ))`. -/
noncomputable def alpha (K δ θ r : ℝ) : ℝ := (1 / δ) * (1 - K / ((1 - r) * θ))

/-- The full-commitment entry probability at fee `r`: `α(θ; r)` for `θ ∈ [θ_P(r), 1]`, and `0`
otherwise. -/
noncomputable def commitProb (K δ r θ : ℝ) : ℝ :=
  if thetaP K δ r ≤ θ ∧ θ ≤ 1 then alpha K δ θ r else 0

/-- `Π^C_P(r)`, p. 13, as printed. -/
noncomputable def PiC (K δ r : ℝ) : ℝ :=
  (∫ θ in (thetaS K r)..(thetaP K δ r), r * θ) +
  ∫ θ in (thetaP K δ r)..1,
    ((1 - δ) * r * θ + (alpha K δ θ r * (δ * θ - K) + (1 - alpha K δ θ r) * (δ * r * θ)))

/-- §4: the platform's objective at fee `r` for a commitment policy `a` (type `θ` ↦ probability of
entry), integrated over the set `Θ_E` of types in `[0,1]` that satisfy (E). -/
noncomputable def commitPayoff (K δ r : ℝ) (a : ℝ → ℝ) : ℝ :=
  ∫ θ in {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ K ≤ ((1 - δ) + δ * (1 - a θ)) * (1 - r) * θ},
    ((1 - a θ) * r * θ + a θ * ((1 - δ) * r * θ + δ * θ - K))

/-- The seller's expected net payoff from entering (`π_S` averaged) when the platform enters with
probability `q`. -/
def sellerGain (K δ r q θ : ℝ) : ℝ := ((1 - δ) + δ * (1 - q)) * (1 - r) * θ - K

/-- `π_P(r, θ)`, with the indicator `1_E` replaced by the platform's entry probability `b`. -/
def platformPayoff (K δ r b θ : ℝ) : ℝ :=
  (1 - δ) * r * θ + (1 - b) * (δ * r * θ) + b * (δ * θ - K)

section
variable {X : Type} [MeasurableSpace X]

/-- An information policy (signal): a measurable family `θ ↦ σ(θ)` of probability measures on
the set `X` of signal realizations. -/
def IsInfoPolicy (σ : ℝ → Measure X) : Prop :=
  Measurable σ ∧ ∀ θ, IsProbabilityMeasure (σ θ)

/-- Probability that the platform enters when the seller's type is `θ`, if it enters with
probability `β x` after realization `x`. -/
noncomputable def entryProb (σ : ℝ → Measure X) (β : X → ℝ) (θ : ℝ) : ℝ := ∫ x, β x ∂(σ θ)

/-- The platform's expected payoff from strategy `β` when the types in `E` enter (θ uniform on
`[0,1]`; types that stay out yield `0`). -/
noncomputable def platformValue (K δ r : ℝ) (σ : ℝ → Measure X) (β : X → ℝ) (E : Set ℝ) : ℝ :=
  ∫ θ in E ∩ Set.Icc (0:ℝ) 1, ∫ x, platformPayoff K δ r (β x) θ ∂(σ θ)

/-- Weak perfect Bayesian equilibrium at fee `r` under the information policy `σ`: the seller
best-responds type by type (either action is allowed at indifference); the platform, which cannot
commit, plays a strategy `β` that maximizes its expected payoff among all measurable `[0,1]`-valued
strategies (ex-ante form of sequential rationality). -/
structure IsEquilibrium (K δ r : ℝ) (σ : ℝ → Measure X) (β : X → ℝ) (E : Set ℝ) : Prop where
  seller_in : ∀ θ ∈ Set.Icc (0:ℝ) 1, θ ∈ E → 0 ≤ sellerGain K δ r (entryProb σ β θ) θ
  seller_out : ∀ θ ∈ Set.Icc (0:ℝ) 1, θ ∉ E → sellerGain K δ r (entryProb σ β θ) θ ≤ 0
  platform_opt : ∀ β' : X → ℝ, Measurable β' → (∀ x, β' x ∈ Set.Icc (0:ℝ) 1) →
    platformValue K δ r σ β' E ≤ platformValue K δ r σ β E

/-- The equilibrium outcome is the full commitment outcome at fee `r`: exactly the types in
`[θ_S(r), 1]` enter, and the platform enters against type `θ` with probability `commitProb`. -/
def ImplementsCommitment (K δ r : ℝ) (σ : ℝ → Measure X) (β : X → ℝ) (E : Set ℝ) : Prop :=
  E ∩ Set.Icc (0:ℝ) 1 = Set.Icc (thetaS K r) 1 ∧
  ∀ θ ∈ Set.Icc (thetaS K r) 1, entryProb σ β θ = commitProb K δ r θ

end

/-- The full commitment outcome at fee `r` is implementable by an information policy: some set of
realizations `X`, signal `σ`, platform strategy `β` and entry set `E` form an equilibrium whose
outcome is the full commitment outcome. -/
def CommitmentImplementable (K δ r : ℝ) : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (σ : ℝ → Measure X) (β : X → ℝ) (E : Set ℝ),
    IsInfoPolicy σ ∧ Measurable β ∧ (∀ x, β x ∈ Set.Icc (0:ℝ) 1) ∧ MeasurableSet E ∧
    IsEquilibrium K δ r σ β E ∧ ImplementsCommitment K δ r σ β E

/-- (OC0) under signal (3): `E[θ | x = 0; θ ≥ θ_S(r)] ≤ θ_P(r)`, where
`Pr(x = 0 | θ) = 1 - commitProb`. -/
def OC0 (K δ r : ℝ) : Prop :=
  (∫ θ in (thetaS K r)..1, θ * (1 - commitProb K δ r θ)) /
    (∫ θ in (thetaS K r)..1, (1 - commitProb K δ r θ)) ≤ thetaP K δ r

/-- (OC1) under signal (3): `E[θ | x = 1; θ ≥ θ_S(r)] > θ_P(r)`. -/
def OC1 (K δ r : ℝ) : Prop :=
  thetaP K δ r < (∫ θ in (thetaS K r)..1, θ * commitProb K δ r θ) /
    (∫ θ in (thetaS K r)..1, commitProb K δ r θ)

/-- Inequality (4), at fee `r`. -/
def Ineq4 (K δ r : ℝ) : Prop :=
  (∫ θ in (thetaP K δ r)..1, (θ - thetaP K δ r) * (1 - alpha K δ θ r)) ≤
    ∫ θ in (thetaS K r)..(thetaP K δ r), (thetaP K δ r - θ)

/-- Signal (3): realization `x = 1` (`true`) with probability `commitProb`, otherwise `x = 0`
(`false`). -/
noncomputable def signal3 (K δ r θ : ℝ) : Measure Bool :=
  ENNReal.ofReal (commitProb K δ r θ) • Measure.dirac true +
    ENNReal.ofReal (1 - commitProb K δ r θ) • Measure.dirac false

/-- The obedient platform strategy on binary signals: enter iff `x = 1`. -/
def recommend (b : Bool) : ℝ := if b then 1 else 0

end Sherlocking.InfoPolicy


