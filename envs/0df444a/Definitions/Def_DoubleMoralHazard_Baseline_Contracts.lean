-- Prove2me | Definitions.Def_DoubleMoralHazard_Baseline_Contracts
-- name    : DoubleMoralHazard_Baseline_Contracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:27.091569+00:00
-- url     : https://prove2.me/theorems/c825c036-7172-487e-9e62-7366c8c10fe7
-- title:
--   §2.1, pp. 11–12 — contracts γ = (L, τ), limited liability, Γ, utilities u (2.1) and U (2.2), (IC), Γ^IC
-- statement:
--   A **contract** $\gamma=(L,\tau)$ consists of a cumulative payment process $L$ and a termination time $\tau$, both determined by what the principal observes: the reported $u$-arrivals and the $o$-arrivals. It is given by a payment function, $L_t=\mathrm{pay}(h,t)$ while the observed history is $h$, and a stopping rule, the termination time $\mathrm{stop}(h)$ if nothing further is observed after $h$. The contract has **limited liability** when the realized payment path is nondecreasing from $L_{0-}=0$ (instantaneous and flow payments are nonnegative); $\Gamma$ is the set of measurable contracts with limited liability.
--
--   For a strategy $\sigma$ (effort $\nu$, reports $\hat N^u$) the agent's expected total discounted utility (2.1) is
--   $$u(\gamma,\nu,\hat N^u)=\mathbb E\Big[\int_0^\tau e^{-rt}\big[R^u(dN^u_t-d\hat N^u_t)+dL_t+c(1-\mathbb 1[\nu_t=\mu])\,dt\big]\Big],$$
--   diverted cash plus payments plus effort cost saved by shirking. The principal's expected discounted profit (2.2) under full effort and truthful reporting is
--   $$U(\gamma,\bar\nu,N^u)=\mathbb E\Big[\int_0^\tau e^{-rt}\big[R^u\,dN^u_t+R^o\,dN^o_t-dL_t-c\,dt\big]\Big].$$
--
--   A contract is **incentive compatible** (IC) if
--   $$u(\gamma,\bar\nu,N^u)\ \ge\ u(\gamma,\nu,\hat N^u)$$
--   for every measurable strategy, i.e. every effort process jointly with every reporting rule. $\Gamma^{IC}$ is the set of contracts in $\Gamma$ that satisfy (IC) and whose expected discounted payments under $(\bar\nu,N^u)$ are finite. The principal's problem is to maximize $U$ over $\Gamma^{IC}$.
--
--   **Formalization Note** The realized termination time is the first $\mathrm{stop}(h_k)$ that precedes the next arrival; integrals run over $[0,\tau]$, so a payment at time $0$ and at $\tau$ counts and revenue after $\tau$ does not. Each term of (2.1) is nonnegative, so $u$ is an $[0,\infty]$-valued expectation (lower Lebesgue integral), and $\int e^{-rt}dL_t$ is the Lebesgue–Stieltjes integral against the realized nondecreasing path. $U$ is a real number assembled from three finite $[0,\infty]$-valued expectations (revenue, payments, reimbursed effort cost); excluding contracts with infinite expected payments (whose principal utility is $-\infty$) loses no candidate for optimality. Measurability of a contract means that under every measurable strategy the realized termination time and payment path are measurable. The individual rationality condition $W_t\ge 0$ holds automatically, since every term of the agent's utility is nonnegative.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), pp. 11–12, §2.1, (2.1), (2.2), (IC), footnotes 8, 9, 12

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_Arrivals

namespace DoubleMoralHazard.Baseline

open MeasureTheory
open scoped ENNReal

/-- A contract `γ = (L, τ)` (p. 11), written as functions of the principal's record (reported
`u`-arrivals and `o`-arrivals, footnote 8).
* `pay h t` is the cumulative payment `L_t` at time `t` while the observed history is `h`.
* `stop h` is the termination time if no further event is observed after `h`. -/
structure Contract where
  pay : PubHistory → ℝ → ℝ
  stop : PubHistory → ℝ≥0∞

/-- Limited liability (p. 11): payments are nonnegative, `I_t ≥ 0` and `ℓ_t ≥ 0`, i.e. the realized
cumulative payment is nondecreasing, starting from `L_{0-} = 0`. Each `pay h` is nondecreasing, and an
observed event never lowers the cumulative payment below its left limit. -/
def IsLimitedLiability (γ : Contract) : Prop :=
  (∀ h, Monotone (γ.pay h)) ∧
  (∀ t : ℝ, t < 0 → γ.pay [] t = 0) ∧
  ∀ (h : PubHistory) (e : ℝ × Bool), (∀ x ∈ h, x.1 ≤ e.1) →
    Function.leftLim (γ.pay h) e.1 ≤ γ.pay (h ++ [e]) e.1

/-- The realized termination time `τ`: after the `k`-th arrival the contract terminates at
`stop (public history)` unless a further arrival comes strictly earlier. -/
noncomputable def termTime (P : Params) (γ : Contract) (σ : Strategy) (ω : Omega) : ℝ≥0∞ :=
  ⨅ (k : ℕ) (_ : γ.stop (publicPart (run P σ ω k).1) < (run P σ ω (k + 1)).2),
    max (run P σ ω k).2 (γ.stop (publicPart (run P σ ω k).1))

/-- The realized cumulative payment path `t ↦ L_t` (`L_t = 0` for `t < 0`). -/
noncomputable def payPath (P : Params) (γ : Contract) (σ : Strategy) (ω : Omega) (t : ℝ) : ℝ :=
  if t < 0 then 0 else γ.pay (publicPart (run P σ ω (numArrivals P σ ω t)).1) t

/-- The window `[0, τ]` of employment, as a set of real times. -/
def employed (τ : ℝ≥0∞) : Set ℝ := {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t ≤ τ}

open Classical in
/-- `∫_{[0,τ]} e^{-rt} dL_t`, the discounted payments (Stieltjes integral against the nondecreasing
path `L`; it includes a payment `I_0` at time `0`). The `else` branch is never used for a contract
with limited liability. -/
noncomputable def discPayment (P : Params) (γ : Contract) (σ : Strategy) (ω : Omega) : ℝ≥0∞ :=
  if hL : Monotone (payPath P γ σ ω) then
    ∫⁻ t in employed (termTime P γ σ ω), ENNReal.ofReal (Real.exp (-(P.r * t)))
      ∂hL.stieltjesFunction.measure
  else 0

/-- `∫_0^τ e^{-rt} Rᵘ (dNᵘ_t - dN̂ᵘ_t)`: the diverted cash of the hidden `u`-arrivals. -/
noncomputable def divertedCash (P : Params) (γ : Contract) (σ : Strategy) (ω : Omega) : ℝ≥0∞ :=
  ∑' k : ℕ, match arrival P σ ω k with
    | some (t, ch, rep) =>
        if ENNReal.ofReal t ≤ termTime P γ σ ω ∧ ch = true ∧ rep = false then
          ENNReal.ofReal (Real.exp (-(P.r * t)) * P.Ru) else 0
    | none => 0

/-- `∫_0^τ e^{-rt} c (1 - 𝕀[ν_t = µ]) dt`: the effort cost saved by shirking. -/
noncomputable def shirkBenefit (P : Params) (γ : Contract) (σ : Strategy) (ω : Omega) : ℝ≥0∞ :=
  ∫⁻ t in employed (termTime P γ σ ω),
    if effortAt P σ ω t then 0 else ENNReal.ofReal (Real.exp (-(P.r * t)) * P.c)

/-- The agent's expected total discounted utility `u(γ, ν, N̂ᵘ)` of (2.1), for the strategy `σ`
(which determines `ν` and `N̂ᵘ`). Every term is nonnegative, so it is an `ℝ≥0∞`-valued expectation. -/
noncomputable def u (P : Params) (γ : Contract) (σ : Strategy) : ℝ≥0∞ :=
  ∫⁻ ω, divertedCash P γ σ ω + discPayment P γ σ ω + shirkBenefit P γ σ ω ∂(law P)

/-- `∫_0^τ e^{-rt} (Rᵘ dN̂ᵘ_t + Rᵒ dNᵒ_t)`: the principal's revenue from observed arrivals. -/
noncomputable def revenue (P : Params) (γ : Contract) (σ : Strategy) (ω : Omega) : ℝ≥0∞ :=
  ∑' k : ℕ, match arrival P σ ω k with
    | some (t, ch, rep) =>
        if ENNReal.ofReal t ≤ termTime P γ σ ω then
          (if ch = true then (if rep = true then ENNReal.ofReal (Real.exp (-(P.r * t)) * P.Ru) else 0)
           else ENNReal.ofReal (Real.exp (-(P.r * t)) * P.Ro))
        else 0
    | none => 0

/-- `∫_0^τ e^{-rt} c dt`: the effort cost the principal reimburses. -/
noncomputable def effortCost (P : Params) (γ : Contract) (σ : Strategy) (ω : Omega) : ℝ≥0∞ :=
  ∫⁻ t in employed (termTime P γ σ ω), ENNReal.ofReal (Real.exp (-(P.r * t)) * P.c)

/-- The principal's expected total discounted profit `U(γ, ν̄, Nᵘ)` of (2.2), under full effort and
truthful reporting: revenue minus payments minus reimbursed effort cost, each an expectation in
`ℝ≥0∞`. The revenue and cost parts are always finite (at most `µ (Rᵘ + Rᵒ) / r` and `c / r`); the
payment part is finite on `Γ^IC`, where this is used. -/
noncomputable def U (P : Params) (γ : Contract) : ℝ :=
  (∫⁻ ω, revenue P γ sbar ω ∂(law P)).toReal
    - (∫⁻ ω, discPayment P γ sbar ω ∂(law P)).toReal
    - (∫⁻ ω, effortCost P γ sbar ω ∂(law P)).toReal

/-- Measurability of a contract: under every measurable strategy the realized termination time and
the realized payment path are measurable. -/
def IsMeasurableContract (P : Params) (γ : Contract) : Prop :=
  ∀ σ, IsMeasurableStrategy P σ →
    Measurable (fun ω => termTime P γ σ ω) ∧
    Measurable (fun q : Omega × ℝ => payPath P γ σ q.1 q.2)

/-- The contract space `Γ` (p. 11): measurable contracts with limited liability. -/
def Gamma (P : Params) : Set Contract :=
  {γ | IsLimitedLiability γ ∧ IsMeasurableContract P γ}

/-- Incentive compatibility (IC), p. 12: no measurable strategy (any effort process jointly with any
reporting rule) gives the agent more than full effort with truthful reporting. -/
def IsIC (P : Params) (γ : Contract) : Prop :=
  ∀ σ : Strategy, IsMeasurableStrategy P σ → u P γ σ ≤ u P γ sbar

/-- `Γ^IC`: contracts in `Γ` satisfying (IC) whose expected payments under `(ν̄, Nᵘ)` are finite.
(A contract with infinite expected payments has principal utility `-∞` and is excluded.) -/
def GammaIC (P : Params) : Set Contract :=
  {γ | γ ∈ Gamma P ∧ IsIC P γ ∧ u P γ sbar < ⊤}

end DoubleMoralHazard.Baseline


