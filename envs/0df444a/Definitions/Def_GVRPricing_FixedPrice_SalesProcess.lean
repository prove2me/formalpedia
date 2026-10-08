-- Prove2me | Definitions.Def_GVRPricing_FixedPrice_SalesProcess
-- name    : GVRPricing_FixedPrice_SalesProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:38:28.929628+00:00
-- url     : https://prove2.me/theorems/d3409a53-8ca5-4eee-8e80-75fcf44a8ac2
-- title:
--   §2.2 — non-anticipating policies, the controlled Poisson sales process, J_u(n,t), J*(n,t) (eqs. (2)–(7)), and the fixed-price revenues J^FP, J^OFP
-- statement:
--   This file builds the stochastic pricing problem of Gallego and van Ryzin (1994), §2.2, and the fixed-price heuristics of §3.3.
--
--   **Policies.** A firm with $n$ items sells over the horizon $[0,t]$, measured in elapsed time $s$. A **non-anticipating pricing policy** $u$ chooses, at time $s$ and with $j$ items already sold at times $\tau_1\le\dots\le\tau_j$, an intensity $\varphi_j(s;\tau_1,\dots,\tau_j)\in\Lambda$, i.e. the price $p(\varphi_j(s;\tau))$. The rule is jointly measurable and locally integrable in time.
--
--   **Sales process.** Demand is a Poisson process whose intensity is the one chosen by the policy. It is constructed from i.i.d. exponential clocks $E_0,E_1,\dots\sim\mathrm{Exp}(1)$: the $(j+1)$-st sale occurs at the first time $s\ge\tau_j$ with
--   $$\int_{\tau_j}^{s}\varphi_j(v;\tau_1,\dots,\tau_j)\,dv\ \ge\ E_j,$$
--   and never if there is no such time ($\tau_0=0$). Only $n$ clocks are used, so at most $n$ items are sold (constraint (2)); after the $n$-th sale the intensity is $0$, the null price. $N_s$ is the number of sales in $[0,s]$, and $\lambda_s$ is the intensity in force at time $s$.
--
--   **Values.** The expected revenue of $u$ is
--   $$J_u(n,t)=E_u\Big[\int_0^t p_s\,dN_s\Big],$$
--   the expected sum of the prices charged at the sales made by time $t$ (eq. (4)), and the optimal expected revenue is
--   $$J^*(n,t)=\sup_{u\in\mathcal U}J_u(n,t)\qquad\text{(eq. (7))}.$$
--   The file also defines $E_u[N_t]$, $E_u[\int_0^t\lambda_s\,ds]$, $E_u[\int_0^t r(\lambda_s)\,ds]$, and the augmented functional
--   $$J_u(n,t,\mu)=E_u\Big[\int_0^t\big(r(\lambda_s)-\mu\lambda_s\big)ds\Big]+n\mu\qquad\text{(eq. (15))}.$$
--
--   **Fixed-price heuristics** (§3.3). $J^{FP}(n,t)$ is the expected revenue of the policy that charges $p^D=p(\lambda^D)$, $\lambda^D=\min\{\lambda^*,n/t\}$, throughout. $J^{OFP}(n,t)$ is the supremum of the expected revenues of all constant prices, i.e. of all constant rates $c\in\Lambda$.
--
--   These are the objects compared in Theorems 2 and 3.
--
--   **Formalization Note** All values are in $[0,\infty]$ (`ℝ≥0∞`, lower Lebesgue integrals), so no expectation is silently truncated. Policies depend on the past sale times only (the internal history of the sales process); randomized policies are not included. The intensity is required to be locally integrable, the standard non-explosion condition of the counting-process framework (the paper notes $\int_0^t\lambda_s\,ds<\infty$). The price recorded at a sale is the one set at the sale instant by the pre-sale state; it differs from the left-limit (predictable) version only on a null set. $J_u(n,0)=0$ and $J_u(0,t)=0$ (eqs. (5)–(6)) are consequences of the construction, not definitions. The augmented functional is real-valued, using the real parts of two expectations that are finite (they are at most $t r^*$ and $n$); the theorems that use it assert that finiteness. The constant policy at a rate $c\notin\Lambda$ falls back to the null price; every use has $c\in\Lambda$.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1004 (PDF 6), §2.2, eqs. (2)–(7); p. 1007 (PDF 9), eq. (15); p. 1007 (PDF 9), §3.3, definitions of J^FP and J^OFP

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- A **non-anticipating pricing policy** (§2.2, p. 1004), in rate form and in **elapsed time**
`s ≥ 0`. `φ j s τ` is the demand intensity `λ_s` the firm sets at elapsed time `s` while `j`
items have been sold so far, the past sale times being `τ = (τ₁, …, τ_j)`; the price charged is
`p(φ j s τ)`. The intensity always lies in `Λ` (constraint (3)), is jointly measurable, and is
locally integrable in time (`∫ λ_s ds < ∞` on bounded intervals, so the sales process does not
explode). Constraint (2) (at most `n` sales) is not a field: it is built into the sales process
below, which has exactly `n` clocks and intensity `0` (the null price) after the `n`-th sale. -/
structure Policy (M : Model) where
  /-- The intensity rule. -/
  φ : (j : ℕ) → ℝ → (Fin j → ℝ) → ℝ
  measurable : ∀ j, Measurable (fun q : ℝ × (Fin j → ℝ) => φ j q.1 q.2)
  mem : ∀ j s τ, φ j s τ ∈ M.Λ
  locallyIntegrable : ∀ j τ (a b : ℝ), ∫⁻ v in Ioc a b, ENNReal.ofReal (φ j v τ) ≠ ∞

/-- The time of the last of `j` sales with times `τ`, and `0` (time zero) when `j = 0`. -/
def lastTime : (j : ℕ) → (Fin j → ℝ) → ℝ
  | 0, _ => 0
  | k + 1, τ => τ (Fin.last k)

/-- The i.i.d. `Exp(1)` clocks `E₀, E₁, …` that drive the sales process: the infinite product of
the exponential distribution with rate `1`. -/
noncomputable def clockLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => expMeasure 1)

namespace Policy

variable {M : Model} (u : Policy M)

/-- Cumulative intensity `∫_{(τ_j, s]} λ_v dv` accumulated since the last sale, while `j` items
have been sold at times `τ`. -/
noncomputable def cumIntensity (j : ℕ) (τ : Fin j → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Ioc (lastTime j τ) s, ENNReal.ofReal (u.φ j v τ)

open Classical in
/-- The time of the `(j+1)`-st sale given the first `j` sale times `τ` and the clock value `e`:
the first time `s ≥ τ_j` at which the cumulative intensity since `τ_j` reaches `e`, or `none`
if it never does. -/
noncomputable def nextSale (j : ℕ) (τ : Fin j → ℝ) (e : ℝ) : Option ℝ :=
  if {s : ℝ | lastTime j τ ≤ s ∧ ENNReal.ofReal e ≤ u.cumIntensity j τ s}.Nonempty then
    some (sInf {s : ℝ | lastTime j τ ≤ s ∧ ENNReal.ofReal e ≤ u.cumIntensity j τ s})
  else none

/-- The sales history driven by the clocks `E`: `history E j = some τ` with `τ` the first `j`
sale times if at least `j` sales ever occur, and `none` otherwise. The `(j+1)`-st sale uses the
clock `E j`. -/
noncomputable def history (E : ℕ → ℝ) : (j : ℕ) → Option (Fin j → ℝ)
  | 0 => some Fin.elim0
  | j + 1 => (history E j).bind fun τ =>
      (u.nextSale j τ (E j)).map fun s => Fin.snoc (α := fun _ => ℝ) τ s

/-- `saleTime E j` is the time `τ_j` of the `j`-th sale (`τ₀ = 0`), and `⊤` if fewer than `j`
sales ever occur. -/
noncomputable def saleTime (E : ℕ → ℝ) (j : ℕ) : WithTop ℝ :=
  (u.history E j).elim ⊤ fun τ => ((lastTime j τ : ℝ) : WithTop ℝ)

open Classical in
/-- `N_t`: the number of items sold in `[0, t]` from an initial stock `n`. -/
noncomputable def salesBy (n : ℕ) (t : ℝ) (E : ℕ → ℝ) : ℕ :=
  ((Finset.range n).filter fun j => u.saleTime E (j + 1) ≤ ((t : ℝ) : WithTop ℝ)).card

open Classical in
/-- `λ_s`: the intensity in force at time `s` from an initial stock `n`, i.e. `φ j s (τ₁,…,τ_j)`
for `τ_j < s ≤ τ_{j+1}` and `j < n`, and `0` (null price) once all `n` items are sold. -/
noncomputable def intensityAt (n : ℕ) (E : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (u.history E j).elim 0 fun τ =>
    if lastTime j τ < s ∧ ((s : ℝ) : WithTop ℝ) ≤ u.saleTime E (j + 1) then u.φ j s τ else 0

open Classical in
/-- `∫_0^t p_s dN_s`: the revenue collected in `[0, t]` from an initial stock `n`, the sum over
the (at most `n`) sales made by time `t` of the price charged at the sale, `p` of the intensity
`φ j τ_{j+1} (τ₁, …, τ_j)` in force at the sale instant. -/
noncomputable def revenueOn (n : ℕ) (t : ℝ) (E : ℕ → ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range n, (u.history E (j + 1)).elim 0 fun τ =>
    if τ (Fin.last j) ≤ t then
      ENNReal.ofReal (M.price (u.φ j (τ (Fin.last j)) (Fin.init (α := fun _ => ℝ) τ)))
    else 0

/-- `J_u(n, t) = E_u[∫_0^t p_s dN_s]`, eq. (4): the expected revenue of the policy `u` from an
initial stock `n` over the horizon `[0, t]`. -/
noncomputable def expectedRevenue (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ E, u.revenueOn n t E ∂clockLaw

/-- `E_u[∫_0^t dN_s] = E_u[N_t]`, the expected number of sales in `[0, t]`. -/
noncomputable def expectedSales (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ E, (u.salesBy n t E : ℝ≥0∞) ∂clockLaw

/-- `E_u[∫_0^t λ_s ds]`, the expected cumulative intensity over `[0, t]`. -/
noncomputable def expectedCumIntensity (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ E, (∫⁻ s in Ioc 0 t, ENNReal.ofReal (u.intensityAt n E s)) ∂clockLaw

/-- `E_u[∫_0^t r(λ_s) ds]`, the expected integrated revenue rate over `[0, t]`. -/
noncomputable def expectedRevenueRate (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ E, (∫⁻ s in Ioc 0 t, ENNReal.ofReal (M.r (u.intensityAt n E s))) ∂clockLaw

/-- The augmented functional of eq. (15),
`J_u(n, t, μ) = E_u[∫_0^t (r(λ_s) − μ λ_s) ds] + n μ`, written as
`E_u[∫ r(λ_s) ds] − μ E_u[∫ λ_s ds] + n μ`. Both expectations are finite (they are at most
`t r*` and `n`); the statements that use this functional assert that finiteness. -/
noncomputable def augmentedValue (n : ℕ) (t μ : ℝ) : ℝ :=
  (u.expectedRevenueRate n t).toReal - μ * (u.expectedCumIntensity n t).toReal + n * μ

end Policy

open Classical in
/-- The **constant-intensity policy** at rate `c` (fixed price `p(c)` for the whole horizon,
until stock runs out). If `c ∉ Λ` it is the null-price policy (rate `0`); every use below has
`c ∈ Λ`. -/
noncomputable def constPolicy (M : Model) (c : ℝ) : Policy M where
  φ := fun _ _ _ => if c ∈ M.Λ then c else 0
  measurable := fun _ => measurable_const
  mem := fun _ _ _ => by
    split_ifs with h
    · exact h
    · exact M.zero_mem
  locallyIntegrable := fun _ _ a b => by
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [Real.volume_Ioc])

/-- `J*(n, t) = sup_{u ∈ 𝒰} J_u(n, t)`, eq. (7): the optimal expected revenue. -/
noncomputable def optValue (M : Model) (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ u : Policy M, u.expectedRevenue n t

/-- `J^FP(n, t)` (§3.3, p. 1007): the expected revenue of the **fixed-price heuristic**, which
charges `p^D = p(λ^D)` with `λ^D = min{λ*, n/t}` for the whole horizon. For `t > 0` the rate
`λ^D` lies in `Λ` (it is in `[0, λ*]`; if `n/t` exceeds every allowable rate then `λ^D = λ*`). -/
noncomputable def fpValue (M : Model) (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  (constPolicy M (min M.lstar ((n : ℝ) / t))).expectedRevenue n t

/-- `J^OFP(n, t)` (§3.3, p. 1007): the expected revenue of the **optimal fixed-price heuristic**,
the best constant price, i.e. the supremum over all allowable constant rates `c ∈ Λ` (the null
price, rate `0`, included). -/
noncomputable def ofpValue (M : Model) (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ c ∈ M.Λ, (constPolicy M c).expectedRevenue n t

end GVRPricing.FixedPrice


