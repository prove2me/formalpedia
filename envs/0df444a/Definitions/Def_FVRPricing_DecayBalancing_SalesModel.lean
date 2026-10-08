-- Prove2me | Definitions.Def_FVRPricing_DecayBalancing_SalesModel
-- name    : FVRPricing_DecayBalancing_SalesModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:24.216589+00:00
-- url     : https://prove2.me/theorems/a1481b8d-57af-443a-9d77-2ecfea2b0b5d
-- title:
--   Bayesian sales process with a Gamma prior, $J^\pi$, $J^*$, the known-rate values $J^\pi_\lambda$, $J^*_\lambda$, and Assumption 2
-- statement:
--   **Model** (§2, pp. 5–7, with a single Gamma prior as in §6, p. 18). Customers arrive as a Poisson process of rate $\lambda$; a customer facing price $p$ buys one unit with probability $\bar F(p)$. The vendor starts with $x$ units and a $\mathrm{Gamma}(a,b)$ prior on $\lambda$ (density $b^a\lambda^{a-1}e^{-\lambda b}/\Gamma(a)$: shape $a$, **rate** $b$, mean $\mu = a/b$). The posterior after $n_t$ sales is $\mathrm{Gamma}(a_t,b_t)$ with $a_t = a + n_t$ and $b_t = b + \int_0^t \bar F(p_s)\,ds$. A **policy** is a map $\pi(x,a,b)\ge 0$, measurable in $(a,b)$ for each $x$; the price at time $t$ is $p_t = \pi(x_t,a_t,b_t)$.
--
--   **Construction of the sales process (the b-clock).** Given $\lambda$, the sales intensity is $\lambda\bar F(p_t)$ and $db_t/dt = \bar F(p_t)$, so measured on the $b$-scale sales form a Poisson process of rate $\lambda$, whatever the policy. Draw $\lambda\sim\mathrm{Gamma}(a,b)$ and independent clocks $E_1,\dots,E_x\sim\mathrm{Exp}(1)$, set $B_0 = b$, $B_{j+1} = B_j + E_{j+1}/\lambda$ (the $b$-value at the $(j+1)$-st sale). Between sales $j$ and $j+1$ the state is $(x-j, a+j, \beta)$, $\beta\in(B_j,B_{j+1}]$, and this stage lasts real time
--   $$D_j = \int_{B_j}^{B_{j+1}} \frac{d\beta}{\bar F(\pi(x-j,a+j,\beta))}\in[0,\infty].$$
--   The $(j+1)$-st sale happens at $T_{j+1} = D_0+\dots+D_j$ at the price $\pi(x-j,a+j,B_{j+1})$ in force just before it.
--
--   **Values.** For a discount rate $\alpha$ the path revenue is $\sum_{j<x} e^{-\alpha T_{j+1}}\,\pi(x-j,a+j,B_{j+1})$ (a sale at $T=\infty$ contributes $0$; with $\lambda\le 0$ there are no sales). More generally the dynamics may be driven by one policy $\pi_{\rm dyn}$ while the payment at each sale is the price of another policy $\pi_{\rm pay}$ in the pre-sale state. Then
--   $$J^\pi(x,a,b) = E\Big[\sum_{k:\,t_k\le\tau_0} e^{-\alpha t_k} p_{t_k-}\Big],\qquad J^*(x,a,b) = \sup_{\pi\in\Pi} J^\pi(x,a,b),$$
--   with values in $[0,\infty]$. With a **known** rate $\lambda$ and a policy $\pi:\mathbb N\to\mathbb R_+$ of the inventory only, the same construction (no prior) gives $J^\pi_\lambda(x)$ and $J^*_\lambda(x) = \sup_\pi J^\pi_\lambda(x)$ (§2, p. 6).
--
--   **Assumption 2** (p. 9): for every $x\in\mathbb N$, $J^*_\lambda(x)$ is finite and a differentiable function of $\lambda$ on $\mathbb R_+$.
--
--   **Formalization Note** The revenue is the sum over sales (first display of p. 6) rather than the compensated integral $E\int_0^{\tau_0} e^{-\alpha t}p_t\lambda\bar F(p_t)\,dt$; p. 6 states that the two are equal. The paper's state also carries mixture weights $w$, trivial for one Gamma prior. Policies take values in $\mathbb R_+$, and the value at $x=0$ (the paper's convention $\pi(0,\cdot)=\infty$) is never used. Expectations are lower Lebesgue integrals in $[0,\infty]$ and suprema are taken in $[0,\infty]$, so no junk value of a real supremum or of a non-integrable expectation arises. The guard "no sales when $\lambda\le 0$" concerns a null event of the Gamma prior and is the correct convention for a known rate $\lambda = 0$.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), pp. 5–7, §2 (model, J^π_λ, J*_λ, J^π, J*); p. 9, Assumption 2; p. 18, §6 (single Gamma prior)

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_ReservationLaw

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

/-- The unit-rate exponential law is a probability measure (needed for the product of clocks). -/
instance instIsProbabilityMeasureExpOne : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- Law of the `x` i.i.d. `Exp(1)` clocks `E₁, …, E_x` driving the sales in the b-clock. -/
noncomputable def clockLaw (x : ℕ) : Measure (Fin x → ℝ) :=
  Measure.pi (fun _ : Fin x => expMeasure 1)

/-- b-value at the `j`-th sale: `B₀ = b`, `B_{j+1} = B_j + E_{j+1}/λ`. -/
noncomputable def bClock (b lam : ℝ) {x : ℕ} (e : Fin x → ℝ) (j : ℕ) : ℝ :=
  b + (∑ i ∈ Finset.univ.filter (fun i : Fin x => (i : ℕ) < j), e i) / lam

/-- Real-time length of stage `j` (between sales `j` and `j+1`), in which the state is
`(x − j, a + j, β)` with `β ∈ (B_j, B_{j+1}]` and `db/dt = F̄(π(x − j, a + j, b))`:
`D_j = ∫_{B_j}^{B_{j+1}} dβ / F̄(π(x − j, a + j, β)) ∈ [0, ∞]`. -/
noncomputable def stageDuration (f : ℝ → ℝ) (πdyn : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b lam : ℝ)
    (e : Fin x → ℝ) (j : ℕ) : ENNReal :=
  ∫⁻ β in Set.Ioc (bClock b lam e j) (bClock b lam e (j + 1)),
    (ENNReal.ofReal (Fbar f (πdyn (x - j) (a + j) β)))⁻¹

/-- Real time of the `k`-th sale, `T_k = D₀ + ⋯ + D_{k−1}` (possibly `∞`). -/
noncomputable def saleTime (f : ℝ → ℝ) (πdyn : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b lam : ℝ)
    (e : Fin x → ℝ) (k : ℕ) : ENNReal :=
  ∑ j ∈ Finset.range k, stageDuration f πdyn x a b lam e j

/-- Discount factor `e^{−αT}`, equal to `0` when `T = ∞` (the sale never happens). -/
noncomputable def disc (α : ℝ) (T : ENNReal) : ENNReal :=
  if T = ⊤ then 0 else ENNReal.ofReal (Real.exp (-(α * T.toReal)))

/-- Discounted revenue of one sample path, `Σ_k e^{−α t_k} p_{t_k−}`: the dynamics are driven by the
policy `πdyn`, and at each sale the vendor is paid the price `πpay` would post in the pre-sale state.
With `λ ≤ 0` there are no sales. -/
noncomputable def pathRevenue (f : ℝ → ℝ) (α : ℝ) (πdyn πpay : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b lam : ℝ)
    (e : Fin x → ℝ) : ENNReal :=
  if lam ≤ 0 then 0 else
    ∑ j : Fin x, disc α (saleTime f πdyn x a b lam e ((j : ℕ) + 1)) *
      ENNReal.ofReal (πpay (x - j) (a + j) (bClock b lam e ((j : ℕ) + 1)))

/-- Admissible Bayesian policies `π : S → ℝ₊`, `π(x, a, b)`: measurable in `(a, b)` for each `x`
and non-negative. The value at `x = 0` is never used. -/
def IsPolicy (π : ℕ → ℝ → ℝ → ℝ) : Prop :=
  (∀ n : ℕ, Measurable (fun q : ℝ × ℝ => π n q.1 q.2)) ∧ ∀ (n : ℕ) (a b : ℝ), 0 ≤ π n a b

/-- `J^π(x, a, b)`: expected discounted revenue of policy `π` from state `(x, a, b)`, with
`λ ~ Gamma(a, b)` (shape `a`, rate `b`) and the sales process built in the b-clock. -/
noncomputable def Jpi (f : ℝ → ℝ) (α : ℝ) (π : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b : ℝ) : ENNReal :=
  ∫⁻ lam, ∫⁻ e, pathRevenue f α π π x a b lam e ∂(clockLaw x) ∂(gammaMeasure a b)

/-- `J*(x, a, b) = sup_{π ∈ Π} J^π(x, a, b)`. -/
noncomputable def Jstar (f : ℝ → ℝ) (α : ℝ) (x : ℕ) (a b : ℝ) : ENNReal :=
  ⨆ (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π), Jpi f α π x a b

/-- `J^π_λ(x)`: known arrival rate `λ`, policy `π : ℕ → ℝ` depending on the inventory only. -/
noncomputable def JpiKnown (f : ℝ → ℝ) (α lam : ℝ) (π : ℕ → ℝ) (x : ℕ) : ENNReal :=
  ∫⁻ e, pathRevenue f α (fun n _ _ => π n) (fun n _ _ => π n) x 0 0 lam e ∂(clockLaw x)

/-- `J*_λ(x) = sup_{π ∈ Π_λ} J^π_λ(x)` over non-negative price functions of the inventory. -/
noncomputable def JstarKnown (f : ℝ → ℝ) (α lam : ℝ) (x : ℕ) : ENNReal :=
  ⨆ (π : ℕ → ℝ) (_ : ∀ n, 0 ≤ π n), JpiKnown f α lam π x

/-- Assumption 2 (p. 9): for every `x`, `J*_λ(x)` is a (finite, real-valued) differentiable function of
`λ` on `ℝ₊`. -/
def Assumption2 (f : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ x : ℕ, (∀ lam : ℝ, 0 ≤ lam → JstarKnown f α lam x ≠ ⊤) ∧
    DifferentiableOn ℝ (fun lam => (JstarKnown f α lam x).toReal) (Set.Ici 0)

end FVRPricing.DecayBalancing


