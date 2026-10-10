-- Prove2me | Definitions.Def_RiskSensMFG_Existence_FixedPoint
-- name    : RiskSensMFG_Existence_FixedPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:28.724712+00:00
-- url     : https://prove2.me/theorems/82387121-a386-434a-a9ea-de8ec4d53b42
-- title:
--   §4.2, pp. 14–16 — the sets $\mathcal P^t_w$, $\Xi$, the value functions $J^\nu_{*,t}$ and the set-valued map $\Gamma=C\cap B$
-- statement:
--   Let $\alpha\ge0$ and $w:\mathsf X\to[1,\infty)$ satisfy parts (d) and (e) of Assumption 1: $w$ is a continuous moment function, $\int w(y)\,p(dy|x,a,\mu)\le\alpha w(x)$ for all $(x,a,\mu)$, and $M:=\int w\,d\mu_0<\infty$. For $\nu\in\mathcal P(\mathsf X\times\mathsf A)$ write $\nu_1$ for its marginal on $\mathsf X$.
--
--   1. For $t\ge0$,
--   $$\mathcal P^t_w(\mathsf X)=\{\mu\in\mathcal P(\mathsf X):\mu(w)\le\alpha^tM\},\qquad \mathcal P^t_w(\mathsf X\times\mathsf A)=\{\nu\in\mathcal P(\mathsf X\times\mathsf A):\nu_1\in\mathcal P^t_w(\mathsf X)\},$$
--   and $\Xi=\prod_{t\ge0}\mathcal P^t_w(\mathsf X\times\mathsf A)$, with the product of the weak topologies.
--   2. For a state–action flow $\nu=(\nu_t)_{t\ge0}$, $J^\nu_{*,t}(\cdot,\lambda\beta^t)$ is the infinite-horizon optimal value function at time $t$ of the nonhomogeneous MDP with costs $c(x,a,\nu_{s,1})$ and kernels $p(\cdot|x,a,\nu_{s,1})$, and $J^\nu_{*,t}(\cdot,\lambda\beta^t,k)$ the one with finite horizon $k$.
--   3. $\Gamma(\nu)=C(\nu)\cap B(\nu)$, where
--   $$C(\nu)=\Big\{\nu':\ \nu'_{0,1}=\mu_0,\ \nu'_{t+1,1}(\cdot)=\int_{\mathsf X\times\mathsf A}p(\cdot\,|\,x,a,\nu_{t,1})\,\nu_t(dx,da)\ \forall t\Big\},$$
--   $$B(\nu)=\Big\{\nu':\ \forall t\ge0,\ \nu'_t\Big(\Big\{(x,a):e^{\lambda\beta^tc(x,a,\nu_{t,1})}\int_{\mathsf X}J^\nu_{*,t+1}(y,\lambda\beta^{t+1})\,p(dy|x,a,\nu_{t,1})=\big[T^\nu_tJ^\nu_{*,t+1}(\cdot,\lambda\beta^{t+1})\big](x)\Big\}\Big)=1\Big\},$$
--   with $[T^\nu_tu](x)=\inf_{a\in\mathsf A}\big[e^{\lambda\beta^tc(x,a,\nu_{t,1})}\int u(y)\,p(dy|x,a,\nu_{t,1})\big]$.
--
--   $C(\nu)$ encodes consistency of the mean-field term with the state distribution of a generic agent, and $B(\nu)$ encodes optimality of the policy obtained by disintegrating the state–action flow. Mean-field equilibria come from fixed points $\nu\in\Gamma(\nu)$.
--
--   **Formalization Note** As printed, the right-hand side of the recursion in $C(\nu)$ uses $\nu_t$, not $\nu'_t$. $M$ is the real number $\int w\,d\mu_0$ (finite by (e)). $\Xi$ is a subset of $\mathcal P(\mathsf X\times\mathsf A)^{\mathbb N}$, which carries the product topology. The set in $B(\nu)$ is measured by the outer measure of $\nu'_t$; under Assumption 1 it is closed, because the functions involved are continuous.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, §4.2, pp. 14–16: P^t_w, Ξ (p. 14), T^ν_t, J^ν_{*,t}, C(ν), B(ν), Γ (pp. 15–16); finite-horizon J^ν_{*,t}(·, λβ^t, k) (proof of Proposition 5, p. 19)

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model
import Definitions.Def_RiskSensMFG_Existence_NonhomMDP

open MeasureTheory ProbabilityTheory

namespace RiskSensMFG.Existence

variable {X A : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [TopologicalSpace A] [OpensMeasurableSpace A]
  [SecondCountableTopology X] [SecondCountableTopology A]

/-- The marginal `ν₁ ∈ P(X)` on `X` of `ν ∈ P(X × A)`. -/
noncomputable def marg (ν : PM (X × A)) : PM X :=
  ProbabilityMeasure.map (show ProbabilityMeasure (X × A) from ν) measurable_fst.aemeasurable

/-- Parts (d) and (e) of Assumption 1 for a given constant `α` and function `w`: `α ≥ 0`, `w` is a
continuous moment function with values in `[1, ∞)`, `∫ w(y) p(dy | x, a, μ) ≤ α w(x)` for all
`(x, a, μ)` (3), and `∫ w dμ₀ < ∞`. -/
def MomentCondition (M : Model X A) (α : ℝ) (w : X → ℝ) : Prop :=
  0 ≤ α ∧ Continuous w ∧ (∀ x, 1 ≤ w x) ∧ IsMomentFunction w ∧
    (∀ x a μ, ∫⁻ y, ENNReal.ofReal (w y) ∂(M.p (x, a, μ)) ≤ ENNReal.ofReal (α * w x)) ∧
    ∫⁻ x, ENNReal.ofReal (w x) ∂(M.μ₀ : Measure X) < ⊤

/-- `M := ∫ w dμ₀` (Assumption 1-(e)). -/
noncomputable def Mw (M : Model X A) (w : X → ℝ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (w x) ∂(M.μ₀ : Measure X)).toReal

/-- `P^t_w(X) = {μ ∈ P(X) : μ(w) ≤ αᵗ M}` (p. 14). -/
def Pw (M : Model X A) (α : ℝ) (w : X → ℝ) (t : ℕ) : Set (PM X) :=
  {μ | ∫⁻ x, ENNReal.ofReal (w x) ∂(ProbabilityMeasure.toMeasure μ) ≤
    ENNReal.ofReal (α ^ t * Mw M w)}

/-- `Ξ = ∏_{t ≥ 0} P^t_w(X × A)`, where `P^t_w(X × A) = {ν ∈ P(X × A) : ν₁ ∈ P^t_w(X)}` (p. 14). -/
def Xi (M : Model X A) (α : ℝ) (w : X → ℝ) : Set (ℕ → PM (X × A)) :=
  {ν | ∀ t, marg (ν t) ∈ Pw M α w t}

/-- `J^ν_{*,t}(x, λβᵗ)`: the infinite-horizon optimal value at time `t` of the nonhomogeneous MDP
with costs `c(x, a, ν_{s,1})` and kernels `p(· | x, a, ν_{s,1})` (p. 15). -/
noncomputable def Copt (M : Model X A) (ν : ℕ → PM (X × A)) (t : ℕ) (x : X) : ℝ :=
  JinfOpt M (fun s => marg (ν s)) t x (M.lam * M.β ^ t)

/-- `J^ν_{*,t}(x, λβᵗ, k)`: the same optimal value with finite horizon `k` (proof of Proposition 5,
p. 19). -/
noncomputable def CoptFin (M : Model X A) (ν : ℕ → PM (X × A)) (t k : ℕ) (x : X) : ℝ :=
  JfinOpt M (fun s => marg (ν s)) t k x (M.lam * M.β ^ t)

/-- `C(ν)` (p. 15): `ν'_{0,1} = μ₀` and `ν'_{t+1,1}(·) = ∫ p(· | x, a, ν_{t,1}) ν_t(dx, da)`. -/
def Cset (M : Model X A) (ν : ℕ → PM (X × A)) : Set (ℕ → PM (X × A)) :=
  {ν' | ProbabilityMeasure.toMeasure (marg (ν' 0)) = (M.μ₀ : Measure X) ∧
    ∀ t, ProbabilityMeasure.toMeasure (marg (ν' (t + 1))) =
      (M.p.comap (fun xa : X × A => (xa.1, xa.2, marg (ν t))) (by fun_prop)) ∘ₘ
        ProbabilityMeasure.toMeasure (ν t)}

/-- `B(ν)` (pp. 15–16): for every `t`, `ν'_t`-almost every `(x, a)` attains the infimum in
`[T^ν_t J^ν_{*,t+1}(·, λβ^{t+1})](x)`. -/
def Bset (M : Model X A) (ν : ℕ → PM (X × A)) : Set (ℕ → PM (X × A)) :=
  {ν' | ∀ t, ProbabilityMeasure.toMeasure (ν' t)
    {xa : X × A | Real.exp (M.lam * M.β ^ t * M.c (xa.1, xa.2, marg (ν t))) *
        ∫ y, Copt M ν (t + 1) y ∂(M.p (xa.1, xa.2, marg (ν t))) =
      T M (fun s => marg (ν s)) t (Copt M ν (t + 1)) xa.1} = 1}

/-- `Γ(ν) = C(ν) ∩ B(ν)` (p. 15). -/
def Gamma (M : Model X A) (ν : ℕ → PM (X × A)) : Set (ℕ → PM (X × A)) :=
  Cset M ν ∩ Bset M ν

end RiskSensMFG.Existence


