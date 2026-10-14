-- Prove2me | Definitions.Def_UnknownLoads_Refined_Load
-- name    : UnknownLoads_Refined_Load
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:32.80334+00:00
-- url     : https://prove2.me/theorems/d22770cf-dde5-4192-8ebb-43fed38d0692
-- title:
--   Standing data of §3 (exponential service), the fluid total mass u of (4), and (m, Δ)-bounded offered load (Definition 1)
-- statement:
--   This module fixes the deterministic data of the exponential-service model of §3 and Definition 1.
--
--   1. **Standing data.** A horizon $T>0$; an arrival-rate function $\lambda:[0,T]\to[0,\infty)$ that is bounded, $\lambda(t)\le C$, and measurable (new tasks arrive at rate $n\lambda(t)$ in the system with $n$ server pools); a service rate $\mu>0$; and an integral parameter $\Delta\ge1$. The offered load per server pool is $\rho(t):=\lambda(t)/\mu$.
--   2. **Occupancy space.** $Q:=\{q\in[0,1]^{\mathbb N}: q(i+1)\le q(i)\le q(0)=1\text{ for all }i\ge0\}$; $q(i)$ is the fraction of server pools with at least $i$ tasks.
--   3. **Fluid total mass** (4). For a limiting initial occupancy state $q(0)$,
--   $$
--   u(0):=\sum_{i=1}^\infty q(0,i),\qquad u(t):=u(0)e^{-\mu t}+\int_0^t\rho(s)\mu e^{-\mu(t-s)}\,ds .
--   $$
--   4. **Definition 1.** For an integer $m\ge0$ and an interval $[a,b]\subset[0,T]$, let $\rho_{\min}:=\inf_{t\in[a,b]}\rho(t)$ and $\rho_{\max}:=\sup_{t\in[a,b]}\rho(t)$, and
--   $$
--   \sigma(a,b,m,\Delta):=\begin{cases}\frac1\mu\log\Big(\frac{\rho_{\min}}{\rho_{\min}-m\Delta}\Big)+\frac1\mu\Big[\log\Big(\frac{u(a)-\rho_{\max}}{(m+1)\Delta-\rho_{\max}}\Big)\Big]^+ & \text{if } u(a)>\rho_{\max},\\ \frac1\mu\log\Big(\frac{\rho_{\min}}{\rho_{\min}-m\Delta}\Big) & \text{if } u(a)\le\rho_{\max}.\end{cases}
--   $$
--   The offered load is **$(m,\Delta)$-bounded on $[a,b]$** if $m\Delta<\rho_{\min}\le\rho_{\max}<(m+1)\Delta$ and $b-a>\sigma(a,b,m,\Delta)$. The constant $\sigma_{\mathrm{bd}}(a,b,m,\Delta)$ of Proposition 10 is the second summand alone in the first case and $0$ in the second.
--   5. **Lipschitz sets** (p. 47). $L^\varepsilon_M$ is the set of real càdlàg functions $x$ on $[0,T]$ with $x(0)=0$ and $|x(t)-x(s)|\le M|t-s|+\varepsilon$ for all $s,t\in[0,T]$; $L_M:=L^0_M$.
--
--   These objects enter the statement of Theorem 2 and of every milestone of the mission.
--
--   **Formalization Note** $\lambda$ is a function on $\mathbb R$ that is required to be measurable (the paper uses $\int\lambda$ without saying so) and nonnegative and bounded on $[0,T]$; its values outside $[0,T]$ are never used. $u(0)$ is a real series; it is applied only to the almost-sure limit $q(0)$ of the initial conditions, which lies in $Q$ and vanishes beyond the constant $B$ of §3, so the series is a finite sum. $\rho_{\min}$ and $\rho_{\max}$ are `sInf`/`sSup` of $\rho([a,b])$, a nonempty bounded set under the definition's hypotheses; the logarithms are evaluated only at positive arguments there. $[x]^+$ is `max x 0`. "Càdlàg on $[0,T]$" means right-continuous at each $t\in[0,T)$ with a finite left limit at each $t\in(0,T]$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 12–14, §3 and (4); p. 15, Definition 1; p. 30, Proposition 10 (σ_bd); p. 47 (L_M, L^ε_M)

import Mathlib

namespace UnknownLoads.Refined

open MeasureTheory Set Filter Topology

/-- A real function is càdlàg on `[0, T]`: right-continuous at every `t ∈ [0, T)` and with a
finite left limit at every `t ∈ (0, T]`. Values outside `[0, T]` play no role. -/
def IsCadlagOn (f : ℝ → ℝ) (T : ℝ) : Prop :=
  (∀ t ∈ Ico 0 T, ContinuousWithinAt f (Ici t) t) ∧
    ∀ t ∈ Ioc 0 T, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)

/-- `x ∈ L^ε_M` (p. 47): `x` is a real càdlàg function on `[0, T]` with `x(0) = 0` and
`|x(t) − x(s)| ≤ M|t − s| + ε` for all `s, t ∈ [0, T]`. With `ε = 0` this is `L_M`. -/
def LipSet (T M ε : ℝ) (x : ℝ → ℝ) : Prop :=
  IsCadlagOn x T ∧ x 0 = 0 ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |x t - x s| ≤ M * |t - s| + ε

/-- The occupancy space `Q = {q ∈ [0,1]^ℕ : q(i+1) ≤ q(i) ≤ q(0) = 1 for all i ≥ 0}`. -/
def OccupancySpace : Set (ℕ → ℝ) :=
  {q | q 0 = 1 ∧ (∀ i, 0 ≤ q i ∧ q i ≤ 1) ∧ ∀ i, q (i + 1) ≤ q i}

/-- The standing data of §3 for exponential service (`r = 1`): a horizon `T > 0`, a bounded,
nonnegative, measurable arrival-rate function `λ` on `[0, T]` (arrivals at rate `nλ(t)`), a service
rate `µ > 0` and an integral parameter `Δ ≥ 1`. -/
structure LoadData where
  T : ℝ
  T_pos : 0 < T
  lam : ℝ → ℝ
  lam_measurable : Measurable lam
  lam_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ lam t
  C : ℝ
  lam_le : ∀ t ∈ Icc 0 T, lam t ≤ C
  mu : ℝ
  mu_pos : 0 < mu
  Δ : ℕ
  one_le_Δ : 1 ≤ Δ

namespace LoadData

variable (D : LoadData)

/-- The offered load per server pool, `ρ(t) = λ(t)/µ`. -/
noncomputable def rho (t : ℝ) : ℝ := D.lam t / D.mu

/-- `∫₀ᵗ λ(s) ds`. -/
noncomputable def cumRate (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, D.lam s

/-- The fluid total mass `u` of (4): `u(0) = ∑_{i ≥ 1} q(0, i)` and
`u(t) = u(0) e^{-µt} + ∫₀ᵗ ρ(s) µ e^{-µ(t-s)} ds`, for the limiting initial occupancy `q0`.
(Applied to the limit of (2), which vanishes beyond `B`, so the sum is finite.) -/
noncomputable def fluidU (q0 : ℕ → ℝ) (t : ℝ) : ℝ :=
  (∑' i, q0 (i + 1)) * Real.exp (-D.mu * t) +
    ∫ s in (0 : ℝ)..t, D.rho s * D.mu * Real.exp (-D.mu * (t - s))

/-- `ρ_min = inf_{t ∈ [a,b]} ρ(t)`. -/
noncomputable def rhoMin (a b : ℝ) : ℝ := sInf (D.rho '' Icc a b)

/-- `ρ_max = sup_{t ∈ [a,b]} ρ(t)`. -/
noncomputable def rhoMax (a b : ℝ) : ℝ := sSup (D.rho '' Icc a b)

/-- The constant `σ(a, b, m, Δ)` of Definition 1 (`[x]⁺ = max x 0`). -/
noncomputable def sigma (q0 : ℕ → ℝ) (a b : ℝ) (m : ℕ) : ℝ :=
  if D.rhoMax a b < D.fluidU q0 a then
    1 / D.mu * Real.log (D.rhoMin a b / (D.rhoMin a b - m * D.Δ)) +
      1 / D.mu * max (Real.log ((D.fluidU q0 a - D.rhoMax a b) /
        ((m + 1) * D.Δ - D.rhoMax a b))) 0
  else
    1 / D.mu * Real.log (D.rhoMin a b / (D.rhoMin a b - m * D.Δ))

/-- The constant `σ_bd(a, b, m, Δ)` of Proposition 10. -/
noncomputable def sigmaBd (q0 : ℕ → ℝ) (a b : ℝ) (m : ℕ) : ℝ :=
  if D.rhoMax a b < D.fluidU q0 a then
    1 / D.mu * max (Real.log ((D.fluidU q0 a - D.rhoMax a b) /
        ((m + 1) * D.Δ - D.rhoMax a b))) 0
  else 0

/-- Definition 1: the offered load is `(m, Δ)`-bounded on `[a, b] ⊂ [0, T]`:
`mΔ < ρ_min ≤ ρ_max < (m+1)Δ` and `b - a > σ(a, b, m, Δ)`. -/
def IsBounded (q0 : ℕ → ℝ) (m : ℕ) (a b : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ b ∧ b ≤ D.T ∧
    (m : ℝ) * D.Δ < D.rhoMin a b ∧ D.rhoMax a b < ((m : ℝ) + 1) * D.Δ ∧
    D.sigma q0 a b m < b - a

end LoadData

end UnknownLoads.Refined


