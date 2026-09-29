-- Prove2me | Definitions.Def_TamingMonster_Regret_Analysis
-- name    : TamingMonster_Regret_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T08:24:27.462627+00:00
-- url     : https://prove2.me/theorems/38dc7391-a73d-4db6-b393-e8f0d97b5899
-- title:
--   Variance quantities $V$, $\widehat V_m$, $\mathcal V_t$, constants $m_0,t_0,\rho,\theta_1,\theta_2,c_0,C_0$, and the event $\mathcal E$
-- statement:
--   This file defines the quantities of the regret analysis of ILOVETOCONBANDITS (Appendices B and C of Agarwal et al. 2014).
--
--   1. For weights $P$ on $\Pi$, a policy $\pi$ and $\mu$, with $\mathcal D_X$ the context marginal of $\mathcal D$ (Eqs. (8), (9)):
--   $$V(P,\pi,\mu)=\mathbb E_{x\sim\mathcal D_X}\Bigl[\frac1{P^\mu(\pi(x)\mid x)}\Bigr],\qquad \widehat V_m(P,\pi,\mu)=\frac1{\tau_m}\sum_{i=1}^{\tau_m}\frac1{P^\mu(\pi(x_i)\mid x_i)}.$$
--   2. $\mathcal V_t(\pi)=\max_{0\le m\le m(t)-1}V(\widetilde Q_m,\pi,\mu_m)$ for the completed weights of the run (Eq. (11)).
--   3. $m_0=\min\{m\ge1:d_{\tau_m}/\tau_m\le 1/(4K)\}$, $t_0=\min\{t\ge1:d_t/t\le1/(4K)\}$, $\rho=\sup_{m\ge m_0}\sqrt{\tau_m/\tau_{m-1}}$, $\theta_1=94.1$, $\theta_2=\psi/6.4$, $c_0=4\rho(1+\theta_1)$ and $C_0=4\psi+c_0$.
--   4. The event $\mathcal E$ (§C.2) holds when
--   $$V(P,\pi,\mu_m)\le 6.4\,\widehat V_m(P,\pi,\mu_m)+81.3K\qquad(13)$$
--   for every probability distribution $P$ over $\Pi$, every $\pi\in\Pi$ and every $m\ge1$ with $\tau_m\ge 4Kd_{\tau_m}$; and, for every $\pi\in\Pi$, every epoch $m\ge1$ and every round $t$ of epoch $m$,
--   $$|\widehat{\mathcal R}_t(\pi)-\mathcal R(\pi)|\le\begin{cases}\max\Bigl\{\sqrt{\tfrac{3\mathcal V_t(\pi)d_t}{t}},\ \tfrac{2\mathcal V_t(\pi)d_t}{t}\Bigr\}&m\le m_0,\\[1mm]\mathcal V_t(\pi)\mu_{m-1}+\tfrac{d_t}{t\mu_{m-1}}&m>m_0.\end{cases}\qquad(14)$$
--
--   Lemmas 12–14 are deterministic consequences of $\mathcal E$, and the paper shows $\Pr(\mathcal E)\ge1-\delta/2$ from Lemmas 10 and 11.
--
--   **Formalization Note** The paper's $\mathbb N$ is $\{1,2,\dots\}$, so $m_0$ and $t_0$ are minima over positive integers. $\rho$ is a real supremum over the nonempty set $\{m\ge m_0\}$; it is at most $\sqrt2$ when $m_0\ge2$ and $\tau_{m+1}\le2\tau_m$ for $m\ge1$, which every statement using $c_0$ assumes. Eq. (14)'s first case prints $\mathcal V_t$ without $(\pi)$; it is read as $\mathcal V_t(\pi)$. The constants $6.4$, $81.3$, $94.1$ are exact rationals. $\mathcal V_t$ is set to $0$ at $t=0$, where it is never used.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 14 (Eqs. (8)-(9)), p. 16 (Eq. (11)), p. 17 (§C.1, §C.2, Eqs. (13)-(14)), p. 18 (t_0, Lemma 13), p. 21 (Lemma 17, C_0)

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm

namespace TamingMonster.Regret

open MeasureTheory

variable {X : Type*} {K : ℕ}

/-- `V(P, π, μ) := E_{x∼D_X}[1/P^μ(π(x)|x)]`, Eq. (8), p. 14, for weights `P` on `Π`, a policy
`π` and `μ`; `ν` is the context distribution `D_X`. -/
noncomputable def Vpop [MeasurableSpace X] (ν : Measure X) (Pi : Finset (X → Fin K))
    (P : Pi → ℝ) (π : X → Fin K) (μ : ℝ) : ℝ :=
  ∫ x, 1 / smoothProj Pi P μ x (π x) ∂ν

/-- `V̂_m(P, π, μ) := Ê_{x∼H_{τ_m}}[1/P^μ(π(x)|x)]`, Eq. (9), p. 14, written for the contexts
`xs 1, …, xs n` of the first `n = τ_m` rounds: `(1/n) ∑_{i=1}^{n} 1/P^μ(π(x_i)|x_i)`. -/
noncomputable def Vhat (Pi : Finset (X → Fin K)) (P : Pi → ℝ) (π : X → Fin K) (μ : ℝ)
    (xs : ℕ → X) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.Icc 1 n, 1 / smoothProj Pi P μ (xs i) (π (xs i))) / n

/-- `𝒱_t(π) := max_{0 ≤ m ≤ m(t)−1} V(Q̃_m, π, μ_m)`, Eq. (11), p. 16, for the completed
weights `Q̃_m` of the run of ILOVETOCONBANDITS on `ω`; `ν = D_X`. Defined for `t ≥ 1`
(then `m(t) ≥ 1`); the value `0` for `t = 0` is never used. -/
noncomputable def AlgoParams.calV [MeasurableSpace X] [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (ν : Measure X) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ)
    (π : X → Fin K) : ℝ :=
  if h : 0 < epochOf A.τ t then
    (Finset.range (epochOf A.τ t)).sup' ⟨0, Finset.mem_range.mpr h⟩
      (fun m => Vpop ν A.Pi (A.Qtilde Z U ω m) π (muM A.Pi A.δ A.τ m))
  else 0

/-- `m₀ := min{m ∈ ℕ : d_{τ_m}/τ_m ≤ 1/(4K)}` (§C.1, p. 17), with `ℕ = {1, 2, …}`. -/
noncomputable def m0 (Pi : Finset (X → Fin K)) (δ : ℝ) (τ : ℕ → ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ dT Pi δ (τ m) / (τ m : ℝ) ≤ 1 / (4 * (K : ℝ))}

/-- `t₀ := min{t ∈ ℕ : d_t/t ≤ 1/(4K)}` (§C.3, p. 18), with `ℕ = {1, 2, …}`. -/
noncomputable def t0 (Pi : Finset (X → Fin K)) (δ : ℝ) : ℕ :=
  sInf {t : ℕ | 1 ≤ t ∧ dT Pi δ t / (t : ℝ) ≤ 1 / (4 * (K : ℝ))}

/-- `ρ := sup_{m ≥ m₀} √(τ_m/τ_{m−1})` (§C.1, p. 17), as a real supremum over the nonempty set
`{m : m ≥ m₀}` (bounded by `√2` when `m₀ ≥ 2` and `τ_{m+1} ≤ 2τ_m` for `m ≥ 1`). -/
noncomputable def rho (Pi : Finset (X → Fin K)) (δ : ℝ) (τ : ℕ → ℕ) : ℝ :=
  ⨆ m : {m : ℕ // m0 Pi δ τ ≤ m}, Real.sqrt ((τ m.1 : ℝ) / (τ (m.1 - 1) : ℝ))

/-- `θ₁ := 94.1` (§C.2, p. 17). -/
noncomputable def theta1 : ℝ := 941 / 10

/-- `θ₂ := ψ/6.4` (§C.2, p. 17). -/
noncomputable def theta2 : ℝ := psi / (64 / 10)

/-- `c₀ := 4ρ(1 + θ₁)` (Lemma 13, p. 18). -/
noncomputable def c0 (Pi : Finset (X → Fin K)) (δ : ℝ) (τ : ℕ → ℕ) : ℝ :=
  4 * rho Pi δ τ * (1 + theta1)

/-- `C₀ := 4ψ + c₀` (Lemma 17, p. 21). -/
noncomputable def C0 (Pi : Finset (X → Fin K)) (δ : ℝ) (τ : ℕ → ℕ) : ℝ :=
  4 * psi + c0 Pi δ τ

/-- The event `ℰ` of §C.2, p. 17, for the run of ILOVETOCONBANDITS with parameters `A` on the
data `Z` (contexts/rewards) and `U` (action-draw randomness), `D` the distribution of `(x, r)` and
`D_X` its context marginal:
(13) `V(P, π, μ_m) ≤ 6.4 V̂_m(P, π, μ_m) + 81.3K` for all probability distributions `P` over `Π`,
all `π ∈ Π` and all `m ∈ ℕ` with `τ_m ≥ 4K d_{τ_m}`; and
(14) for all `π ∈ Π`, all epochs `m ∈ ℕ` and all rounds `t` in epoch `m`
(`τ_{m−1} < t ≤ τ_m`), `|R̂_t(π) − R(π)|` is at most
`max{√(3𝒱_t(π)d_t/t), 2𝒱_t(π)d_t/t}` if `m ≤ m₀`, and `𝒱_t(π)μ_{m−1} + d_t/(tμ_{m−1})` if
`m > m₀`. -/
def AlgoParams.goodEvent [MeasurableSpace X] [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (D : Measure (X × (Fin K → ℝ))) (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) : Set Ω :=
  {ω |
    (∀ P : A.Pi → ℝ, (∀ π, 0 ≤ P π) → ∑ π, P π = 1 → ∀ π : A.Pi, ∀ m : ℕ, 1 ≤ m →
      4 * (K : ℝ) * dT A.Pi A.δ (A.τ m) ≤ (A.τ m : ℝ) →
      Vpop (D.map Prod.fst) A.Pi P (π : X → Fin K) (muM A.Pi A.δ A.τ m) ≤
        64 / 10 * Vhat A.Pi P (π : X → Fin K) (muM A.Pi A.δ A.τ m) (fun i => (Z i ω).1) (A.τ m)
          + 813 / 10 * (K : ℝ)) ∧
    (∀ π : A.Pi, ∀ m : ℕ, 1 ≤ m → ∀ t : ℕ, A.τ (m - 1) < t → t ≤ A.τ m →
      |ipsEst (A.history Z U ω t) (π : X → Fin K) - expReward D (π : X → Fin K)| ≤
        if m ≤ m0 A.Pi A.δ A.τ then
          max (Real.sqrt (3 * A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K)
                * dT A.Pi A.δ t / t))
            (2 * A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) * dT A.Pi A.δ t / t)
        else
          A.calV (D.map Prod.fst) Z U ω t (π : X → Fin K) * muM A.Pi A.δ A.τ (m - 1)
            + dT A.Pi A.δ t / (t * muM A.Pi A.δ A.τ (m - 1)))}

end TamingMonster.Regret


