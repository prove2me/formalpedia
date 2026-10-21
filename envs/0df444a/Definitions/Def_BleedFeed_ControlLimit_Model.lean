-- Prove2me | Definitions.Def_BleedFeed_ControlLimit_Model
-- name    : BleedFeed_ControlLimit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:48.350916+00:00
-- url     : https://prove2.me/theorems/8c76c11b-0f04-44c7-a50d-6407a0239dca
-- title:
--   §3, pp. 8–13 — bleed–feed MDP: biomass growth (1), rewards, stationary-phase risk, critical age, value function (2)–(3), Conditions (4)–(5), Assumption 1
-- statement:
--   This file sets up the finite-horizon Markov decision process of Koca, Martagan, Adan, Maillart and van Ravenstein for bleed–feed decisions in a batch fermentation (§3, pp. 8–13), together with Condition (4) (p. 14), Condition (5) and Assumption 1 (p. 15).
--
--   **Parameters.** An initial biomass $m_0>0$ and a period length $\tau>0$; bounds $0<\mu_\ell\le\mu_u$ of the set of cell growth rates $\mathcal M=[\mu_\ell,\mu_u]$; a maximum cultivation age $I\ge 1$ and a regulatory limit $N\ge 0$ on the number of bleed–feeds; a critical biomass $\tilde m\ge 0$ and a rate $\nu(m)$ of entering the stationary phase, with $\nu(m)=0$ for $m\le\tilde m$, $\nu$ strictly increasing on $[\tilde m,\infty)$ and $\nu(m)\tau\le 1$; and the law $G$ of the growth rate $M$ drawn after a bleed–feed, a probability measure carried by $\mathcal M$.
--
--   **States and primitives.** The state is $(i,\mu,n)$: cultivation age $i\in\{0,\dots,I\}$, growth rate $\mu\in\mathcal M$, bleed–feed count $n\in\{0,\dots,N\}$. The biomass, the reward of continuing and the probability of staying in the exponential growth phase are
--   $$
--   m_{i\mu}=m_0(1+\mu\tau)^i\quad(1),\qquad r_{i\mu}=m_{i+1,\mu}-m_{i\mu},\qquad p_{i\mu}=1-\nu(m_{i\mu})\tau .
--   $$
--   The **critical age** $\tilde\imath_\mu$ is the least age $i$ with $m_{i\mu}>\tilde m$.
--
--   **Optimality equations (2)–(3).** With $v(I,\mu,n)=0$, for $i<I$
--   $$
--   v(i,\mu,n)=\max\bigl\{\,C(i,\mu,n)\equiv r_{i\mu}+p_{i\mu}\,v(i+1,\mu,n),\;\; B(n)\equiv\mathbb E\bigl[C(0,M,n+1)\bigr]\,\bigr\},
--   $$
--   where $B(N)=0$, so that $v(i,\mu,N)=C(i,\mu,N)$. **Bleed–feed is optimal** in $(i,\mu,n)$ when $n<N$ and $C(i,\mu,n)\le B(n)$; **continuing is optimal** when $B(n)\le C(i,\mu,n)$. Ties make both optimal.
--
--   **Condition (4)** asks $\dfrac{r_{i\mu}-r_{i-1,\mu}}{r_{i\mu}}\le p_{i-1,\mu}-p_{i\mu}$ for all $\tilde\imath_\mu\le i<I$, $\mu\in\mathcal M$. **Condition (5)** asks $\dfrac{r_{i-1,\mu^+}-r_{i-1,\mu}}{r_{i\mu^+}}\le p_{i-1,\mu}-p_{i-1,\mu^+}$ for all $\tilde\imath_{\mu^+}<i<I$ and $\mu\le\mu^+$ in $\mathcal M$. **Assumption 1** asks that bleed–feed be optimal in every state $(I-1,\mu,n)$ with $\mu\in\mathcal M$, $n<N$.
--
--   These objects are shared by every statement of the mission: the structural results compare $C(i,\mu,n)$ with $B(n)$ as $i$, $\mu$ and $n$ vary.
--
--   **Formalization Note** The value function is computed by recursion: for a fixed bleed–feed value $b$, `W P b μ i` runs backward in the age ($0$ for $i\ge I$, else $\max\{r_{i\mu}+p_{i\mu}W(i+1),\,b\}$), and `Bk P k` is the bleed–feed value with $k$ bleed–feeds still permitted ($B(n)=$ `Bk P (N - n)`, an integral against $G$). Values at $n>N$ or $i>I$ are never used. Three conventions are added to the page, all disclosed: $\nu(\tilde m)=0$ with $\nu$ strictly increasing from $\tilde m$ on (so that "$p_{i\mu}=1$ for $i<\tilde\imath_\mu$ and $p_{i-1,\mu}>p_{i\mu}$ for $i\ge\tilde\imath_\mu$" holds); $\nu(m)\tau\le 1$, since $1-p_{i\mu}$ is a probability; and $\nu$ measurable, which makes $B(n)$ a genuine integral (it is implied by monotonicity). Condition (5) is stated on the range $\tilde\imath_{\mu^+}<i<I$: the page prints $\tilde\imath_{\mu^+}\le i<I$, under which (5) fails at $i=\tilde\imath_{\mu^+}\ge1$ for every $\mu<\mu^+$ (the right side is $p_{i-1,\mu}-1\le 0$, the left side positive), so every nondegenerate $\mathcal M$ would violate it; the proof of Proposition 3 (p. 34) uses (5) only on the corrected range. In Condition (4), $i-1$ is natural-number subtraction, so the clause at $i=0$ (where the page's index $-1$ is undefined) reads $0\le 0$.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f…6cfa43906), pp. 8–15, §3, eq. (1), optimality equations (2)–(3), Condition (4) (p. 14), Condition (5) and Assumption 1 (p. 15)

import Mathlib

namespace BleedFeed.ControlLimit

/-- The data of the bleed–feed model of Koca, Martagan, Adan, Maillart & van Ravenstein (§3, pp. 8–13).

* `m0` initial biomass, `tau` length τ of a period;
* `muL`, `muU` the bounds µℓ, µu of the growth-rate set ℳ = [µℓ, µu];
* `mtil` the critical biomass m̃, `nu` the rate ν(m) of entering the stationary phase;
* `I` the maximum cultivation age, `N` the regulatory limit on the number of bleed–feeds;
* `G` the law of the growth rate M drawn after a bleed–feed. -/
structure Params where
  m0 : ℝ
  tau : ℝ
  muL : ℝ
  muU : ℝ
  mtil : ℝ
  nu : ℝ → ℝ
  I : ℕ
  N : ℕ
  G : MeasureTheory.Measure ℝ

/-- The set ℳ = [µℓ, µu] of cell growth rates. -/
def Params.rates (P : Params) : Set ℝ := Set.Icc P.muL P.muU

/-- The standing assumptions of §3: positive initial biomass and period length, 0 < µℓ ≤ µu, I ≥ 1,
m̃ ≥ 0; ν vanishes up to m̃ and is strictly increasing from m̃ on; ν(m)τ ≤ 1 (so that
1 − p_iµ = ν(m_iµ)τ is a probability); ν is measurable; G is a probability measure carried by
[µℓ, µu]. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.m0 ∧ 0 < P.tau ∧ 0 < P.muL ∧ P.muL ≤ P.muU ∧ 1 ≤ P.I ∧ 0 ≤ P.mtil ∧
  (∀ m, m ≤ P.mtil → P.nu m = 0) ∧ StrictMonoOn P.nu (Set.Ici P.mtil) ∧
  (∀ m, P.nu m * P.tau ≤ 1) ∧ Measurable P.nu ∧
  MeasureTheory.IsProbabilityMeasure P.G ∧ P.G (P.rates)ᶜ = 0

/-- Biomass at cultivation age `i` with growth rate `μ`: m_iµ = m0 (1 + µτ)^i, equation (1). -/
def mass (P : Params) (i : ℕ) (μ : ℝ) : ℝ := P.m0 * (1 + μ * P.tau) ^ i

/-- Immediate reward of continuing at age `i`: r_iµ = m_{i+1,µ} − m_iµ (p. 12). -/
def r (P : Params) (i : ℕ) (μ : ℝ) : ℝ := mass P (i + 1) μ - mass P i μ

/-- Probability of staying in the exponential growth phase from age `i` to `i + 1`:
p_iµ = 1 − ν(m_iµ)τ (p. 11). -/
def p (P : Params) (i : ℕ) (μ : ℝ) : ℝ := 1 - P.nu (mass P i μ) * P.tau

/-- The critical age ĩ_µ: the least cultivation age at which the biomass exceeds the critical
biomass m̃ (p. 12). -/
noncomputable def critAge (P : Params) (μ : ℝ) : ℕ := sInf {i : ℕ | P.mtil < mass P i μ}

/-- Value along the cultivation age when the bleed–feed value is the constant `b`:
`W P b μ i = 0` for `i ≥ I`, and otherwise
`W P b μ i = max (r_iµ + p_iµ · W P b μ (i+1)) b`. With `b = B(n)` this is v(·, µ, n) of (2). -/
noncomputable def W (P : Params) (b : ℝ) (μ : ℝ) (i : ℕ) : ℝ :=
  if P.I ≤ i then 0 else max (r P i μ + p P i μ * W P b μ (i + 1)) b
termination_by P.I - i
decreasing_by omega

/-- Value of continuing at age `i` when the bleed–feed value is `b`: r_iµ + p_iµ · W(i+1). -/
noncomputable def Ck (P : Params) (b : ℝ) (i : ℕ) (μ : ℝ) : ℝ :=
  r P i μ + p P i μ * W P b μ (i + 1)

/-- Bleed–feed value with `k` bleed–feeds still permitted: `Bk P 0 = 0` (B(N) = 0), and
`Bk P (k+1) = ∫ C(0, µ', ·) dG(µ')` where the continuation uses the bleed–feed value `Bk P k`. -/
noncomputable def Bk (P : Params) : ℕ → ℝ
  | 0 => 0
  | k + 1 => ∫ μ', Ck P (Bk P k) 0 μ' ∂P.G

/-- B(n) = 𝔼[C(0, M, n + 1)] for n < N, and B(N) = 0 (equation (2) and p. 13). -/
noncomputable def B (P : Params) (n : ℕ) : ℝ := Bk P (P.N - n)

/-- C(i, µ, n) = r_iµ + p_iµ v(i + 1, µ, n), the value of continuing (equation (2)). -/
noncomputable def C (P : Params) (i : ℕ) (μ : ℝ) (n : ℕ) : ℝ := Ck P (B P n) i μ

/-- The value function v(i, µ, n) of the optimality equations (2)–(3), with v(I, µ, n) = 0. -/
noncomputable def v (P : Params) (i : ℕ) (μ : ℝ) (n : ℕ) : ℝ := W P (B P n) μ i

/-- Bleed–feed is optimal in state (i, µ, n): it is feasible (n < N) and attains the maximum in (2). -/
def BleedOpt (P : Params) (i : ℕ) (μ : ℝ) (n : ℕ) : Prop := n < P.N ∧ C P i μ n ≤ B P n

/-- Continuing is optimal in state (i, µ, n): it attains the maximum in (2) (at n = N it is the only
action, and B(N) = 0). -/
def ContOpt (P : Params) (i : ℕ) (μ : ℝ) (n : ℕ) : Prop := B P n ≤ C P i μ n

/-- Condition (4), p. 14: (r_iµ − r_{i−1,µ}) / r_iµ ≤ p_{i−1,µ} − p_iµ for all ĩ_µ ≤ i < I, µ ∈ ℳ.
(At i = 0, `i - 1 = 0` in ℕ and the inequality reads 0 ≤ 0.) -/
def Condition4 (P : Params) : Prop :=
  ∀ μ ∈ P.rates, ∀ i : ℕ, critAge P μ ≤ i → i < P.I →
    (r P i μ - r P (i - 1) μ) / r P i μ ≤ p P (i - 1) μ - p P i μ

/-- Condition (5), p. 15, on the range used by the proof of Proposition 3 (p. 34):
(r_{i−1,µ⁺} − r_{i−1,µ}) / r_{iµ⁺} ≤ p_{i−1,µ} − p_{i−1,µ⁺} for all ĩ_{µ⁺} < i < I and µ ≤ µ⁺ in ℳ.
The page prints the range ĩ_{µ⁺} ≤ i < I. -/
def Condition5 (P : Params) : Prop :=
  ∀ μ ∈ P.rates, ∀ μ' ∈ P.rates, μ ≤ μ' → ∀ i : ℕ, critAge P μ' < i → i < P.I →
    (r P (i - 1) μ' - r P (i - 1) μ) / r P i μ' ≤ p P (i - 1) μ - p P (i - 1) μ'

/-- Assumption 1, p. 15: in all states (I − 1, µ, n) with µ ∈ ℳ and n < N, bleed–feed is optimal. -/
def Assumption1 (P : Params) : Prop :=
  ∀ μ ∈ P.rates, ∀ n : ℕ, n < P.N → BleedOpt P (P.I - 1) μ n

end BleedFeed.ControlLimit


