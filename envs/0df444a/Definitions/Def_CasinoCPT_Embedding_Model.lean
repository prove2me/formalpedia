-- Prove2me | Definitions.Def_CasinoCPT_Embedding_Model
-- name    : CasinoCPT_Embedding_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:57.608345+00:00
-- url     : https://prove2.me/theorems/155b4915-bdc3-496d-ab7e-8914bf315137
-- title:
--   §2.2, §3, pp. 9–16 — SSRW with randomization, 𝒯_T, 𝒫₀(ℤ), the potential U_µ, evolutional functions (6), condition (8), randomized Root stopping times (7)
-- statement:
--   This file sets up the casino gambling model of Hu, Obłój and Zhou and the objects used to characterise the laws of its stopped states.
--
--   **The casino space** (§2.2, p. 9). A filtered probability space $(\Omega,\mathcal F,P;(\mathcal F_t)_{t\in\mathbb N})$ carries a standard symmetric random walk $S=(S_t)_{t\in\mathbb N}$ and a random variable $\xi$:
--
--   1. $S_0=0$ and each $S_t$ is $\mathcal F_t$-measurable;
--   2. every increment $S_{t+1}-S_t$ equals $+1$ or $-1$, equals $+1$ with probability $1/2$, and is independent of $\mathcal F_t$;
--   3. $\xi$ is $\mathcal F_0$-measurable and uniformly distributed on $[0,1]$.
--
--   **Admissible strategies** (p. 10). $\mathcal T_T$ is the set of $(\mathcal F_t)$-stopping times $\tau$ with $\tau\le T$. Since $\mathcal F_0$ contains $\xi$, such strategies may be path dependent and randomized.
--
--   **Centred integer laws and potentials** (p. 13). $\mathcal P_0(\mathbb Z)$ is the set of probability measures $\mu$ on $\mathbb Z$ with $\int|y|\,\mu(dy)<\infty$ and $\int y\,\mu(dy)=0$. The potential of $\mu$ is
--   $$U_\mu(x)=\int|x-y|\,\mu(dy),\qquad x\in\mathbb R,$$
--   the negative of the usual potential. For a stopping time $\sigma$, $U_{S_\sigma}$ denotes the potential of the law of $S_\sigma$.
--
--   **Evolutional functions** (6), p. 14. For $x\in\mathbb Z$,
--   $$U^\mu_0(x)=|x|,\qquad U^\mu_t(x)=\frac{U^\mu_{t-1}(x-1)+U^\mu_{t-1}(x+1)}{2}\wedge U_\mu(x),\quad t\ge1.$$
--
--   **Condition (8)** (p. 16). For $T\ge1$,
--   $$U_\mu(x)\le\frac{U^\mu_{T-1}(x+1)+U^\mu_{T-1}(x-1)}{2},\qquad x=-(T-2),-(T-4),\dots,T-4,T-2.$$
--   The index set is the set of integers $x$ with $|x|\le T-2$ and $x+T$ even; it is empty when $T=1$.
--
--   **Randomized Root stopping times** (7), p. 15. A barrier $b:\mathbb Z\to\mathbb N$ has $b(x)=x+2k\ge|x|$ for some $k\in\mathbb Z$, and boundary probabilities satisfy $r(x)\in[0,1]$. A family of Bernoulli variables $\{\xi_{t,x}:t\in\mathbb N,x\in\mathbb Z\}$ is built from $\mathcal F_0$-information. The variables are mutually independent, and
--   $$P(\xi_{t,x}=0)=\begin{cases}0,&t<b(x),\\ r(x),&t=b(x),\\ 1,&t>b(x).\end{cases}$$
--   The randomized Root stopping time is
--   $$\tau_R(b,r)=\inf\{t\in\mathbb N: t\ge b(S_t)\text{ and }\xi_{t,S_t}=0\},\qquad\inf\emptyset=\infty.$$
--
--   These objects state Theorem 3.1 and the auxiliary results of Appendix A.
--
--   **Formalization Note.** Stopping times are $\mathbb N_\infty$-valued, as in Mathlib, and the law of $S_\sigma$ is the push-forward of $P$ under Mathlib's `stoppedValue S σ`. Laws are measures on $\mathbb Z$. The independence of $\xi$ from $S$ assumed on p. 9 is not a separate field: it follows from the increments being independent of $\mathcal F_t\supseteq\mathcal F_0$. The paper extends $U^\mu_t$ to $\mathbb R$ by linear interpolation; the formalization keeps $U^\mu_t$ on the integers, and statements about the interpolation are stated at the integers. A coin value `false` is the paper's $\xi_{t,x}=0$, "stop". The coin probabilities are recorded through the real number $P(\xi_{t,x}=0)$.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, pp. 9–16, §2.2, §3, (6), (7), (8)

import Mathlib

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- §2.2, p. 9: the gain/loss process `S` is a standard symmetric random walk on the filtered
probability space `(Ω, P; (F t))`, and `F 0` carries a random variable `ξ` uniform on `[0, 1]`.
* `S 0 = 0`, and each `S t` is `F t`-measurable;
* every increment `S (t+1) - S t` is `+1` or `-1`, equals `+1` with probability `1/2`, and is
  independent of `F t`;
* `ξ` is `F 0`-measurable with law the uniform distribution on `[0, 1]`.
Independence of `ξ` and `S` (p. 9) follows from the increment independence, since
`F 0 ≤ F t`. -/
structure IsCasinoSpace {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) : Prop where
  isProb : IsProbabilityMeasure P
  zero : ∀ ω, S 0 ω = 0
  adapted : ∀ t, Measurable[F t] (S t)
  step : ∀ t ω, S (t + 1) ω - S t ω = 1 ∨ S (t + 1) ω - S t ω = -1
  fair : ∀ t, P {ω | S (t + 1) ω - S t ω = 1} = 1 / 2
  indep : ∀ t,
    Indep (MeasurableSpace.comap (fun ω => S (t + 1) ω - S t ω) inferInstance) (F t) P
  unif_meas : Measurable[F 0] ξ
  unif_law : P.map ξ = volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The admissible strategies `𝒯_T` (p. 10): `(F t)`-stopping times `τ` with values in
`[0, T]`. Stopping times are `ℕ∞`-valued, as in Mathlib. -/
def IsAdmissible {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℕ mΩ) (T : ℕ)
    (τ : Ω → ℕ∞) : Prop :=
  IsStoppingTime F τ ∧ ∀ ω, τ ω ≤ T

/-- `𝒫₀(ℤ)` (p. 13): probability laws on `ℤ` with finite first moment and mean zero. -/
def InP0Z (μ : Measure ℤ) : Prop :=
  IsProbabilityMeasure μ ∧ Integrable (fun y : ℤ => (y : ℝ)) μ ∧ ∫ y, (y : ℝ) ∂μ = 0

/-- The potential `U_μ(x) = ∫ |x - y| μ(dy)`, `x ∈ ℝ` (p. 13; the negative of the usual
potential, footnote 13). -/
noncomputable def potential (μ : Measure ℤ) (x : ℝ) : ℝ :=
  ∫ y, |x - (y : ℝ)| ∂μ

/-- The evolutional functions (6), p. 14, on the integers:
`U^μ_0(x) = |x|` and `U^μ_t(x) = ((U^μ_{t-1}(x-1) + U^μ_{t-1}(x+1)) / 2) ∧ U_μ(x)`. -/
noncomputable def evol (μ : Measure ℤ) : ℕ → ℤ → ℝ
  | 0, x => |(x : ℝ)|
  | t + 1, x => min ((evol μ t (x - 1) + evol μ t (x + 1)) / 2) (potential μ (x : ℝ))

/-- Condition (8), p. 16: `U_μ(x) ≤ (U^μ_{T-1}(x+1) + U^μ_{T-1}(x-1)) / 2` for
`x = -(T-2), -(T-4), …, T-4, T-2`, i.e. for the integers `x` with `|x| ≤ T - 2` and
`x + T` even (no condition when `T = 1`). Used only with `1 ≤ T`. -/
def Cond8 (μ : Measure ℤ) (T : ℕ) : Prop :=
  ∀ x : ℤ, |x| ≤ (T : ℤ) - 2 → Even (x + (T : ℤ)) →
    potential μ (x : ℝ) ≤ (evol μ (T - 1) (x + 1) + evol μ (T - 1) (x - 1)) / 2

/-- A Root barrier `b` with boundary probabilities `r` (p. 15): for every `x ∈ ℤ`,
`b(x) = x + 2k ≥ |x|` for some integer `k`, and `r(x) ∈ [0, 1]`. -/
def IsRootBarrier (b : ℤ → ℕ) (r : ℤ → ℝ) : Prop :=
  ∀ x : ℤ, |x| ≤ (b x : ℤ) ∧ Even ((b x : ℤ) - x) ∧ 0 ≤ r x ∧ r x ≤ 1

/-- The Bernoulli family `{ξ_{t,x} : t ∈ ℕ, x ∈ ℤ}` of p. 15, realised on the casino space from
`F 0`-information. `coin t x ω = false` is the paper's `ξ_{t,x} = 0` ("stop"). The coins are
`F 0`-measurable and mutually independent, with
`P(ξ_{t,x} = 0) = 0`, `r(x)`, `1` for `t < b(x)`, `t = b(x)`, `t > b(x)` respectively. -/
structure IsRootCoins {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool) : Prop where
  meas : ∀ t x, Measurable[F 0] (coin t x)
  indep : iIndepFun (fun p : ℕ × ℤ => coin p.1 p.2) P
  law : ∀ t x, (P {ω | coin t x ω = false}).toReal =
    if t < b x then 0 else if t = b x then r x else 1

/-- The randomized Root stopping time (7), p. 15:
`τ_R(b, r) = inf {t ∈ ℕ : t ≥ b(S_t) and ξ_{t,S_t} = 0}`, with `inf ∅ = ∞`. -/
noncomputable def rootTime {Ω : Type*} (S : ℕ → Ω → ℤ) (b : ℤ → ℕ)
    (coin : ℕ → ℤ → Ω → Bool) (ω : Ω) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : b (S t ω) ≤ t ∧ coin t (S t ω) ω = false), (t : ℕ∞)

end CasinoCPT.Embedding


