-- Prove2me | Definitions.Def_ManyServerQED_Scheduling_Model
-- name    : ManyServerQED_Scheduling_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:03:50.813251+00:00
-- url     : https://prove2.me/theorems/aa8d8494-c633-4220-b9cf-d3874684b68f
-- title:
--   The sequence of $k$-class, $n$-server queues with abandonment in the QED regime (Assumption 1(i)) and Assumption 3
-- statement:
--   This file defines the sequence of queueing systems of Sections 2.1 and 2.3. There are $k$ customer classes, and the $n$-th system has $n$ identical servers. All systems live on one complete probability space $(\Omega,\mathcal F,P)$.
--
--   **Poisson processes.** A process $N$ is a Poisson process of rate $a\ge0$ if $N(0)=0$, its paths are $\mathbb Z_+$-valued, nondecreasing and càdlàg, its increments over consecutive time windows are independent, and $N(t)-N(s)$ is Poisson with mean $a(t-s)$. Rate $0$ gives the zero process.
--
--   **Primitives of the $n$-th system.**
--   1. Arrivals. For each class $i$, the variables $\check U_i(j)$, $j\ge1$, are strictly positive and i.i.d., with $E\check U_i(1)=1$ and finite variance $C^2_{U,i}=\operatorname{Var}\check U_i(1)$. The interarrival times are $U^n_i(j)=\check U_i(j)/\lambda^n_i$ with $\lambda^n_i>0$, and
--   $$
--   A^n_i(t)=\sup\Big\{m\ge0:\sum_{j=1}^mU^n_i(j)\le t\Big\}.\qquad(3)
--   $$
--   2. Service. $S^n_i$ is a Poisson process of rate $\mu^n_i>0$.
--   3. Abandonment. $R^n_i$ is a Poisson process of rate $\theta^n_i\ge0$.
--
--   For each $n$, all $\check U_i(j)$, $S^n_i$ and $R^n_i$ are mutually independent.
--
--   **Assumption 1(i).** There are $\lambda_i,\mu_i>0$, $\theta_i\ge0$ and $\hat\lambda_i,\hat\mu_i\in\mathbb R$ with $\sum_i\lambda_i/\mu_i=1$ and, as $n\to\infty$,
--   $$
--   n^{-1}\lambda^n_i\to\lambda_i,\quad \mu^n_i\to\mu_i,\quad\theta^n_i\to\theta_i,\quad n^{1/2}(n^{-1}\lambda^n_i-\lambda_i)\to\hat\lambda_i,\quad n^{1/2}(\mu^n_i-\mu_i)\to\hat\mu_i.
--   $$
--
--   **Derived quantities.**
--   - $\rho_i=\lambda_i/\mu_i$, $r_i=(\lambda_iC^2_{U,i}+\lambda_i)^{1/2}$ (14) and $\ell_i=\hat\lambda_i-\rho_i\hat\mu_i$ (p. 15). These give the diffusion data $(\ell,\mu,\theta,r)$.
--   - The rescaled primitives $\hat A^n_i(t)=n^{-1/2}(A^n_i(t)-\lambda^n_it)$, $\hat S^n_i(t)=n^{-1/2}(S^n_i(nt)-n\mu^n_it)$ and $\hat R^n_i(t)=n^{-1/2}(R^n_i(nt)-n\theta^n_it)$.
--   - The next-arrival time $\tau^n_i(t)$, the first class-$i$ arrival at or after $t$.
--
--   **Assumption 3.** There is $m_U\ge2$ with $m_U>m_L$ and $E(\check U_i(1))^{m_U}<\infty$ for every $i$.
--
--   **Formalization Note** Classes are `Fin k`. Time is real and every condition is for $t\ge0$. Following the paper's convention on p. 10 ("without loss"), the partial sums of the $\check U_i(j)$ diverge for every $\omega$, so $A^n_i$ is finite everywhere. The Poisson path properties likewise hold for every $\omega$. Independence is stated for the $\sigma$-algebras of $\check U_i(j)$ and of the paths of $S^n_i$, $R^n_i$ on $[0,\infty)$. Assumption 1(ii) is not part of the model, because the statements carry their own hypotheses on initial states. The counting process $A^n_i$ uses the published `BellWilliams2001.ThresholdPolicy.renewalCount` and `partialSum`.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), pp. 8-10 (§2.1, (2)-(3)), p. 11 (tau), pp. 12-14 (Assumption 1(i), rescaled processes, (14)), p. 15 (ell), p. 20 Assumption 3

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

open BellWilliams2001.ThresholdPolicy

/-!
Atar, Mandelbaum & Reiman (2004), §2.1 (pp. 8–10), §2.3 (pp. 12–14) and Assumption 3 (p. 20): the
sequence of `k`-class, `n`-server queueing systems with abandonment, all on one complete
probability space `(Ω, F, P)`.

Conventions. Classes are `Fin k` (paper class `i` is index `i − 1`). The system index `n` is the
number of servers; the paper's `n ∈ ℕ = {1, 2, …}`, and every statement about the `n`-th system
assumes `1 ≤ n`. Time is real and every condition quantifies over `t ≥ 0` (as in
`BellWilliams2001.ThresholdPolicy.Paths`). The interarrival sequences keep the paper's index base:
`U i j` for `j = 1, 2, …` (the value at `j = 0` is never used). Counting processes are real-valued
functions of time that take values in `ℕ`.
-/

/-- `N` is a **Poisson process of rate `a ≥ 0`** on `(Ω, P)` (time `t ≥ 0`): every path starts at
`0`, takes values in `ℕ`, is nondecreasing, right-continuous with left limits; `N(t)` is a random
variable; increments over consecutive time windows are independent; and `N(t) − N(s)` has the
Poisson law of mean `a(t − s)` for `0 ≤ s ≤ t`. For `a = 0` the last condition says
`N(t) − N(s) = 0` a.s. (Mathlib's `poissonMeasure 0` is the point mass at `0`). -/
structure IsPoissonProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → ℝ → ℝ)
    (a : ℝ) : Prop where
  rate_nonneg : 0 ≤ a
  zero : ∀ ω, N ω 0 = 0
  nat_valued : ∀ ω t, 0 ≤ t → ∃ m : ℕ, N ω t = m
  mono : ∀ ω, MonotoneOn (N ω) (Set.Ici 0)
  cadlag : ∀ ω, IsCadlag (N ω)
  meas : ∀ t, Measurable (fun ω => N ω t)
  indep_incr : ∀ (m : ℕ) (s : Fin (m + 1) → ℝ), 0 ≤ s 0 → Monotone s →
    iIndepFun (fun j : Fin m => fun ω => N ω (s j.succ) - N ω (s j.castSucc)) P
  law : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ j : ℕ,
    P {ω | N ω t - N ω s = j} = poissonMeasure (a * (t - s)).toNNReal {j}

/-- The sequence of queueing systems of §2.1 and §2.3, with Assumption 1(i). Every field is a
hypothesis of the paper:
* (p. 8) a complete probability space `(Ω, F, P)` carrying the processes of every system `n`
  (p. 12);
* (p. 9) for each class `i`, strictly positive i.i.d. `Ǔᵢ(j)`, `j ≥ 1`, with `EǓᵢ(1) = 1` and
  finite squared coefficient of variation `C²_{U,i} = Var Ǔᵢ(1)`; they do not depend on `n`;
  the interarrival times of the `n`-th system are `Uⁿᵢ(j) = Ǔᵢ(j)/λⁿᵢ` (2) with `λⁿᵢ > 0`;
* (p. 9) service: Poisson processes `Sⁿᵢ` of rate `µⁿᵢ ∈ (0, ∞)`; abandonment: Poisson processes
  `Rⁿᵢ` of rate `θⁿᵢ ∈ [0, ∞)`;
* (p. 9) for each `n`, the arrival processes `Aⁿᵢ` (i.e. all `Ǔᵢ(j)`), the `Sⁿᵢ` and the `Rⁿᵢ` are
  mutually independent (paths of `S`, `R` on `t ≥ 0`);
* (p. 10) the realizations on which some `Aⁿᵢ(t)` is infinite are omitted "without loss": the
  partial sums of the `Ǔᵢ(j)` diverge for every `ω`;
* Assumption 1(i) (pp. 12–13): constants `λᵢ, µᵢ ∈ (0, ∞)`, `θᵢ ∈ [0, ∞)`, `λ̂ᵢ, µ̂ᵢ ∈ ℝ` with
  `∑ᵢ λᵢ/µᵢ = 1`, `n⁻¹λⁿᵢ → λᵢ`, `µⁿᵢ → µᵢ`, `θⁿᵢ → θᵢ`, `n^{1/2}(n⁻¹λⁿᵢ − λᵢ) → λ̂ᵢ`,
  `n^{1/2}(µⁿᵢ − µᵢ) → µ̂ᵢ`.

Assumption 1(ii) (initial conditions) is not part of the model; the statements carry their own
hypotheses on the initial data. -/
structure SystemSequence (Ω : Type*) [MeasurableSpace Ω] (k : ℕ) where
  /-- the probability measure `P` -/
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  complete : P.IsComplete
  /-- `Ǔᵢ(j)`, `j ≥ 1` -/
  U : Fin k → ℕ → Ω → ℝ
  U_meas : ∀ i j, Measurable (U i j)
  U_pos : ∀ i j ω, 1 ≤ j → 0 < U i j ω
  U_ident : ∀ i j, 1 ≤ j → IdentDistrib (U i j) (U i 1) P P
  U_memLp : ∀ i, MemLp (U i 1) 2 P
  U_mean : ∀ i, ∫ ω, U i 1 ω ∂P = 1
  U_finite : ∀ i ω, Tendsto (fun m => partialSum (fun j => U i j ω) m) atTop atTop
  /-- `λⁿᵢ` -/
  lamN : ℕ → Fin k → ℝ
  /-- `µⁿᵢ` -/
  muN : ℕ → Fin k → ℝ
  /-- `θⁿᵢ` -/
  thetaN : ℕ → Fin k → ℝ
  lamN_pos : ∀ n i, 0 < lamN n i
  muN_pos : ∀ n i, 0 < muN n i
  thetaN_nonneg : ∀ n i, 0 ≤ thetaN n i
  /-- the service Poisson processes `Sⁿᵢ` -/
  S : ℕ → Fin k → Ω → ℝ → ℝ
  /-- the abandonment Poisson processes `Rⁿᵢ` -/
  R : ℕ → Fin k → Ω → ℝ → ℝ
  S_poisson : ∀ n i, IsPoissonProcess P (S n i) (muN n i)
  R_poisson : ∀ n i, IsPoissonProcess P (R n i) (thetaN n i)
  /-- for each `n`: all `Ǔᵢ(j)` (`j ≥ 1`), all `Sⁿᵢ` and all `Rⁿᵢ` are mutually independent -/
  indep : ∀ n, iIndep (fun a : (Fin k × ℕ) ⊕ (Fin k ⊕ Fin k) =>
    Sum.elim (fun q : Fin k × ℕ => MeasurableSpace.comap (U q.1 (q.2 + 1)) inferInstance)
      (Sum.elim
        (fun i : Fin k => MeasurableSpace.comap (fun ω (t : ℝ≥0) => S n i ω t) inferInstance)
        (fun i : Fin k => MeasurableSpace.comap (fun ω (t : ℝ≥0) => R n i ω t) inferInstance)) a) P
  /-- `λᵢ` -/
  lam : Fin k → ℝ
  /-- `µᵢ` -/
  mu : Fin k → ℝ
  /-- `θᵢ` -/
  theta : Fin k → ℝ
  /-- `λ̂ᵢ` -/
  lamHat : Fin k → ℝ
  /-- `µ̂ᵢ` -/
  muHat : Fin k → ℝ
  lam_pos : ∀ i, 0 < lam i
  mu_pos : ∀ i, 0 < mu i
  theta_nonneg : ∀ i, 0 ≤ theta i
  /-- Assumption 1(i): `∑ᵢ λᵢ/µᵢ = 1` -/
  sum_rho : ∑ i, lam i / mu i = 1
  /-- Assumption 1(i): `n⁻¹λⁿᵢ → λᵢ` -/
  lam_lim : ∀ i, Tendsto (fun n : ℕ => lamN n i / n) atTop (𝓝 (lam i))
  /-- Assumption 1(i): `µⁿᵢ → µᵢ` -/
  mu_lim : ∀ i, Tendsto (fun n : ℕ => muN n i) atTop (𝓝 (mu i))
  /-- Assumption 1(i): `θⁿᵢ → θᵢ` -/
  theta_lim : ∀ i, Tendsto (fun n : ℕ => thetaN n i) atTop (𝓝 (theta i))
  /-- Assumption 1(i): `n^{1/2}(n⁻¹λⁿᵢ − λᵢ) → λ̂ᵢ` -/
  lamHat_lim : ∀ i, Tendsto (fun n : ℕ => Real.sqrt n * (lamN n i / n - lam i)) atTop
    (𝓝 (lamHat i))
  /-- Assumption 1(i): `n^{1/2}(µⁿᵢ − µᵢ) → µ̂ᵢ` -/
  muHat_lim : ∀ i, Tendsto (fun n : ℕ => Real.sqrt n * (muN n i - mu i)) atTop (𝓝 (muHat i))

namespace SystemSequence

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k)

/-- The partial sums `∑_{j=1}^m Uⁿᵢ(j)`, `Uⁿᵢ(j) = Ǔᵢ(j)/λⁿᵢ` ((2), (3), p. 9). -/
noncomputable def arrivalEpoch (n : ℕ) (i : Fin k) (ω : Ω) (m : ℕ) : ℝ :=
  partialSum (fun j => M.U i j ω / M.lamN n i) m

/-- The arrival process (3) (p. 9): `Aⁿᵢ(t) = sup{m ≥ 0 : ∑_{j=1}^m Uⁿᵢ(j) ≤ t}`, finite for every
`ω` by `U_finite`, so `toNat` loses nothing. -/
noncomputable def A (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) : ℝ :=
  ((renewalCount (M.arrivalEpoch n i ω) t).toNat : ℝ)

/-- `τⁿᵢ(t) = inf{u ≥ t : Aⁿᵢ(u) − Aⁿᵢ(u−) > 0}` (p. 11), the time of the first class-`i` arrival no
earlier than `t`. Since the `Ǔᵢ(j)` are strictly positive, `Aⁿᵢ` jumps exactly at the arrival
epochs `∑_{j=1}^m Uⁿᵢ(j)`, `m ≥ 1`; these diverge, so the set below is nonempty and has a least
element. -/
noncomputable def nextArrival (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) : ℝ :=
  sInf {u : ℝ | t ≤ u ∧ ∃ m : ℕ, 1 ≤ m ∧ M.arrivalEpoch n i ω m = u}

/-- `ρᵢ = λᵢ/µᵢ` (Assumption 1(ii), p. 13). -/
noncomputable def rho (i : Fin k) : ℝ := M.lam i / M.mu i

/-- The squared coefficient of variation `C²_{U,i} = Var(Ǔᵢ(1))` (p. 9; `EǓᵢ(1) = 1`). -/
noncomputable def cU2 (i : Fin k) : ℝ := variance (M.U i 1) M.P

/-- `rᵢ = (λᵢC²_{U,i} + λᵢ)^{1/2}` (14), p. 14. -/
noncomputable def rCoef (i : Fin k) : ℝ := Real.sqrt (M.lam i * M.cU2 i + M.lam i)

/-- `ℓᵢ = λ̂ᵢ − ρᵢµ̂ᵢ` (p. 15). -/
noncomputable def ell (i : Fin k) : ℝ := M.lamHat i - M.rho i * M.muHat i

/-- The data `(ℓ, µ, θ, r)` of the limiting diffusion (16), (25)–(26). -/
noncomputable def diffData : DiffusionData k where
  ell := M.ell
  mu := M.mu
  theta := M.theta
  r := M.rCoef
  mu_pos := M.mu_pos
  theta_nonneg := M.theta_nonneg
  r_pos := fun i => Real.sqrt_pos.2 (by
    have h1 : 0 ≤ M.cU2 i := variance_nonneg _ _
    have h2 := M.lam_pos i
    positivity)

/-- `Âⁿᵢ(t) = n^{−1/2}(Aⁿᵢ(t) − λⁿᵢ t)` (p. 14). -/
noncomputable def Ahat (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) : ℝ :=
  (M.A n i ω t - M.lamN n i * t) / Real.sqrt n

/-- `Ŝⁿᵢ(t) = n^{−1/2}(Sⁿᵢ(nt) − nµⁿᵢ t)` (p. 14). -/
noncomputable def Shat (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) : ℝ :=
  (M.S n i ω (n * t) - n * M.muN n i * t) / Real.sqrt n

/-- `R̂ⁿᵢ(t) = n^{−1/2}(Rⁿᵢ(nt) − nθⁿᵢ t)` (p. 14). -/
noncomputable def Rhat (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) : ℝ :=
  (M.R n i ω (n * t) - n * M.thetaN n i * t) / Real.sqrt n

/-- Assumption 3 (p. 20), with `m_L` the growth exponent of Assumption 2(iv): there is a constant
`m_U ≥ 2`, `m_U > m_L`, with `E(Ǔᵢ(1))^{m_U} < ∞` for every class `i` (a lower Lebesgue integral,
`Ǔᵢ(1) > 0`). -/
def Assumption3 (mL mU : ℝ) : Prop :=
  2 ≤ mU ∧ mL < mU ∧ ∀ i, ∫⁻ ω, ENNReal.ofReal (M.U i 1 ω) ^ mU ∂M.P < ⊤

end SystemSequence

end ManyServerQED.Scheduling


