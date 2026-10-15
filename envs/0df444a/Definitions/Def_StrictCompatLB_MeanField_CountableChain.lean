-- Prove2me | Definitions.Def_StrictCompatLB_MeanField_CountableChain
-- name    : StrictCompatLB_MeanField_CountableChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:37.183164+00:00
-- url     : https://prove2.me/theorems/762f3659-7a5a-48af-85a9-3d87fb319586
-- title:
--   Markov chains on a countable state space — stationary distributions, n-step kernels, petite sets, drift, and uniformisation by a Poisson clock
-- statement:
--   Let $S$ be a countable set and $K:S\times S\to\mathbb R$ a transition kernel, $K(z,z')$ being the probability of a jump from $z$ to $z'$. This file collects the generic notions used for the load-balancing chain.
--
--   1. $K$ is **stochastic** if $K(z,z')\ge 0$ and $\sum_{z'}K(z,z')=1$ for every $z$.
--   2. The **one-step expectation** $(Kf)(z)=\sum_{z'}K(z,z')f(z')$ and the **drift** $\Delta V(z)=(KV)(z)-V(z)=\mathbb E[V(Y_1)-V(Y_0)\mid Y_0=z]$ of a function $V$ (App. H, (H.1)).
--   3. The **$n$-step kernel** $K^0(z,z')=\mathbb 1\{z=z'\}$, $K^{n+1}(z,z')=\sum_y K^n(z,y)K(y,z')$.
--   4. A **stationary distribution** is a probability vector $\pi$ on $S$ with $\sum_z\pi(z)K(z,z')=\pi(z')$ for every $z'$. For a probability vector $\pi$ we write $\pi(A)=\sum_{z\in A}\pi(z)$ and $\mathbb E_\pi[f]=\sum_z\pi(z)f(z)\in[0,\infty]$ for $f\ge0$.
--   5. **Petite set** (Definition H.3): $C\subseteq S$ is petite if there are a probability distribution $a=(a(n))_{n\ge0}$ on $\mathbb N$ and a nonzero measure $\mu$ on $S$ with
--   $$\sum_{n=0}^\infty K^n(z,A)\,a(n)\;\ge\;\mu(A)\qquad\text{for all }z\in C,\ A\subseteq S.$$
--   6. **Uniformised process.** On a probability space $(\Omega,P)$, a pair $(Y,\tau)$ realises the continuous-time process with jump kernel $K$, clock rate $r$ and initial state $z_0$ if $Y=(Y_n)_{n\ge0}$ is a Markov chain with kernel $K$ started at $z_0$, i.e.
--   $$P(Y_0=z_0',\dots,Y_n=z_n)=\mathbb 1\{z_0'=z_0\}\prod_{j<n}K(z_j,z_{j+1}),$$
--   the gaps $\tau_0,\tau_1,\dots$ are i.i.d. exponential with rate $r$, and $Y$ is independent of $(\tau_k)$. The process at time $t\ge0$ is $Y_{n(t)}$, where $n(t)=\max\{n:\tau_0+\dots+\tau_{n-1}\le t\}$ is the number of clock epochs in $(0,t]$.
--
--   For a Markov process with bounded jump rates, running the embedded uniformised chain at the epochs of an independent Poisson clock is the standard construction (App. H, p. 46: "the Markov process can now be viewed as a uniformized Markov chain"); the stationary distributions of the process are those of the uniformised chain.
--
--   **Formalization Note** The kernel is real-valued; $(Kf)(z)$ and $K^n$ are written with `tsum`, which is a finite sum for the kernels used in this mission (every row has finite support). The petite-set inequality and the expectation are computed in $[0,\infty]$, so no summability condition is needed there. The epoch count is an `sSup` of a set of naturals; it equals $n(t)$ for $t\ge0$ whenever the gaps are positive with divergent sum (an event of probability one), and returns $0$ on the complementary null event.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 46, App. H (uniformised chain, (H.1)); p. 49, Definition H.3, (H.11)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-! Discrete-time Markov chains on a countable state space `S` given by a transition kernel
`K : S → S → ℝ` (`K z z'` is the probability of a jump from `z` to `z'`), and the continuous-time
process obtained from such a chain by uniformisation: the chain jumps at the epochs of an
independent Poisson clock. Generic notions, used for the load-balancing chain of
Rutten & Mukherjee, arXiv:2008.07562v2, App. H (pp. 46–50). -/

/-- `K` is a stochastic kernel: nonnegative entries, every row a probability vector. -/
def IsStochasticKernel {S : Type*} (K : S → S → ℝ) : Prop :=
  (∀ z z', 0 ≤ K z z') ∧ ∀ z, HasSum (K z) 1

/-- The one-step conditional expectation `E[f(Y₁) | Y₀ = z] = ∑_{z'} K(z, z') f(z')`. It is a
`tsum`; for the kernels it is applied to here every row has finite support, so the sum is a
finite sum. -/
noncomputable def kexp {S : Type*} (K : S → S → ℝ) (f : S → ℝ) (z : S) : ℝ :=
  ∑' z', K z z' * f z'

/-- The expected one-step increase `ΔV(z) = E[V(Y₁) − V(Y₀) | Y₀ = z]` of a function `V`
(App. H, (H.1), p. 46). -/
noncomputable def oneStepDrift {S : Type*} (K : S → S → ℝ) (V : S → ℝ) (z : S) : ℝ :=
  kexp K V z - V z

/-- The `n`-step transition probabilities `Kⁿ(z, z')`: `K⁰` is the identity and
`K^{n+1}(z, z') = ∑_y Kⁿ(z, y) K(y, z')`. -/
noncomputable def stepProb {S : Type*} [DecidableEq S] (K : S → S → ℝ) : ℕ → S → S → ℝ
  | 0, z, z' => if z = z' then 1 else 0
  | n + 1, z, z' => ∑' y, stepProb K n z y * K y z'

/-- `π` is a probability vector on `S`. -/
def IsProbVec {S : Type*} (π : S → ℝ) : Prop :=
  (∀ z, 0 ≤ π z) ∧ HasSum π 1

/-- `π` is a stationary distribution of `K`: a probability vector with
`∑_z π(z) K(z, z') = π(z')` for every `z'` (the series converging to `π(z')`). -/
def IsStationary {S : Type*} (K : S → S → ℝ) (π : S → ℝ) : Prop :=
  IsProbVec π ∧ ∀ z', HasSum (fun z => π z * K z z') (π z')

/-- The probability `π(A) = ∑_{z ∈ A} π(z)` of a set `A` of states under the law `π`. -/
noncomputable def probOf {S : Type*} (π : S → ℝ) (A : Set S) : ℝ :=
  ∑' z, A.indicator π z

/-- The expectation `E_π[f] = ∑_z π(z) f(z)` of a nonnegative function, computed in `[0, ∞]`
(never a junk value). -/
noncomputable def expectENN {S : Type*} (π : S → ℝ) (f : S → ℝ) : ℝ≥0∞ :=
  ∑' z, ENNReal.ofReal (π z) * ENNReal.ofReal (f z)

/-- Petite set (Definition H.3, p. 49): `C ⊆ S` is petite if there are a probability
distribution `a = (a(n))_{n ≥ 0}` on `ℕ` and a nontrivial measure `μ` on `S` (given by its
masses `μ(x) ∈ [0, ∞]`, `μ(A) = ∑_{x ∈ A} μ(x)`, not identically zero) such that
`∑_{n ≥ 0} Kⁿ(z, A) a(n) ≥ μ(A)` for every `z ∈ C` and every `A ⊆ S`. -/
def IsPetite {S : Type*} [DecidableEq S] (K : S → S → ℝ) (C : Set S) : Prop :=
  ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ HasSum a 1 ∧
    ∃ μ : S → ℝ≥0∞, (∑' x, μ x) ≠ 0 ∧
      ∀ z ∈ C, ∀ A : Set S,
        ∑' x, A.indicator μ x ≤
          ∑' n, ENNReal.ofReal (a n) *
            ∑' x, A.indicator (fun y => ENNReal.ofReal (stepProb K n z y)) x

/-- The number of clock epochs in `[0, t]` when the gaps between consecutive epochs are
`τ 0, τ 1, …` (the `k`-th epoch is at `τ 0 + ⋯ + τ (k-1)`): the largest `n` with
`τ 0 + ⋯ + τ (n-1) ≤ t`. For `t ≥ 0` and positive gaps with divergent sum this set is
`{0, …, n(t)}`; on the null event where it is unbounded, `sSup` returns `0`. -/
noncomputable def epochCount (τ : ℕ → ℝ) (t : ℝ) : ℕ :=
  sSup {n : ℕ | ∑ k ∈ Finset.range n, τ k ≤ t}

/-- The continuous-time path `t ↦ Y_{n(t)}` of a chain `Y` run at the clock epochs. -/
noncomputable def jumpPath {S : Type*} (Y : ℕ → S) (τ : ℕ → ℝ) (t : ℝ) : S :=
  Y (epochCount τ t)

/-- A **uniformised Markov process** with kernel `K`, clock rate `rate` and initial state `z₀`,
on a probability space `(Ω, P)`:
1. `Y = (Y₀, Y₁, …)` is a Markov chain with kernel `K` started at `z₀`: for every `n` and states
   `z_0, …, z_n`, `P(Y₀ = z₀', …, Y_n = z_n) = 𝟙{z₀' = z₀} ∏_{j < n} K(z_j, z_{j+1})`;
2. the gaps `τ 0, τ 1, …` are i.i.d. exponential with rate `rate`;
3. the chain `Y` is independent of the gaps.
The process at time `t ≥ 0` is `jumpPath Y τ t = Y_{n(t)}`. -/
def IsUniformizedProcess {S : Type*} [DecidableEq S] [MeasurableSpace S]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (K : S → S → ℝ) (rate : ℝ) (z₀ : S)
    (Y : ℕ → Ω → S) (τ : ℕ → Ω → ℝ) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ n, Measurable (Y n)) ∧
  (∀ (n : ℕ) (zs : ℕ → S), P {ω | ∀ j ≤ n, Y j ω = zs j} =
      ENNReal.ofReal ((if zs 0 = z₀ then 1 else 0) *
        ∏ j ∈ Finset.range n, K (zs j) (zs (j + 1)))) ∧
  (∀ k, Measurable (τ k)) ∧ iIndepFun τ P ∧ (∀ k, P.map (τ k) = expMeasure rate) ∧
  IndepFun (fun ω n => Y n ω) (fun ω k => τ k ω) P

end StrictCompatLB.MeanField


