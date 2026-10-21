-- Prove2me | Definitions.Def_JSEQDelay_Diffusion_Model
-- name    : JSEQDelay_Diffusion_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:01.258877+00:00
-- url     : https://prove2.me/theorems/592522ce-da4b-4ade-a6fa-3fe3a7352042
-- title:
--   §2.1–2.2, §3.1–3.3, pp. 7–12 — the JSEQ network with delayed information, its primitives, heavy traffic, delay function, estimators and diffusion scaling
-- statement:
--   A dispatcher routes one stream of jobs to $K\ge 2$ parallel single-server queues $\mathbb K=\{1,\dots,K\}$. This file fixes the sequence of networks indexed by $n$ and every object the main theorem refers to.
--
--   1. **Primitives.** A probability space $(\Omega,\mathcal F,\mathbb P)$ carries the interarrival times $u(1),u(2),\dots$ and, for each server $k$, the service times $v_k(1),v_k(2),\dots$. All of these variables are mutually independent, each sequence is identically distributed, and each variable is positive with mean $1$; the variances are $\alpha^2>0$ and $\gamma_k^2>0$. The renewal counts are $X(t)=\sup\{m: u(1)+\dots+u(m)\le t\}$ and $S_k(t)$ likewise.
--   2. **Rates and heavy traffic (Assumption 2.2).** The $n$-th network has rates $\lambda^n>0$, $\mu^n_k>0$ with
--   $$\lambda^n=n\bar\lambda+\sqrt n\,\hat\lambda+o(\sqrt n),\qquad \mu^n_k=n\bar\mu_k+\sqrt n\,\hat\mu_k+o(\sqrt n),\qquad \langle\bar\mu,\mathbf 1\rangle=\bar\lambda,$$
--   with $\bar\lambda,\bar\mu_k>0$. Then $X^n(t)=X(\lambda^nt)$ and $S^n_k(t)=S_k(\mu^n_kt)$.
--   3. **Delay function (§3.1).** $\tau:[0,\infty)\to[0,\infty)^K$ is componentwise non-decreasing with $\tau_k(t)\le t$ for $t>0$. **Assumption 3.1** adds continuity and an increasing sequence $T_0=0<T_1<\dots\to\infty$ with $\tau_k(t)\le T_m$ for $t\in[0,T_{m+1}]$.
--   4. **Estimators (22)–(24).** An estimator $\Psi^n$ maps a pair of paths $(q,a)\in\mathbb D_0(\mathbb R_+^K)\times\mathbb D_0(\mathbb R^K)$ to a path in $\mathbb D_0(\mathbb R_+^K)$, measurably for each time, and $\Psi^n(q,a)(t)$ depends only on $q_k$ on $[0,\tau_k(t)]$ and on $a$ on $[0,t]$. The estimated queue length is
--   $$\Phi^n_k(q,a)(t)=q_k(\tau_k(t))+a_k(t)-a_k(\tau_k(t))-\mu^n_k\,(t-\tau_k(t))+\Psi^n_k(q,a)(t).$$
--   5. **The JSEQ network.** The queue lengths $Q^n$ and routed arrivals $A^n$ start at $0$ and satisfy, for $t\ge0$,
--   $$Q^n_k(t)=A^n_k(t)-S^n_k\big(B^n_k(t)\big),\qquad B^n_k(t)=\int_0^t\mathbf 1\{Q^n_k(s)>0\}\,ds .$$
--   With $R^n=\Phi^n(Q^n,A^n)$, the $i$-th job, arriving at $\sigma^n_i=(u(1)+\dots+u(i))/\lambda^n$, joins the queue $k$ with $R^n_k(\sigma^n_i-)<R^n_j(\sigma^n_i-)$ for $j<k$ and $R^n_k(\sigma^n_i-)\le R^n_l(\sigma^n_i-)$ for $l\ge k$ (shortest estimate, lexicographic ties), and $A^n_k(t)$ counts the jobs $i\le X^n(t)$ sent to $k$.
--   6. **Diffusion scaling (9)–(13), (27), (29)–(30).** $\hat Q^n=Q^n/\sqrt n$, $\hat A^n_k=(A^n_k-\mu^n_k\iota)/\sqrt n$, $\hat X^n=(X^n-\langle\mu^n,\mathbf 1\rangle\iota)/\sqrt n$, $\hat S^n_k=(S^n_k-\mu^n_k\iota)/\sqrt n$, $\hat L^n_k=\mu^n_k(\iota-B^n_k)/\sqrt n$, $\hat\Psi^n(q,a)=\Psi^n(\sqrt n q,\sqrt n a+\mu^n\iota)/\sqrt n$, $\hat R^n=R^n/\sqrt n$ and $\hat M^n=\Psi^n(Q^n,A^n)/\sqrt n$, where $\iota(t)=t$.
--
--   These are the prelimit objects of Theorem 4.4; every later statement of the mission is phrased in them.
--
--   **Formalization Note** Servers are `Fin K` (paper index $k$ is Lean $k-1$, ties go to the smallest index). Paths are `ℝ → Fin K → ℝ` and only $t\ge0$ matters. Estimators act on real-valued paths because (27) evaluates them at $\sqrt n q$ and $\sqrt n a+\mu^n\iota$, which are not integer-valued. Routing uses the left limits $R^n(\sigma^n_i-)$ (`Function.leftLim`) as in the prose rule on p. 11, not the integral against $\Theta^n(\cdot)(s-)$. Renewal counts are $\mathbb N\cup\{\infty\}$-valued and converted to $\mathbb N$; they are finite on the probability-one event where the partial sums diverge, and the network equations are imposed on that event only. Positivity of the primitives is imposed for every $\omega$. $\alpha,\gamma_k$ are taken positive (only their squares appear). Rates are required positive for $n\ge1$, the paper's $\mathbb N$.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), pp. 7–8, §2.1, §2.2, (6)–(13), Assumption 2.2; pp. 9–12, §3.1, Assumption 3.1, §3.2, (22)–(25) and the routing rule on p. 11, §3.3, (26)–(30)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open BellWilliams2001.ThresholdPolicy

/-!
Atar & Lipshutz, *Heavy traffic limits for join the shortest estimated queue policy using
delayed information* (authors' manuscript of January 12, 2020), §1 p. 6, §2.1–2.2 pp. 7–8,
§3.1–3.3 pp. 9–12: the sequence of `K`-server networks routed by join the shortest estimated
queue (JSEQ). Servers are `Fin K` (the paper's server `k` is Lean's `k - 1`; the
lexicographic tie-break picks the smallest index). Time is real; paths are `ℝ → Fin K → ℝ` and
only times `t ≥ 0` matter.
-/

/-- A path in `ℝ^K` indexed by real time; only its values at `t ≥ 0` matter. -/
abbrev Path (K : ℕ) := ℝ → Fin K → ℝ

/-- `(q, a) ∈ 𝔻₀(ℝ₊^K) × 𝔻₀(ℝ^K)` (p. 6, (26)–(27)): both paths are RCLL on `[0, ∞)` and start
at `0`, and `q` is non-negative on `[0, ∞)`. This is the domain of the (scaled and unscaled)
estimator functions. -/
def IsD0Pair {K : ℕ} (q a : Path K) : Prop :=
  (∀ k, IsCadlag (fun t => q t k)) ∧ (∀ k, IsCadlag (fun t => a t k)) ∧
  q 0 = 0 ∧ a 0 = 0 ∧ ∀ t, 0 ≤ t → ∀ k, 0 ≤ q t k

/-- **Primitives** (§2.1, p. 7). The probability space `(Ω, 𝓕, P)` carries the interarrival
times `u 1, u 2, …` and, for each server `k`, the service times `v k 1, v k 2, …` (index base
`1`; the values at index `0` are never used). All of these random variables are mutually
independent (so the `K + 1` sequences are independent IID sequences), each sequence is
identically distributed, every variable is positive, has mean `1`, and has finite variance,
equal to `α²` for the arrivals and `γ k²` for server `k`, with `α > 0`, `γ k > 0`. -/
def Primitives {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (α : ℝ) (γ : Fin K → ℝ) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ i ω, 0 < u i ω) ∧ (∀ k i ω, 0 < v k i ω) ∧
  iIndepFun (fun p : Option (Fin K) × ℕ+ =>
    match p.1 with
    | none => u (p.2 : ℕ)
    | some k => v k (p.2 : ℕ)) P ∧
  (∀ i, 1 ≤ i → IdentDistrib (u i) (u 1) P P) ∧
  (∀ k i, 1 ≤ i → IdentDistrib (v k i) (v k 1) P P) ∧
  MemLp (u 1) 2 P ∧ (∀ k, MemLp (v k 1) 2 P) ∧
  ∫ ω, u 1 ω ∂P = 1 ∧ (∀ k, ∫ ω, v k 1 ω ∂P = 1) ∧
  0 < α ∧ variance (u 1) P = α ^ 2 ∧
  (∀ k, 0 < γ k ∧ variance (v k 1) P = γ k ^ 2)

/-- The arrival and service rates of the `n`-th network are positive (§2.1, p. 7):
`λⁿ > 0` and `μⁿ_k > 0`, for every network index `n ≥ 1` (the paper's `ℕ = {1, 2, …}`). -/
def Rates {K : ℕ} (lam : ℕ → ℝ) (mu : ℕ → Fin K → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ ∀ k, 0 < mu n k

/-- The first-order constants of the heavy traffic condition: `λ̄ > 0`, `μ̄_k > 0` and the
balance `⟨μ̄, 𝟏⟩ = λ̄` ((16), p. 8). -/
def LimitParams {K : ℕ} (lamBar : ℝ) (muBar : Fin K → ℝ) : Prop :=
  0 < lamBar ∧ (∀ k, 0 < muBar k) ∧ ∑ k, muBar k = lamBar

/-- **Assumption 2.2** (heavy traffic, p. 8): `λⁿ = nλ̄ + √n λ̂ + o(√n)`,
`μⁿ_k = nμ̄_k + √n μ̂_k + o(√n)`, with `λ̄, μ̄_k > 0` and `⟨μ̄, 𝟏⟩ = λ̄` (16). The `o(√n)` terms
are encoded as `(λⁿ − nλ̄)/√n → λ̂` and `(μⁿ_k − nμ̄_k)/√n → μ̂_k`. -/
def HeavyTraffic {K : ℕ} (lam : ℕ → ℝ) (mu : ℕ → Fin K → ℝ) (lamBar lamHat : ℝ)
    (muBar muHat : Fin K → ℝ) : Prop :=
  LimitParams lamBar muBar ∧
  Tendsto (fun n : ℕ => (lam n - n * lamBar) / Real.sqrt n) atTop (𝓝 lamHat) ∧
  ∀ k, Tendsto (fun n : ℕ => (mu n k - n * muBar k) / Real.sqrt n) atTop (𝓝 (muHat k))

/-- A **delay function** (§3.1, p. 9): `τ : [0, ∞) → [0, ∞)^K`, componentwise non-decreasing,
with `τ_k(t) ≤ t` for all `k` and `t > 0`. -/
def DelayFunction {K : ℕ} (τ : ℝ → Fin K → ℝ) : Prop :=
  (∀ t, 0 ≤ t → ∀ k, 0 ≤ τ t k) ∧
  (∀ k, MonotoneOn (fun t => τ t k) (Set.Ici 0)) ∧
  (∀ t, 0 < t → ∀ k, τ t k ≤ t)

/-- **Assumption 3.1** (p. 9): the delay function `τ` is continuous and there is an increasing
sequence `(T_m)_{m ≥ 0}` with `T₀ = 0` and `T_m → ∞` such that `τ_k(t) ≤ T_m` for all
`t ∈ [0, T_{m+1}]` and all `k`. -/
def Assumption31 {K : ℕ} (τ : ℝ → Fin K → ℝ) : Prop :=
  DelayFunction τ ∧ ContinuousOn τ (Set.Ici 0) ∧
  ∃ T : ℕ → ℝ, StrictMono T ∧ T 0 = 0 ∧ Tendsto T atTop atTop ∧
    ∀ m : ℕ, ∀ t ∈ Set.Icc 0 (T (m + 1)), ∀ k, τ t k ≤ T m

/-- **Estimator function** `Ψⁿ` ((22)–(24), p. 10), taken on real-valued paths so that the
scaled estimator (27) is defined: on its domain `𝔻₀(ℝ₊^K) × 𝔻₀(ℝ^K)` (`IsD0Pair`),
1. for each `t`, `(q, a) ↦ Ψ(q, a)(t)` is measurable for the product σ-algebra on paths;
2. `Ψ(q, a)` is RCLL, non-negative and starts at `0` (it maps into `𝔻₀(ℝ₊^K)`);
3. `Ψ(q, a)(t)` depends only on `(q|_{τ(t)}, a|_t)`: if `q'_k = q_k` on `[0, τ_k(t)]` for every
   `k` and `a' = a` on `[0, t]`, then `Ψ(q', a')(t) = Ψ(q, a)(t)`. -/
def IsEstimator {K : ℕ} (τ : ℝ → Fin K → ℝ) (Ψ : Path K → Path K → Path K) : Prop :=
  (∀ t, Measurable (fun p : {p : Path K × Path K // IsD0Pair p.1 p.2} => Ψ p.1.1 p.1.2 t)) ∧
  (∀ q a, IsD0Pair q a →
    (∀ k, IsCadlag (fun t => Ψ q a t k)) ∧ Ψ q a 0 = 0 ∧
    ∀ t, 0 ≤ t → ∀ k, 0 ≤ Ψ q a t k) ∧
  (∀ q a q' a', IsD0Pair q a → IsD0Pair q' a' → ∀ t, 0 ≤ t →
    (∀ k, ∀ s ∈ Set.Icc 0 (τ t k), q' s k = q s k) → (∀ s ∈ Set.Icc 0 t, a' s = a s) →
    Ψ q' a' t = Ψ q a t)

/-- The estimated-queue-length function `Φⁿ`, defined from `Ψⁿ` by (24), p. 10:
`Φⁿ_k(q, a)(t) = q_k(τ_k(t)) + a_k[τ_k(t), t] − μⁿ_k (t − τ_k(t)) + Ψⁿ_k(q, a)(t)`. -/
def Phi {K : ℕ} (mu : Fin K → ℝ) (τ : ℝ → Fin K → ℝ) (Ψ : Path K → Path K → Path K)
    (q a : Path K) : Path K :=
  fun t k => q (τ t k) k + (a t k - a (τ t k) k) - mu k * (t - τ t k) + Ψ q a t k

/-- The exogenous arrival count `Xⁿ(t) = X(λⁿ t)` (§2.1, p. 7), where `X` is the renewal
process of the interarrival times `u`; the `ℕ∞`-valued `renewalCount` is finite whenever the
partial sums diverge, and is converted to `ℕ`. -/
noncomputable def arrivalCount {Ω : Type*} (u : ℕ → Ω → ℝ) (lam : ℝ) (ω : Ω) (t : ℝ) : ℕ :=
  (renewalCount (partialSum (fun i => u i ω)) (lam * t)).toNat

/-- The service count `Sⁿ_k(t) = S_k(μⁿ_k t)` (§2.1, p. 7), with `S_k` the renewal process of
the service times `v k`, converted from `ℕ∞` to `ℕ` as for `arrivalCount`. -/
noncomputable def serviceCount {Ω : Type*} {K : ℕ} (v : Fin K → ℕ → Ω → ℝ) (mu : Fin K → ℝ)
    (k : Fin K) (ω : Ω) (t : ℝ) : ℕ :=
  (renewalCount (partialSum (fun i => v k i ω)) (mu k * t)).toNat

/-- The `i`-th exogenous arrival epoch `σⁿ_i = inf{t ≥ 0 : Xⁿ(t) ≥ i}`, which for positive
interarrival times is `(u 1 + ⋯ + u i)/λⁿ` (p. 11). -/
noncomputable def arrivalEpoch {Ω : Type*} (u : ℕ → Ω → ℝ) (lam : ℝ) (ω : Ω) (i : ℕ) : ℝ :=
  partialSum (fun j => u j ω) i / lam

/-- The busy time `Bⁿ_k(t) = ∫₀ᵗ 1{Q_k(s) > 0} ds` of server `k` ((7), p. 7). -/
noncomputable def busyTime {K : ℕ} (q : Path K) (k : Fin K) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, if 0 < q s k then (1 : ℝ) else 0

/-- The JSEQ routing rule with lexicographic tie-break (p. 11): given the estimates `r`, a job
is routed to queue `k` iff `r_k < r_j` for all `j < k` and `r_k ≤ r_l` for all `l ≥ k`. -/
def RoutedTo {K : ℕ} (r : Fin K → ℝ) (k : Fin K) : Prop :=
  (∀ j, j < k → r k < r j) ∧ (∀ l, k ≤ l → r k ≤ r l)

open Classical in
/-- **One sample path of the `n`-th JSEQ network** (§2.1 (6)–(8), p. 7; §3.2 (24)–(25) and the
routing rule, pp. 10–11), for arrival rate `lam = λⁿ`, service rates `mu = μⁿ`, delay function
`τ` and estimator `Ψ = Ψⁿ`. The queue lengths `q` and routed arrivals `a` satisfy:
* `q(0) = 0` and `a(0) = 0`;
* (8) with (7): `q_k(t) = a_k(t) − Sⁿ_k(Bⁿ_k(t))`, `Bⁿ_k(t) = ∫₀ᵗ 1{q_k(s) > 0} ds`, `t ≥ 0`;
* routing: with the estimated queue lengths `R = Φⁿ(q, a)` of (24)–(25), job `i` (arriving at
  `σⁿ_i`) goes to the queue `k` selected by `RoutedTo` from the left limits `R(σⁿ_i−)`, and
  `a_k(t)` counts the jobs `i ≤ Xⁿ(t)` routed to `k`. In particular `⟨a(t), 𝟏⟩ = Xⁿ(t)` (6). -/
def IsJSEQPath {Ω : Type*} {K : ℕ} (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (lam : ℝ)
    (mu : Fin K → ℝ) (τ : ℝ → Fin K → ℝ) (Ψ : Path K → Path K → Path K) (ω : Ω)
    (q a : Path K) : Prop :=
  q 0 = 0 ∧ a 0 = 0 ∧
  (∀ t, 0 ≤ t → ∀ k, q t k = a t k - serviceCount v (fun j => mu j) k ω (busyTime q k t)) ∧
  (∀ t, 0 ≤ t → ∀ k, a t k =
    (((Finset.Icc 1 (arrivalCount u lam ω t)).filter (fun i =>
      RoutedTo (fun j => Function.leftLim (fun s => Phi mu τ Ψ q a s j)
        (arrivalEpoch u lam ω i)) k)).card : ℝ))

/-- The sample path `ω` has divergent arrival and service partial sums (true almost surely
under `Primitives`, by the strong law of large numbers), so that every count is finite. -/
def GoodPath {Ω : Type*} {K : ℕ} (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (ω : Ω) : Prop :=
  Tendsto (partialSum (fun i => u i ω)) atTop atTop ∧
  ∀ k, Tendsto (partialSum (fun i => v k i ω)) atTop atTop

/-- The processes `(Qⁿ, Aⁿ)` form the `n`-th JSEQ network: every sample path with divergent
arrival and service partial sums (`GoodPath`, an event of probability one under `Primitives`)
satisfies `IsJSEQPath`. On the complementary null event infinitely many jobs arrive in a
bounded time and the model is not defined; the processes are unconstrained there. -/
def IsJSEQNetwork {Ω : Type*} {K : ℕ} (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (lam : ℝ)
    (mu : Fin K → ℝ) (τ : ℝ → Fin K → ℝ) (Ψ : Path K → Path K → Path K)
    (Q A : Ω → Path K) : Prop :=
  ∀ ω, GoodPath u v ω → IsJSEQPath u v lam mu τ Ψ ω (Q ω) (A ω)

/-! ### Diffusion scaling ((9)–(13), p. 8; (26)–(30), pp. 11–12) -/

/-- `Q̂ⁿ_k(t) = Qⁿ_k(t)/√n` (9). -/
noncomputable def Qhat {Ω : Type*} {K : ℕ} (n : ℕ) (Q : Ω → Path K) : Ω → Path K :=
  fun ω t k => Q ω t k / Real.sqrt n

/-- `Âⁿ_k(t) = (Aⁿ_k(t) − μⁿ_k t)/√n` (11). -/
noncomputable def Ahat {Ω : Type*} {K : ℕ} (n : ℕ) (mu : Fin K → ℝ) (A : Ω → Path K) :
    Ω → Path K :=
  fun ω t k => (A ω t k - mu k * t) / Real.sqrt n

/-- `X̂ⁿ(t) = (Xⁿ(t) − ⟨μⁿ, 𝟏⟩ t)/√n` (10): centred at `⟨μⁿ, 𝟏⟩ t`, not at `λⁿ t`. -/
noncomputable def Xhat {Ω : Type*} {K : ℕ} (n : ℕ) (u : ℕ → Ω → ℝ) (lam : ℝ)
    (mu : Fin K → ℝ) : Ω → ℝ → ℝ :=
  fun ω t => ((arrivalCount u lam ω t : ℝ) - (∑ k, mu k) * t) / Real.sqrt n

/-- `Ŝⁿ_k(t) = (Sⁿ_k(t) − μⁿ_k t)/√n` (12). -/
noncomputable def Shat {Ω : Type*} {K : ℕ} (n : ℕ) (v : Fin K → ℕ → Ω → ℝ)
    (mu : Fin K → ℝ) : Ω → Path K :=
  fun ω t k => ((serviceCount v mu k ω t : ℝ) - mu k * t) / Real.sqrt n

/-- `L̂ⁿ_k(t) = μⁿ_k (t − Bⁿ_k(t))/√n` (13), the scaled idleness process. -/
noncomputable def Lhat {Ω : Type*} {K : ℕ} (n : ℕ) (mu : Fin K → ℝ) (Q : Ω → Path K) :
    Ω → Path K :=
  fun ω t k => mu k * (t - busyTime (Q ω) k t) / Real.sqrt n

/-- The scaled estimator `Ψ̂ⁿ(q, a)(t) = Ψⁿ(√n q, √n a + μⁿ ι)(t)/√n` (27). -/
noncomputable def PsiHat {K : ℕ} (n : ℕ) (mu : Fin K → ℝ) (Ψ : Path K → Path K → Path K) :
    Path K → Path K → Path K :=
  fun q a t k =>
    Ψ (fun s j => Real.sqrt n * q s j) (fun s j => Real.sqrt n * a s j + mu j * s) t k /
      Real.sqrt n

/-- The scaled estimated queue lengths `R̂ⁿ = Rⁿ/√n = Φⁿ(Qⁿ, Aⁿ)/√n` (29). -/
noncomputable def Rhat {Ω : Type*} {K : ℕ} (n : ℕ) (mu : Fin K → ℝ) (τ : ℝ → Fin K → ℝ)
    (Ψ : Path K → Path K → Path K) (Q A : Ω → Path K) : Ω → Path K :=
  fun ω t k => Phi mu τ Ψ (Q ω) (A ω) t k / Real.sqrt n

/-- The scaled estimated idleness `M̂ⁿ = Mⁿ/√n = Ψⁿ(Qⁿ, Aⁿ)/√n` (30). -/
noncomputable def Mhat {Ω : Type*} {K : ℕ} (n : ℕ) (Ψ : Path K → Path K → Path K)
    (Q A : Ω → Path K) : Ω → Path K :=
  fun ω t k => Ψ (Q ω) (A ω) t k / Real.sqrt n

end JSEQDelay.Diffusion


