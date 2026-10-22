-- Prove2me | Definitions.Def_ForkJoinCtrl_Tracking_Model
-- name    : ForkJoinCtrl_Tracking_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:39.686987+00:00
-- url     : https://prove2.me/theorems/e1c4543e-2399-42c4-b79f-f76c91f17f1d
-- title:
--   §2.1–§3.2, pp. 6–9 — stochastic primitives, Assumptions 1–2, admissible runs (Definition 1) started empty, and the diffusion scalings
-- statement:
--   On a probability space $(\Omega,\mathcal F,\mathbf P)$ the **primitives** are the sequences $\bar u_{jn}$ (inter-arrival times of type $j$ at unit rate), $v_{kn}$ and $v_{ijn}$ (service times, $i\in\mathcal I_j$), $n\ge 1$: almost surely strictly positive, i.i.d. within each sequence, and all mutually independent, with
--
--   $$\mathbf E[\bar u_{j1}]=1,\ \operatorname{Var}(\bar u_{j1})=\beta_j^2,\quad \mathbf E[v_{k1}]=\tfrac1{\mu_k},\ \operatorname{Var}(v_{k1})=\tfrac{\sigma_k^2}{\mu_k^2},\quad \mathbf E[v_{ij1}]=\tfrac1{\mu_{ij}},\ \operatorname{Var}(v_{ij1})=\tfrac{\sigma_{ij}^2}{\mu_{ij}^2}.$$
--
--   System $r$ has arrival rates $\lambda^r_j>0$ and inter-arrival times $\bar u_{jn}/\lambda^r_j$; $A^r_j$, $S_k$, $S_{ij}$ are the renewal counting processes of §2.1 (the service processes do not depend on $r$).
--
--   1. **Assumption 1** (p. 8): there is $\bar\alpha>0$ with $\mathbf E[e^{\alpha\bar u_{j1}}],\mathbf E[e^{\alpha v_{k1}}],\mathbf E[e^{\alpha v_{ij1}}]<\infty$ for all $\alpha\in(-\bar\alpha,\bar\alpha)$.
--   2. **Assumption 2** (pp. 8–9): $\lambda^r_j\to\lambda_j$; $\sum_{j\in\mathcal J_i}\lambda_j/\mu_{ij}=1$; $r(\sum_{j\in\mathcal J_i}\lambda^r_j/\mu_{ij}-1)\to\theta_i\in\mathbb R$; and $r(\lambda^r_j-\mu_k)\to\theta_k\in\mathbb R$ for heavy-traffic dedicated servers $k\in\mathcal K^H_j$, $\to-\infty$ for light-traffic ones $k\in\mathcal K^L_j$.
--
--   A **run** of system $r$ under an admissible policy (Definition 1) consists of busy-time processes $T_k$, $T_{ij}$, queue processes $Q_k$, $Q_{ij}$, join-buffer processes $Q^{(1)}_k$, $Q^{(1)}_{ij}$ and job counts $N_j$ satisfying (2)–(6), (7a), (7b) and the empty initial state $Q=Q^{(1)}=0$ at time $0$: queue balance (3), the join equations (4), head-of-line service (5), work conservation (6) and continuity and monotonicity of the cumulative busy times $T_k$ and $T_{ij}$. The workload is $W^r_i(t)=\sum_{j\in\mathcal J_i}Q^r_{ij}(t)/\mu_{ij}$ (12) and the diffusion scalings are $\hat N^r_j(t)=r\cdot r^{-2}N^r_j(r^2t)$, $\hat Q^r_k(t)=r\cdot r^{-2}Q^r_k(r^2t)$, $\hat W^r_i(t)=r\cdot r^{-2}W^r_i(r^2t)$.
--
--   **Formalization Note** Time is real and only $t\ge 0$ matters; systems are indexed by $r\in\mathbb N$ (the extra system $r=0$ does not affect limits). The work-conservation rule (6) "the idle time increases iff the buffers are empty" is encoded pathwise: on every $[s,t]$ throughout which the buffers are nonempty the idle time is constant, and on every $[s,t)$ throughout which they are empty it grows by $t-s$. (4b) is written as "some join buffer of type $j$ is empty", which is equivalent given (3c). The pathwise conditions are required for $\mathbf P$-almost every $\omega$ (so the junk value of the counting map on a null set cannot make runs impossible); (7a) is measurability of $\omega\mapsto T_{ij}(t)$ for every $t\ge0$. The primitives are required to have finite second moments, since the paper's variances are real numbers.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, pp. 6–9, §2.1, §2.2 (2)–(7), Definition 1, §3.1, Assumptions 1–2, §3.2 (10)–(12)

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP

namespace ForkJoinCtrl.Tracking

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Topology

/-!
Özkan, arXiv:2002.01496v1, §2.1–§2.2 (pp. 6–7), §3.1 (pp. 8–9), §3.2 (p. 9): the stochastic
primitives, Assumptions 1–2, the sequence of systems `r`, admissible runs (Definition 1) with the
empty initial state, and the diffusion scalings (10)–(12).

Time is real; only `t ≥ 0` matters. The sequence of systems is indexed by `r : ℕ` (the paper's
`r ∈ ℕ₊`; the system `r = 0` only adds one irrelevant term to every limit `r → ∞`).
-/

variable {N : Network}

/-- Index set of all stochastic primitives: `arr j n` is `ū_jn`, `ded k n` is `v_kn`, `sh i j n`
is `v_ijn`. -/
inductive PrimIdx (N : Network) where
  | arr (j : Fin N.J) (n : ℕ)
  | ded (k : Fin N.K) (n : ℕ)
  | sh (i : Fin N.I) (j : Fin N.J) (n : ℕ)

/-- The primitives that exist in the paper: index `n ∈ ℕ₊`, and `v_ijn` only for `i ∈ ℐ_j`. -/
def PrimIdx.Valid : PrimIdx N → Prop
  | .arr _ n => 1 ≤ n
  | .ded _ n => 1 ≤ n
  | .sh i j n => N.P i j = true ∧ 1 ≤ n

/-- Evaluation of the family of primitives at an index. -/
def primEval {Ω : Type*} (ubar : Fin N.J → ℕ → Ω → ℝ) (v : Fin N.K → ℕ → Ω → ℝ)
    (vs : Fin N.I → Fin N.J → ℕ → Ω → ℝ) : PrimIdx N → Ω → ℝ
  | .arr j n => ubar j n
  | .ded k n => v k n
  | .sh i j n => vs i j n

/-- The stochastic model of §2.1 and §3.1 on one probability space `(Ω, P)`.

* `ubar j n = ū_jn`, `v k n = v_kn`, `vs i j n = v_ijn` (`n ≥ 1`; the value at `n = 0` is unused):
  almost surely strictly positive random variables, i.i.d. within each sequence, and all of them mutually
  independent (p. 6);
* `E[ū_j1] = 1`, `Var(ū_j1) = β_j²`; `E[v_k1] = 1/µ_k`, `Var(v_k1) = σ_k²/µ_k²`;
  `E[v_ij1] = 1/µ_ij`, `Var(v_ij1) = σ_ij²/µ_ij²` (`σ²` is the squared coefficient of variation),
  with finite second moments;
* `lamr r j = λ^r_j > 0`, the arrival rates of system `r` (p. 8);
* `thetaI i = θ_i`, `thetaK k = θ_k` (for heavy `k`) and the heavy/light split `heavy k`
  (`k ∈ 𝒦^H_j` iff `heavy k = true`) of Assumption 2 (p. 9); the split is pinned down by
  `Model.Assumption2`. -/
structure Model (N : Network) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  ubar : Fin N.J → ℕ → Ω → ℝ
  v : Fin N.K → ℕ → Ω → ℝ
  vs : Fin N.I → Fin N.J → ℕ → Ω → ℝ
  lamr : ℕ → Fin N.J → ℝ
  thetaI : Fin N.I → ℝ
  thetaK : Fin N.K → ℝ
  heavy : Fin N.K → Bool
  isProb : IsProbabilityMeasure P
  meas : ∀ x : PrimIdx N, Measurable (primEval ubar v vs x)
  ubar_pos : ∀ j n, 1 ≤ n → ∀ᵐ ω ∂P, 0 < ubar j n ω
  v_pos : ∀ k n, 1 ≤ n → ∀ᵐ ω ∂P, 0 < v k n ω
  vs_pos : ∀ i j n, N.P i j = true → 1 ≤ n → ∀ᵐ ω ∂P, 0 < vs i j n ω
  indep : iIndepFun (fun x : {x : PrimIdx N // x.Valid} => primEval ubar v vs x.1) P
  ubar_ident : ∀ j n, 1 ≤ n → IdentDistrib (ubar j n) (ubar j 1) P P
  v_ident : ∀ k n, 1 ≤ n → IdentDistrib (v k n) (v k 1) P P
  vs_ident : ∀ i j n, N.P i j = true → 1 ≤ n → IdentDistrib (vs i j n) (vs i j 1) P P
  ubar_L2 : ∀ j, MemLp (ubar j 1) 2 P
  v_L2 : ∀ k, MemLp (v k 1) 2 P
  vs_L2 : ∀ i j, N.P i j = true → MemLp (vs i j 1) 2 P
  ubar_mean : ∀ j, ∫ ω, ubar j 1 ω ∂P = 1
  ubar_var : ∀ j, variance (ubar j 1) P = N.beta2 j
  v_mean : ∀ k, ∫ ω, v k 1 ω ∂P = 1 / N.muK k
  v_var : ∀ k, variance (v k 1) P = N.sig2K k / N.muK k ^ 2
  vs_mean : ∀ i j, N.P i j = true → ∫ ω, vs i j 1 ω ∂P = 1 / N.mu i j
  vs_var : ∀ i j, N.P i j = true → variance (vs i j 1) P = N.sig2 i j / N.mu i j ^ 2
  lamr_pos : ∀ r j, 0 < lamr r j

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Assumption 1 (Moment), p. 8: there is `ᾱ > 0` such that for all `α ∈ (−ᾱ, ᾱ)`,
`E[e^{α ū_j1}] < ∞`, `E[e^{α v_k1}] < ∞`, `E[e^{α v_ij1}] < ∞` for all `j`, `k ∈ 𝒦_j`, `i ∈ ℐ_j`. -/
def Model.Assumption1 (M : Model N Ω P) : Prop :=
  ∃ αbar : ℝ, 0 < αbar ∧ ∀ α ∈ Set.Ioo (-αbar) αbar,
    (∀ j, Integrable (fun ω => Real.exp (α * M.ubar j 1 ω)) P) ∧
    (∀ k, Integrable (fun ω => Real.exp (α * M.v k 1 ω)) P) ∧
    (∀ i j, N.P i j = true → Integrable (fun ω => Real.exp (α * M.vs i j 1 ω)) P)

/-- Assumption 2 (Asymptotic Regime), pp. 8–9:
1. `λ^r_j → λ_j` for all `j`;
2. `∑_{j ∈ 𝒥_i} λ_j/µ_ij = 1` for all `i`;
3. `r((∑_{j ∈ 𝒥_i} λ^r_j/µ_ij) − 1) → θ_i ∈ ℝ` for all `i`;
4. `r(λ^r_j − µ_k) → θ_k ∈ ℝ ∪ {−∞}` for all `j` and `k ∈ 𝒦_j`: for a heavy-traffic server
   (`heavy k = true`, `k ∈ 𝒦^H_j`) the limit is the real number `thetaK k`; for a light-traffic
   server (`k ∈ 𝒦^L_j`) the sequence tends to `−∞`. -/
def Model.Assumption2 (M : Model N Ω P) : Prop :=
  (∀ j, Tendsto (fun r : ℕ => M.lamr r j) atTop (𝓝 (N.lam j))) ∧
  (∀ i, ∑ j ∈ N.Ji i, N.lam j / N.mu i j = 1) ∧
  (∀ i, Tendsto (fun r : ℕ => (r : ℝ) * ((∑ j ∈ N.Ji i, M.lamr r j / N.mu i j) - 1)) atTop
    (𝓝 (M.thetaI i))) ∧
  (∀ k, (M.heavy k = true →
      Tendsto (fun r : ℕ => (r : ℝ) * (M.lamr r (N.own k) - N.muK k)) atTop (𝓝 (M.thetaK k))) ∧
    (M.heavy k = false →
      Tendsto (fun r : ℕ => (r : ℝ) * (M.lamr r (N.own k) - N.muK k)) atTop atBot))

/-- `A^r_j(t) = sup{n ∈ ℕ : U^r_j(n) ≤ t}`, the number of type `j` arrivals by time `t` in system
`r`, where `U^r_j(n) = ∑_{l=1}^n u^r_jl` and `u^r_jl = ū_jl / λ^r_j` (pp. 6, 8). -/
noncomputable def Model.A (M : Model N Ω P) (r : ℕ) (j : Fin N.J) (ω : Ω) (t : ℝ) : ℕ :=
  count (fun l => M.ubar j l ω / M.lamr r j) t

/-- `V_k(n) = ∑_{l=1}^n v_kl` (p. 6). -/
def Model.V (M : Model N Ω P) (k : Fin N.K) (ω : Ω) (n : ℕ) : ℝ :=
  partialSum (fun l => M.v k l ω) n

/-- `S_k(t) = sup{n ∈ ℕ : V_k(n) ≤ t}` (p. 6); it does not depend on `r`. -/
noncomputable def Model.S (M : Model N Ω P) (k : Fin N.K) (ω : Ω) (t : ℝ) : ℕ :=
  count (fun l => M.v k l ω) t

/-- `V_ij(n) = ∑_{l=1}^n v_ijl` (p. 6). -/
def Model.Vs (M : Model N Ω P) (i : Fin N.I) (j : Fin N.J) (ω : Ω) (n : ℕ) : ℝ :=
  partialSum (fun l => M.vs i j l ω) n

/-- `S_ij(t) = sup{n ∈ ℕ : V_ij(n) ≤ t}` (p. 6); it does not depend on `r`. -/
noncomputable def Model.Ss (M : Model N Ω P) (i : Fin N.I) (j : Fin N.J) (ω : Ω) (t : ℝ) : ℕ :=
  count (fun l => M.vs i j l ω) t

/-- The processes of one run of a system (§2.2, p. 7), as functions of `ω` and of real time:
`Tk k = T_k`, `Tij i j = T_ij` (cumulative busy times), `Qk k = Q_k`, `Qij i j = Q_ij` (jobs in
front of a server, including the one in service), `Q1k k = Q^{(1)}_k`, `Q1ij i j = Q^{(1)}_ij`
(jobs waiting for the join after a server), and `Nj j = N_j` (type `j` jobs in the system). -/
structure Paths (N : Network) (Ω : Type*) where
  Tk : Fin N.K → Ω → ℝ → ℝ
  Tij : Fin N.I → Fin N.J → Ω → ℝ → ℝ
  Qk : Fin N.K → Ω → ℝ → ℝ
  Qij : Fin N.I → Fin N.J → Ω → ℝ → ℝ
  Q1k : Fin N.K → Ω → ℝ → ℝ
  Q1ij : Fin N.I → Fin N.J → Ω → ℝ → ℝ
  Nj : Fin N.J → Ω → ℝ → ℝ

/-- (2a) `I_k(t) := t − T_k(t)`, the cumulative idle time of dedicated server `k`. -/
def Paths.Ik (X : Paths N Ω) (k : Fin N.K) (ω : Ω) (t : ℝ) : ℝ :=
  t - X.Tk k ω t

/-- (2b) `I_i(t) := t − ∑_{j ∈ 𝒥_i} T_ij(t)`, the cumulative idle time of shared server `i`. -/
def Paths.Ii (X : Paths N Ω) (i : Fin N.I) (ω : Ω) (t : ℝ) : ℝ :=
  t - ∑ j ∈ N.Ji i, X.Tij i j ω t

/-- The idle-time rule (6) for an idle-time path `idle` and an emptiness predicate `empty`:
`idle` is nondecreasing on `[0, ∞)`, `idle(0) = 0`, and `idle(t)` increases if and only if the
buffers are empty, read pathwise as
* (only if) on every interval `[s, t] ⊆ [0, ∞)` throughout which the buffers are not empty,
  `idle(t) = idle(s)`;
* (if) on every interval `[s, t) ⊆ [0, ∞)` throughout which the buffers are empty,
  `idle(t) − idle(s) = t − s`. -/
def IdleRule (idle : ℝ → ℝ) (empty : ℝ → Prop) : Prop :=
  MonotoneOn idle (Set.Ici 0) ∧ idle 0 = 0 ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → (∀ u ∈ Set.Icc s t, ¬ empty u) → idle t = idle s) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → (∀ u ∈ Set.Ico s t, empty u) → idle t - idle s = t - s)

/-- The sample path `ω` of `X` satisfies the dynamics of system `r` under an admissible policy
(Definition 1, p. 7) started empty (p. 9): for all `t ≥ 0`,
* (3a) `Q_k(t) = Q_k(0) + A^r_j(t) − S_k(T_k(t))` for `k ∈ 𝒦_j`;
* (3b) `Q_ij(t) = Q_ij(0) + A^r_j(t) − S_ij(T_ij(t))` for `i ∈ ℐ_j`;
* (3c) `Q_k, Q_ij, Q^{(1)}_k, Q^{(1)}_ij ≥ 0`;
* (4a) `N_j(t) = Q_k(t) + Q^{(1)}_k(t) = Q_ij(t) + Q^{(1)}_ij(t)` for `k ∈ 𝒦_j`, `i ∈ ℐ_j`;
* (4b) `min_{k ∈ 𝒦_j} Q^{(1)}_k(t) ∧ min_{i ∈ ℐ_j} Q^{(1)}_ij(t) = 0`, written (given (3c)) as: one
  of these join buffers is empty;
* (5a) `V_k(S_k(T_k(t))) ≤ T_k(t) < V_k(S_k(T_k(t)) + 1)`;
* (5b) `V_ij(S_ij(T_ij(t))) ≤ T_ij(t) < V_ij(S_ij(T_ij(t)) + 1)`;
* (6a) the rule `IdleRule` for `I_k` with "empty" meaning `Q_k = 0`;
* (6b) the rule `IdleRule` for `I_i` with "empty" meaning `max_{j ∈ 𝒥_i} Q_ij = 0`, i.e. (given
  (3c)) `Q_ij = 0` for all `j ∈ 𝒥_i`;
* `T_k` is a continuous nondecreasing cumulative busy time on `[0, ∞)`;
* (7b) `T_ij` is continuous and nondecreasing on `[0, ∞)` with `T_ij(0) = 0`;
* empty start: `Q_k(0) = Q_ij(0) = Q^{(1)}_k(0) = Q^{(1)}_ij(0) = 0`. -/
def Paths.IsAdmissibleAt (X : Paths N Ω) (M : Model N Ω P) (r : ℕ) (ω : Ω) : Prop :=
  (∀ k t, 0 ≤ t →
    X.Qk k ω t = X.Qk k ω 0 + (M.A r (N.own k) ω t : ℝ) - (M.S k ω (X.Tk k ω t) : ℝ)) ∧
  (∀ i j t, N.P i j = true → 0 ≤ t →
    X.Qij i j ω t = X.Qij i j ω 0 + (M.A r j ω t : ℝ) - (M.Ss i j ω (X.Tij i j ω t) : ℝ)) ∧
  (∀ k t, 0 ≤ t → 0 ≤ X.Qk k ω t ∧ 0 ≤ X.Q1k k ω t) ∧
  (∀ i j t, N.P i j = true → 0 ≤ t → 0 ≤ X.Qij i j ω t ∧ 0 ≤ X.Q1ij i j ω t) ∧
  (∀ j t, 0 ≤ t →
    (∀ k ∈ N.Kj j, X.Nj j ω t = X.Qk k ω t + X.Q1k k ω t) ∧
    (∀ i ∈ N.Ij j, X.Nj j ω t = X.Qij i j ω t + X.Q1ij i j ω t)) ∧
  (∀ j t, 0 ≤ t →
    (∃ k ∈ N.Kj j, X.Q1k k ω t = 0) ∨ (∃ i ∈ N.Ij j, X.Q1ij i j ω t = 0)) ∧
  (∀ k t, 0 ≤ t →
    M.V k ω (M.S k ω (X.Tk k ω t)) ≤ X.Tk k ω t ∧
    X.Tk k ω t < M.V k ω (M.S k ω (X.Tk k ω t) + 1)) ∧
  (∀ i j t, N.P i j = true → 0 ≤ t →
    M.Vs i j ω (M.Ss i j ω (X.Tij i j ω t)) ≤ X.Tij i j ω t ∧
    X.Tij i j ω t < M.Vs i j ω (M.Ss i j ω (X.Tij i j ω t) + 1)) ∧
  (∀ k, IdleRule (X.Ik k ω) (fun u => X.Qk k ω u = 0)) ∧
  (∀ i, IdleRule (X.Ii i ω) (fun u => ∀ j ∈ N.Ji i, X.Qij i j ω u = 0)) ∧
  (∀ k, ContinuousOn (X.Tk k ω) (Set.Ici 0) ∧ MonotoneOn (X.Tk k ω) (Set.Ici 0)) ∧
  (∀ i j, N.P i j = true →
    ContinuousOn (X.Tij i j ω) (Set.Ici 0) ∧ MonotoneOn (X.Tij i j ω) (Set.Ici 0) ∧
    X.Tij i j ω 0 = 0) ∧
  (∀ k, X.Qk k ω 0 = 0 ∧ X.Q1k k ω 0 = 0) ∧
  (∀ i j, N.P i j = true → X.Qij i j ω 0 = 0 ∧ X.Q1ij i j ω 0 = 0)

/-- A run of system `r` under an admissible scheduling policy (Definition 1, p. 7), started empty
(p. 9): the paths satisfy the dynamics for `P`-almost every `ω`, and (7a) every `T_ij(t)`,
`t ≥ 0`, is `𝓕`-measurable (so anticipating policies are allowed). -/
structure Run (M : Model N Ω P) (r : ℕ) extends Paths N Ω where
  meas_T : ∀ i j, N.P i j = true → ∀ t : ℝ, 0 ≤ t → Measurable (fun ω => Tij i j ω t)
  adm : ∀ᵐ ω ∂P, toPaths.IsAdmissibleAt M r ω

variable {M : Model N Ω P} {r : ℕ}

/-- (12) The workload of shared server `i`: `W^r_i(t) := ∑_{j ∈ 𝒥_i} Q^r_ij(t) / µ_ij`. -/
noncomputable def Paths.W (X : Paths N Ω) (i : Fin N.I) (ω : Ω) (t : ℝ) : ℝ :=
  ∑ j ∈ N.Ji i, X.Qij i j ω t / N.mu i j

/-- The unscaled LP parameter `(Q^r_k(t), k; W^r_i(t), i)` of system `r` at time `t` (p. 13). -/
noncomputable def Paths.b (X : Paths N Ω) (ω : Ω) (t : ℝ) : LPParam N :=
  (fun k => X.Qk k ω t, fun i => X.W i ω t)

/-- (10a), (11a): `N̂^r_j(t) := r N̄^r_j(t) = r · r^{−2} N^r_j(r² t)`. -/
noncomputable def Run.Nhat (X : Run M r) (j : Fin N.J) (ω : Ω) (t : ℝ) : ℝ :=
  (r : ℝ) * (((r : ℝ) ^ 2)⁻¹ * X.Nj j ω ((r : ℝ) ^ 2 * t))

/-- (10e), (11e): `Q̂^r_k(t) := r · r^{−2} Q^r_k(r² t)`. -/
noncomputable def Run.Qhat (X : Run M r) (k : Fin N.K) (ω : Ω) (t : ℝ) : ℝ :=
  (r : ℝ) * (((r : ℝ) ^ 2)⁻¹ * X.Qk k ω ((r : ℝ) ^ 2 * t))

/-- p. 9: `Ŵ^r_i(t) := r W̄^r_i(t) = r · r^{−2} W^r_i(r² t)`. -/
noncomputable def Run.What (X : Run M r) (i : Fin N.I) (ω : Ω) (t : ℝ) : ℝ :=
  (r : ℝ) * (((r : ℝ) ^ 2)⁻¹ * X.W i ω ((r : ℝ) ^ 2 * t))

/-- The diffusion-scaled LP parameter `(Q̂^r_k(t), k ∈ 𝒦; Ŵ^r_i(t), i ∈ ℐ)` (p. 19). -/
noncomputable def Run.bhat (X : Run M r) (ω : Ω) (t : ℝ) : LPParam N :=
  (fun k => X.Qhat k ω t, fun i => X.What i ω t)

end ForkJoinCtrl.Tracking


