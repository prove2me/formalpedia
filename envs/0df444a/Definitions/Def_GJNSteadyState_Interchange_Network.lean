-- Prove2me | Definitions.Def_GJNSteadyState_Interchange_Network
-- name    : GJNSteadyState_Interchange_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:08.747008+00:00
-- url     : https://prove2.me/theorems/08f4d4a2-f54f-4aff-bdb7-e9665ad889f3
-- title:
--   §2.1, pp. 6–8 — generalized Jackson network: primitives F_A, F_S, P, assumptions (1)–(2), rates α, μ, λ, ρ, workload vector w
-- statement:
--   A **generalized Jackson network** (GJN) has $J$ single-server stations $1,\dots,J$, each serving its jobs first-in-first-out.
--
--   1. **Arrivals.** Let $\mathcal J$ be the set of stations that receive external arrivals. For $j\in\mathcal J$ the interarrival times $a_j(1),a_j(2),\dots$ are i.i.d. with law $F_{A,j}$, a law of a strictly positive time. The external arrival rate is $\alpha_j = 1/\mathbb E[a_j(1)]$ for $j\in\mathcal J$ and $\alpha_j=0$ otherwise.
--   2. **Service.** The service times $v_j(1),v_j(2),\dots$ at station $j$ are i.i.d. with law $F_{S,j}$, strictly positive, with mean $m_j=\mathbb E[v_j(1)]$ and service rate $\mu_j = 1/m_j$; $M=\mathrm{diag}(m_1,\dots,m_J)$.
--   3. **Variability.** $c^2_{a,j} = \mathrm{Var}(a_j(1))\,\alpha_j^2$ for $j\in\mathcal J$ ($0$ otherwise) and $c^2_{s,j} = \mathrm{Var}(v_j(1))\,\mu_j^2$.
--   4. **Routing.** A job completing service at $j$ is routed to station $k$ with probability $p_{jk}$ and leaves with probability $1-\sum_k p_{jk}$. The matrix $P=(p_{jk})$ is substochastic ($p_{jk}\ge 0$, $\sum_k p_{jk}\le 1$) with spectral radius less than one.
--   5. **Residual-time condition** (1)–(2). There are $\theta^*>0$ and $C<\infty$ such that for every $z\ge 0$
--   $$\mathbb E\big[e^{\theta^*(a_j(1)-z)}\,\big|\,a_j(1)>z\big]\le C \quad (j\in\mathcal J),\qquad \mathbb E\big[e^{\theta^*(v_j(1)-z)}\,\big|\,v_j(1)>z\big]\le C\quad(\text{all }j).$$
--   In particular the interarrival and service times have finite exponential moments.
--
--   From these data one defines the effective arrival rates $\lambda = [I-P']^{-1}\alpha$ (the solution of the traffic equation $\lambda=\alpha+P'\lambda$), the traffic intensities $\rho_j = \lambda_j/\mu_j = \lambda_j m_j$, and the workload vector $w = e'[I-P']^{-1}$, i.e. $w_j = \sum_i ([I-P']^{-1})_{ij}$. The network is **critically loaded** when $\rho_j=1$ for every $j$. The file also fixes the residual-life law of a positive time given its elapsed age, the law of one routing decision, and the extended state space $\mathcal X = \mathbb Z_+^J\times\mathbb R_+^{2J}$ of states $(z,a,v)$: queue lengths, elapsed interarrival times and elapsed service times.
--
--   These are the objects every result of the paper is stated about.
--
--   **Formalization Note** Stations are `Fin J`; $P'$ is `Pᵀ`. The spectral-radius condition is written $P^m\to 0$. Condition (1)–(2) is stated in the equivalent form $\mathbb E[e^{\theta^*(a-z)};\,a>z]\le C\,\mathbb P(a>z)$ for all $z\ge0$, which is the conditional bound wherever the conditioning event has positive probability and is empty otherwise. For uniformity every station carries a law `FA j`, which for $j\notin\mathcal J$ is a dummy (never used: such a station has no external arrivals); `IsGJN` asks every `FA j` and `FS j` to be a probability law on $(0,\infty)$. The page prints "$\mathrm{var}[a_j^2(1)]\alpha_j^2$" and "$\rho = M^{-1}\lambda = M^{-1}[I-P']\alpha$"; the intended $\mathrm{Var}[a_j(1)]\alpha_j^2$ and $\rho_j=\lambda_j m_j$ with $\lambda=[I-P']^{-1}\alpha$ are used. The residual law at an age $a$ with $\mathbb P(X>a)=0$ is set to the point mass at $0$ (such ages are not reachable). The workload is stored as a nonnegative real (`toNNReal`), which is exact since $w\ge 0$. The carrier `State J` stores the elapsed times as reals; the predicate `InStateSpace` cuts out $\mathcal X$ (elapsed times $\ge 0$), and every statement that quantifies over initial states or initial laws is restricted to it.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, pp. 6–8, Section 2.1 (assumptions (1)–(3)); p. 11 (w = e′[I − P′]⁻¹); p. 12 (critical network)

import Mathlib

open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-!
Gamarnik–Zeevi (2006), §2.1, pp. 6–8: the parameters of a generalized Jackson network (GJN)
with `J` single-server stations, indexed by `Fin J` (paper station `j` is Lean index `j − 1`).
Vectors are column vectors `Fin J → ℝ`; `Pᵀ` is the paper's `P′`.
-/

/-- The parameters `(F_{A,j}, F_{S,j}, P)` of a generalized Jackson network (§2.1, pp. 6–7):
* `arrSet` is the set `𝒥 = {j : α_j > 0}` of stations with external arrivals;
* `FA j` is the law `F_{A,j}` of the interarrival times `a_j(1), a_j(2), …` (only used for
  `j ∈ arrSet`; for `j ∉ arrSet` it is a dummy law and the station has no external arrivals);
* `FS j` is the law `F_{S,j}` of the service times `v_j(1), v_j(2), …`;
* `P = (p_jk)` is the routing matrix: a job completing service at `j` goes to `k` with
  probability `p_jk` and leaves with probability `1 − Σ_k p_jk`.
The probabilistic assumptions are collected separately in `Network.IsGJN`. -/
structure Network (J : ℕ) where
  arrSet : Finset (Fin J)
  FA : Fin J → Measure ℝ
  FS : Fin J → Measure ℝ
  P : Matrix (Fin J) (Fin J) ℝ

/-- The standing assumptions of §2.1 (pp. 6–8) on a GJN:
1. every `F_{A,j}` and `F_{S,j}` is a probability law of a strictly positive time;
2. conditions (1)–(2) (p. 7): there are `θ* > 0` and `C < ∞` such that for every `z ≥ 0`,
   `E[exp(θ*(a_j(1) − z)) ; a_j(1) > z] ≤ C · P(a_j(1) > z)` for `j ∈ 𝒥`, and likewise for
   `v_j(1)` and every `j`; i.e. `sup_{z ≥ 0} E[exp(θ*(a_j(1) − z)) | a_j(1) > z] ≤ C` over the
   `z` where the conditioning event has positive probability (for `z = 0` this is the finite
   moment generating function `E exp(θ* a_j(1)) ≤ C`);
3. `P` is substochastic: `p_jk ≥ 0`, `Σ_k p_jk ≤ 1`, and its spectral radius is `< 1`,
   written as `Pᵐ → 0`. -/
def Network.IsGJN {J : ℕ} (N : Network J) : Prop :=
  (∀ j, IsProbabilityMeasure (N.FA j)) ∧ (∀ j, N.FA j (Set.Iic 0) = 0) ∧
  (∀ j, IsProbabilityMeasure (N.FS j)) ∧ (∀ j, N.FS j (Set.Iic 0) = 0) ∧
  (∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ,
    (∀ j ∈ N.arrSet, ∀ z : ℝ, 0 ≤ z →
      ∫⁻ a in Set.Ioi z, ENNReal.ofReal (Real.exp (θ * (a - z))) ∂(N.FA j) ≤
        ENNReal.ofReal C * N.FA j (Set.Ioi z)) ∧
    (∀ j, ∀ z : ℝ, 0 ≤ z →
      ∫⁻ v in Set.Ioi z, ENNReal.ofReal (Real.exp (θ * (v - z))) ∂(N.FS j) ≤
        ENNReal.ofReal C * N.FS j (Set.Ioi z))) ∧
  (∀ j k, 0 ≤ N.P j k) ∧ (∀ j, ∑ k, N.P j k ≤ 1) ∧
  Tendsto (fun m : ℕ => N.P ^ m) atTop (𝓝 0)

/-- External arrival rate `α_j = 1/E[a_j(1)]` for `j ∈ 𝒥`, and `α_j = 0` otherwise (p. 6). -/
noncomputable def alpha {J : ℕ} (N : Network J) (j : Fin J) : ℝ :=
  if j ∈ N.arrSet then 1 / ∫ a, a ∂(N.FA j) else 0

/-- Mean service time `m_j = E[v_j(1)]` (p. 7); `M = diag(m)`. -/
noncomputable def meanS {J : ℕ} (N : Network J) (j : Fin J) : ℝ := ∫ v, v ∂(N.FS j)

/-- Service rate `μ_j = 1/m_j` (p. 7). -/
noncomputable def mu {J : ℕ} (N : Network J) (j : Fin J) : ℝ := 1 / meanS N j

/-- Squared coefficient of variation of interarrival times, `c²_{a,j} = Var(a_j(1)) α_j²` for
`j ∈ 𝒥`, and `0` otherwise (p. 7). -/
noncomputable def ca2 {J : ℕ} (N : Network J) (j : Fin J) : ℝ :=
  if j ∈ N.arrSet then
    ((∫ a, a ^ 2 ∂(N.FA j)) - (∫ a, a ∂(N.FA j)) ^ 2) * alpha N j ^ 2
  else 0

/-- Squared coefficient of variation of service times, `c²_{s,j} = Var(v_j(1)) μ_j²` (p. 7). -/
noncomputable def cs2 {J : ℕ} (N : Network J) (j : Fin J) : ℝ :=
  ((∫ v, v ^ 2 ∂(N.FS j)) - (meanS N j) ^ 2) * mu N j ^ 2

/-- Effective arrival rates `λ = [I − P′]⁻¹ α`, the solution of the traffic equation
`λ = α + P′λ` (p. 7). -/
noncomputable def lam {J : ℕ} (N : Network J) : Fin J → ℝ :=
  (1 - N.Pᵀ)⁻¹ *ᵥ alpha N

/-- Traffic intensities `ρ_j = λ_j / μ_j = λ_j m_j` (pp. 7–8). -/
noncomputable def rho {J : ℕ} (N : Network J) (j : Fin J) : ℝ := lam N j * meanS N j

/-- The network is critically loaded: `ρ_j = 1` at every station (§2.3, p. 12). -/
def IsCritical {J : ℕ} (N : Network J) : Prop := ∀ j, rho N j = 1

/-- The workload vector `w = e′[I − P′]⁻¹` (p. 11), a row vector:
`w_j = Σ_i ([I − P′]⁻¹)_{ij}`. -/
noncomputable def wvec {J : ℕ} (N : Network J) : Fin J → ℝ :=
  Matrix.vecMul (fun _ => (1 : ℝ)) (1 - N.Pᵀ)⁻¹

/-- The residual-life law of a law `F` of a positive time, given elapsed time `a`: the law of
`X − a` conditioned on `X > a`, `X ∼ F`. When `F((a, ∞)) = 0` the conditioning is undefined,
and the convention is the point mass at `0`. For `a = 0` and `F` carried by `(0, ∞)` this is
`F` itself. -/
noncomputable def residual (F : Measure ℝ) (a : ℝ) : Measure ℝ :=
  if F (Set.Ioi a) = 0 then Measure.dirac 0
  else (F (Set.Ioi a))⁻¹ • (F.restrict (Set.Ioi a)).map (fun x => x - a)

/-- The law of one routing decision `ψ^j(l)` out of station `j` (p. 7), with values in
`Fin (J + 1)`: value `k.castSucc` means "routed to station `k`" (probability `p_jk`), value
`Fin.last J` means "leaves the network" (probability `1 − Σ_k p_jk`). -/
noncomputable def routeLaw {J : ℕ} (P : Matrix (Fin J) (Fin J) ℝ) (j : Fin J) :
    Measure (Fin (J + 1)) :=
  (∑ k : Fin J, ENNReal.ofReal (P j k) • Measure.dirac k.castSucc) +
    ENNReal.ofReal (1 - ∑ k, P j k) • Measure.dirac (Fin.last J)

/-- The extended state space `𝒳 = ℤ₊^J × ℝ₊^{2J}` (p. 9): a state `(z, a, v)` holds the queue
lengths `z`, the times `a_j` elapsed since the last external arrival to `j`, and the service
times `v_j` already received by the job in service at `j`. -/
abbrev State (J : ℕ) := (Fin J → ℕ) × (Fin J → ℝ) × (Fin J → ℝ)

/-- `x = (z, a, v)` lies in the paper's state space `𝒳 = ℤ₊^J × ℝ₊^{2J}` (p. 9): the elapsed
times `a_j` and `v_j` are nonnegative. (The carrier `State J` uses `ℝ` for these coordinates; a
negative "elapsed time" is not a state of the network.) -/
def InStateSpace {J : ℕ} (x : State J) : Prop := 0 ≤ x.2.1 ∧ 0 ≤ x.2.2

end GJNSteadyState.Interchange


