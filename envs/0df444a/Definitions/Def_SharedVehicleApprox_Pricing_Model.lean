-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Model
-- name    : SharedVehicleApprox_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:56.898754+00:00
-- url     : https://prove2.me/theorems/89c80219-093b-4b95-abaa-68132e813157
-- title:
--   §2.1–§3.4 — states, quantile policies, stationarity (1), objective (2), flows (3), elevated objective (8), Algorithm 1, traffic equations, availabilities, infinite-unit objective
-- statement:
--   This module fixes the model of the shared vehicle system with $m$ units (vehicles) and $n$ nodes (stations), with no travel times (§2.1–§2.3), and the objects of the approximation framework (§3).
--
--   1. **States.** $S_{n,m}=\{x\in\mathbb N_0^n : \sum_i x_i=m\}$, the placements of the $m$ units over the $n$ nodes (reused from the closed Jackson network vocabulary). A ride from $i$ to $j$ moves the system from $x$ to $x-e_i+e_j$.
--   2. **Reward curves.** Given per-ride rewards $I_{ij}$ written as functions of the quantile $q\in[0,1]$, the reward curve is $R_{ij}(q)=q\,I_{ij}(q)$; in particular $R_{ij}(0)=0$.
--   3. **State-dependent policies.** A policy assigns to each state $x\in S_{n,m}$ quantiles $q_{ij}(x)\in[0,1]$, with $q_{ij}(x)=0$ whenever $x_i=0$ (no ride leaves an empty station). A state-independent quantile matrix $q$ is run as the policy $x\mapsto q_{ij}\mathbf 1\{x_i>0\}$.
--   4. **Stationary laws.** Given arrival rates $\varphi_{ij}$, a law $\pi$ is stationary for the policy $q$ if $\pi\ge0$, $\pi$ vanishes off $S_{n,m}$, $\sum_{x\in S_{n,m}}\pi(x)=1$, and at every $x\in S_{n,m}$ the balance equation (1) holds:
--   $$\pi(x)\sum_{i,j}\varphi_{ij}q_{ij}(x)=\sum_{i,j}\pi(x+e_i-e_j)\,\varphi_{ij}\,q_{ij}(x+e_i-e_j),$$
--   where a predecessor $x+e_i-e_j$ with a negative coordinate contributes $0$.
--   5. **Objective and flows.** $\mathrm{Obj}_m(q)=\sum_{x\in S_{n,m}}\pi(x)\sum_{i,j}\varphi_{ij}R_{ij}(q_{ij}(x))$ (2) and $f_{ij,m}(q)=\sum_{x\in S_{n,m}}\pi(x)\varphi_{ij}q_{ij}(x)$ (3).
--   6. **Elevated flow relaxation.** The elevated objective (8) $\widehat{\mathrm{Obj}}(q)=\sum_{i,j}\varphi_{ij}R_{ij}(q_{ij})$; balanced demand $\sum_k\varphi_{ki}q_{ki}=\sum_j\varphi_{ij}q_{ij}$ for all $i$; a quantile matrix is feasible for Algorithm 1 if it lies in $[0,1]^{n\times n}$ and is balanced, and optimal if it is feasible and maximizes $\widehat{\mathrm{Obj}}$ over the feasible set.
--   7. **Connectivity.** The support graph of $q$ has an edge $a\to b$ when $a\ne b$ and $\varphi_{ab}q_{ab}>0$; `SupportConnected` says it is strongly connected.
--   8. **Traffic equations, availabilities.** $r$ solves the traffic equations of $q$ if $\sum_j r_j\varphi_{ji}q_{ji}=r_i\sum_k\varphi_{ik}q_{ik}$ for all $i$; $r_{\max}=\max_j r_j$; $G_m=\sum_{x\in S_{n,m}}\prod_j r_j^{x_j}$; the availability of node $i$ under $\pi$ is $A_{i,m}=\sum_{x\in S_{n,m}}\pi(x)\mathbf 1\{x_i>0\}$; the infinite-unit availability is $A_{i,\infty}=r_i/r_{\max}$, and the infinite-unit objective is $\mathrm{Obj}_\infty(q)=\sum_i A_{i,\infty}\sum_j\varphi_{ij}R_{ij}(q_{ij})$.
--
--   These are the objects of every statement of the mission, from the balance equation to Theorem 15.
--
--   **Formalization Note** Nodes are `Fin n`, so the paper's node $i$ is index $i-1$. Laws are functions on all of $\mathbb N^n$ that vanish off $S_{n,m}$. The predecessor $x+e_i-e_j$ for $i\ne j$ is `moveState x i j` and is used only when $x_j\ge1$; for $i=j$ it is $x$ itself. Decision variables are quantiles; prices and value distributions do not appear.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, pp. 6–16 (PDF 7–17): §2.1 p. 6–7, (1) p. 7, (2)–(3) p. 8, Theorem 2 and Lemma 3 p. 9, (8) p. 13, Algorithm 1 p. 14, balanced demand p. 15, A_m and Obj_∞ p. 16

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace SharedVehicleApprox.Pricing

open Finset QueueingFundamentals.Networks

/-- The reward curve `R_ij(q) = q · I_ij(q)` (p. 8) of the per-ride reward `I_ij`, written as a
function of the quantile `q`. Nodes are `Fin n` (the paper's node `i` is index `i - 1`). -/
def rewardCurve {n : ℕ} (I : Fin n → Fin n → ℝ → ℝ) (i j : Fin n) (q : ℝ) : ℝ :=
  q * I i j q

/-- A state-dependent quantile policy of the `m`-unit system (§2.2, p. 7): at every state
`x ∈ S_{n,m}` each quantile `q_ij(x)` lies in `[0, 1]`, and `q_ij(x) = 0` when `x_i = 0`
(unavailability). Values off `S_{n,m}` are irrelevant. -/
def IsPolicy (n m : ℕ) (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) : Prop :=
  ∀ x ∈ states n m, ∀ i j, 0 ≤ q x i j ∧ q x i j ≤ 1 ∧ (x i = 0 → q x i j = 0)

/-- A state-independent quantile matrix `q` run in the `m`-unit system (§2.3, pp. 8–9): the
quantile `q_ij` is quoted while a unit is present at `i`, and no ride starts at an empty
station. -/
def toPolicy {n : ℕ} (q : Fin n → Fin n → ℝ) : (Fin n → ℕ) → Fin n → Fin n → ℝ :=
  fun x i j => if 0 < x i then q i j else 0

/-- The right-hand-side summand of the balance equation (1), p. 7, for the pair `(i, j)` at the
state `x`: `π(x + e_i − e_j) φ_ij q_ij(x + e_i − e_j)`. For `i = j` the predecessor is `x` itself;
for `i ≠ j` it is `moveState x i j`, which exists only when `x_j ≥ 1` (otherwise the paper sets
`π := 0` there). -/
def inflowTerm {n : ℕ} (φ : Fin n → Fin n → ℝ) (q : (Fin n → ℕ) → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) (x : Fin n → ℕ) (i j : Fin n) : ℝ :=
  if i = j then π x * φ i i * q x i i
  else if 1 ≤ x j then π (moveState x i j) * φ i j * q (moveState x i j) i j else 0

/-- A stationary law of the `m`-unit system under the policy `q` (§2.2, p. 7): a probability
vector on `S_{n,m}`, zero off `S_{n,m}`, satisfying the balance equation (1)
`π(x) ∑_{i,j} φ_ij q_ij(x) = ∑_{i,j} π(x + e_i − e_j) φ_ij q_ij(x + e_i − e_j)` at every
`x ∈ S_{n,m}`. -/
def IsStationary (n m : ℕ) (φ : Fin n → Fin n → ℝ) (q : (Fin n → ℕ) → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ (∀ x, x ∉ states n m → π x = 0) ∧ (∑ x ∈ states n m, π x) = 1 ∧
    ∀ x ∈ states n m,
      π x * (∑ i, ∑ j, φ i j * q x i j) = ∑ i, ∑ j, inflowTerm φ q π x i j

/-- The steady-state objective (2), p. 8:
`Obj_m(q) = ∑_{x ∈ S_{n,m}} π(x) ∑_{i,j} φ_ij R_ij(q_ij(x))`, for the policy `q` and its
stationary law `π`. -/
def obj (n m : ℕ) (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ) : ℝ :=
  ∑ x ∈ states n m, π x * ∑ i, ∑ j, φ i j * rewardCurve I i j (q x i j)

/-- The steady-state flow (3), p. 8: `f_ij,m(q) = ∑_{x ∈ S_{n,m}} π(x) φ_ij q_ij(x)`. -/
def flow (n m : ℕ) (φ : Fin n → Fin n → ℝ) (q : (Fin n → ℕ) → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) (i j : Fin n) : ℝ :=
  ∑ x ∈ states n m, π x * φ i j * q x i j

/-- The elevated objective (8), p. 13: `Ôbj(q) = ∑_{i,j} φ_ij R_ij(q_ij)`. -/
def elevObj {n : ℕ} (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (q : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, φ i j * rewardCurve I i j (q i j)

/-- Balanced demand (p. 15): `∑_k φ_ki q_ki = ∑_j φ_ij q_ij` at every node `i`. -/
def IsBalanced {n : ℕ} (φ : Fin n → Fin n → ℝ) (q : Fin n → Fin n → ℝ) : Prop :=
  ∀ i, ∑ k, φ k i * q k i = ∑ j, φ i j * q i j

/-- Feasibility in the elevated flow relaxation program of Algorithm 1 (p. 14):
`q_ij ∈ [0, 1]` for all `i, j` and balanced demand. -/
def IsRelaxFeasible {n : ℕ} (φ : Fin n → Fin n → ℝ) (q : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) ∧ IsBalanced φ q

/-- `q` is an optimal solution of the elevated flow relaxation program of Algorithm 1 (p. 14):
it is feasible and maximizes `∑_{(i,j)} φ_ij R_ij(q_ij)` over all feasible quantiles. -/
def IsRelaxOptimal {n : ℕ} (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (q : Fin n → Fin n → ℝ) : Prop :=
  IsRelaxFeasible φ q ∧ ∀ q', IsRelaxFeasible φ q' → elevObj φ I q' ≤ elevObj φ I q

/-- The support graph `{(a, b) : a ≠ b, φ_ab q_ab > 0}` of a state-independent `q` is strongly
connected (the irreducibility assumption of §2, p. 7, and App. A, p. 34). -/
def SupportConnected {n : ℕ} (φ : Fin n → Fin n → ℝ) (q : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < φ a b * q a b) i j

/-- `r` solves the traffic equations of `q` in rate form (proof of Proposition 8, p. 14):
`∑_j r_j φ_ji q_ji = r_i ∑_k φ_ik q_ik` for every node `i`. -/
def IsTraffic {n : ℕ} (φ : Fin n → Fin n → ℝ) (q : Fin n → Fin n → ℝ) (r : Fin n → ℝ) : Prop :=
  ∀ i, ∑ j, r j * φ j i * q j i = r i * ∑ k, φ i k * q i k

/-- `r_max = max_j r_j` (p. 16). -/
def rmax {n : ℕ} [NeZero n] (r : Fin n → ℝ) : ℝ :=
  univ.sup' univ_nonempty r

/-- The Gordon–Newell normalization constant `G_m = ∑_{x ∈ S_{n,m}} ∏_j r_j^{x_j}`
(Theorem 2, p. 9). -/
noncomputable def G {n : ℕ} (r : Fin n → ℝ) (m : ℕ) : ℝ :=
  normConst (fun j y => r j ^ y) m

/-- The availability `A_i,m = ∑_{x ∈ S_{n,m}} π(x) 1{x_i > 0}` of node `i` under the law `π`
(Lemma 3, p. 9). -/
noncomputable def availability {n : ℕ} (m : ℕ) (π : (Fin n → ℕ) → ℝ) (i : Fin n) : ℝ :=
  tailMarginal m π i 1

/-- The infinite-unit availability `A_i,∞ = r_i / r_max` of node `i` (Proposition 6, p. 12;
proof of Lemma 12, p. 16). -/
noncomputable def availInf {n : ℕ} [NeZero n] (r : Fin n → ℝ) (i : Fin n) : ℝ :=
  r i / rmax r

/-- The infinite-unit objective `Obj_∞(q) = ∑_i A_i,∞ B_i(q)` with
`B_i(q) = ∑_j φ_ij q_ij I_ij(q_ij)` (proof of Lemma 12, p. 16). -/
noncomputable def objInf {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (q : Fin n → Fin n → ℝ) (r : Fin n → ℝ) : ℝ :=
  ∑ i, availInf r i * ∑ j, φ i j * rewardCurve I i j (q i j)

end SharedVehicleApprox.Pricing


