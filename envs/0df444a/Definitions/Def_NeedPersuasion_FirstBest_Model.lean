-- Prove2me | Definitions.Def_NeedPersuasion_FirstBest_Model
-- name    : NeedPersuasion_FirstBest_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:19.930983+00:00
-- url     : https://prove2.me/theorems/1e547f77-bf3e-49a7-a981-c516782c6e68
-- title:
--   §2, pp. 9–14 — primitives, Assumption 1, Π_AP, Π_SM, (JOIN), (LEAVE), welfare (2)–(3), Pareto efficiency, threshold structure, m_fi and fi
-- statement:
--   This module sets up the queueing model of information design for a congested social service.
--
--   A single server with unit-rate exponential service times serves, first come first served, an *unobservable* queue. Two independent Poisson streams of users arrive: **high-need** users (type H, rate $\lambda_H$) have no outside option and always join, and **low-need** users (type L, rate $\lambda_L$) either join or take an outside option of value $0$. Write $\lambda=\lambda_L+\lambda_H$. A type-$i$ user who joins with $n$ users already in the system receives utility $u_i(n)$, $n\in\mathbb N_0$.
--
--   The **standing assumptions** are $\lambda_L>0$, $\lambda_H\ge 0$, $\lambda\le 1$, $u_i(0)>0$ and $\lim_k u_i(k)<0$ for $i\in\{L,H\}$, together with **Assumption 1**: each $u_i$ is strictly decreasing, and the increments $u_L(n)-u_L(n+1)$ are non-increasing in $n$.
--
--   1. The **admission policies** $\Pi_{AP}$ are the distributions $\pi$ on $\mathbb N_0$ with $\pi_n\ge0$, $\sum_n\pi_n=1$ and the detailed-balance constraints
--   $$\lambda_H\pi_n\le\pi_{n+1}\le\lambda\pi_n\qquad(n\ge0).$$
--   2. The obedience values are $J(\pi)=\sum_{n\ge0}(\pi_{n+1}-\lambda_H\pi_n)u_L(n)$ (JOIN) and $L(\pi)=\sum_{n\ge0}(\lambda\pi_n-\pi_{n+1})u_L(n)$ (LEAVE). The **signaling mechanisms** $\Pi_{SM}\subseteq\Pi_{AP}$ are those with $J(\pi)\ge0$ and $L(\pi)\le0$.
--   3. The welfares are $W_L(\pi)=\sum_n(\pi_{n+1}-\lambda_H\pi_n)u_L(n)=J(\pi)$ and $W_H(\pi)=\lambda_H\sum_n\pi_nu_H(n)$, and $W(\pi,\theta)=\theta W_L(\pi)+(1-\theta)W_H(\pi)$.
--   4. $\hat\pi$ **Pareto-dominates** $\pi$ if $W_i(\hat\pi)\ge W_i(\pi)$ for both types, strictly for at least one; $\pi$ is **Pareto-efficient within a class** $S$ if $\pi\in S$ and no element of $S$ Pareto-dominates it (Definition 1).
--   5. $\pi$ has a **threshold structure** (Definition 2) if for some $m\in\mathbb N_0\cup\{\infty\}$, $\pi_{k+1}=\lambda\pi_k$ for $k<m$ and $\pi_{k+1}=\lambda_H\pi_k$ for $k>m$; its threshold is $x=m+a$ with $a=(\pi_{m+1}-\lambda_H\pi_m)/(\lambda_L\pi_m)$.
--   6. The **full-information threshold** $m_{fi}$ is the least $k$ with $u_L(k)<0$, and for $x\ge0$ the **threshold policy** $\pi_x$ is the distribution proportional to $\lambda^k$ for $k\le m$ and to $\lambda^m(\lambda_H+a\lambda_L)\lambda_H^{k-m-1}$ for $k>m$, where $m=\lfloor x\rfloor$, $a=x-m$. The full-information mechanism is $\mathrm{fi}=\pi_{m_{fi}}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The paper treats the welfare sums as finite; membership in $\Pi_{AP}$ therefore also requires $\sum_n\pi_nu_L(n)$ and $\sum_n\pi_nu_H(n)$ to converge. "$\lim_k u_i(k)<0$" is encoded as "$u_i(k)<0$ for some $k$", which is equivalent for a strictly decreasing sequence. $W_L$ is defined by the right-hand form of (2), without the division by $\lambda_L\pi_n$. Threshold $\infty$ is the first disjunct of the threshold-structure predicate; "threshold at most $y$" requires a finite $m$.
-- source:
--   arXiv:2005.07253v3, §2, pp. 9–13 (Assumption 1, (JOIN), (LEAVE), (2), (3), Definition 1, (a)); Definition 2, p. 14; threshold policies, p. 16

import Mathlib

namespace NeedPersuasion.FirstBest

/-- The primitives of §2 (p. 9): the arrival rates `lamL` (= λ_L, low-need users) and `lamH`
(= λ_H, high-need users) of two independent Poisson streams, and the utilities `uL n`, `uH n`
(= u_L(n), u_H(n)) of a low-need / high-need user who joins a queue with `n` users already in the
system (service is exponential with rate one). -/
structure Model where
  lamL : ℝ
  lamH : ℝ
  uL : ℕ → ℝ
  uH : ℕ → ℝ

namespace Model

/-- The total arrival rate λ = λ_L + λ_H (p. 9). -/
def lam (M : Model) : ℝ := M.lamL + M.lamH

/-- The standing assumptions of §2 (p. 9) and Assumption 1 (pp. 9–10): λ_L > 0, λ_H ≥ 0, λ ≤ 1,
u_i(0) > 0 and lim_{k→∞} u_i(k) < 0 for i ∈ {L, H} (for a strictly decreasing sequence this is
"u_i(k) < 0 for some k"), u_L and u_H strictly decreasing, and u_L(n) − u_L(n+1) non-increasing. -/
def Standing (M : Model) : Prop :=
  0 < M.lamL ∧ 0 ≤ M.lamH ∧ M.lam ≤ 1 ∧ 0 < M.uL 0 ∧ 0 < M.uH 0 ∧
    (∃ k, M.uL k < 0) ∧ (∃ k, M.uH k < 0) ∧ StrictAnti M.uL ∧ StrictAnti M.uH ∧
    Antitone (fun n => M.uL n - M.uL (n + 1))

end Model

/-- Π_AP, the admission policies (Lemma 1 (1)–(2), p. 11; p. 13): steady-state distributions `π` on
ℕ = N₀ with `π n ≥ 0`, `∑ π n = 1`, and the detailed-balance constraints
λ_H π_n ≤ π_{n+1} ≤ λ π_n. Finite welfare (`π · u_L` and `π · u_H` summable) is part of the class:
the paper treats the welfare sums (2)–(3) as finite numbers. -/
def PiAP (M : Model) : Set (ℕ → ℝ) :=
  {π | (∀ n, 0 ≤ π n) ∧ HasSum π 1 ∧
    (∀ n, M.lamH * π n ≤ π (n + 1) ∧ π (n + 1) ≤ M.lam * π n) ∧
    Summable (fun n => π n * M.uL n) ∧ Summable (fun n => π n * M.uH n)}

/-- J(π) = ∑_{n ≥ 0} (π_{n+1} − λ_H π_n) u_L(n), the left side of (JOIN) (p. 11). -/
noncomputable def joinVal (M : Model) (π : ℕ → ℝ) : ℝ :=
  ∑' n, (π (n + 1) - M.lamH * π n) * M.uL n

/-- L(π) = ∑_{n ≥ 0} (λ π_n − π_{n+1}) u_L(n), the left side of (LEAVE) (p. 11). -/
noncomputable def leaveVal (M : Model) (π : ℕ → ℝ) : ℝ :=
  ∑' n, (M.lam * π n - π (n + 1)) * M.uL n

/-- Π_SM, the (obedient binary) signaling mechanisms (p. 12): the π ∈ Π_AP with J(π) ≥ 0 (JOIN)
and L(π) ≤ 0 (LEAVE). -/
def PiSM (M : Model) : Set (ℕ → ℝ) :=
  {π | π ∈ PiAP M ∧ 0 ≤ joinVal M π ∧ leaveVal M π ≤ 0}

/-- W_L(π) = ∑_{n ≥ 0} (π_{n+1} − λ_H π_n) u_L(n), the welfare of low-need users, right-hand form
of (2) (p. 12). -/
noncomputable def WL (M : Model) (π : ℕ → ℝ) : ℝ :=
  ∑' n, (π (n + 1) - M.lamH * π n) * M.uL n

/-- W_H(π) = λ_H ∑_{n ≥ 0} π_n u_H(n), the welfare of high-need users, (3) (p. 12). -/
noncomputable def WH (M : Model) (π : ℕ → ℝ) : ℝ :=
  M.lamH * ∑' n, π n * M.uH n

/-- W(π, θ) = θ W_L(π) + (1 − θ) W_H(π) (p. 13). -/
noncomputable def W (M : Model) (θ : ℝ) (π : ℕ → ℝ) : ℝ :=
  θ * WL M π + (1 - θ) * WH M π

/-- Definition 1 (p. 12): `π'` Pareto-dominates `π` if W_i(π') ≥ W_i(π) for i ∈ {L, H}, with a
strict inequality for at least one i. -/
def Dominates (M : Model) (π' π : ℕ → ℝ) : Prop :=
  (WL M π ≤ WL M π' ∧ WH M π ≤ WH M π') ∧ (WL M π < WL M π' ∨ WH M π < WH M π')

/-- Definition 1 (p. 12; p. 13 for Π_AP): `π` is Pareto-efficient within the class `S` if `π ∈ S`
and no `π' ∈ S` Pareto-dominates `π`. -/
def ParetoEfficientIn (M : Model) (S : Set (ℕ → ℝ)) (π : ℕ → ℝ) : Prop :=
  π ∈ S ∧ ∀ π' ∈ S, ¬ Dominates M π' π

/-- Definition 2 (p. 14): `π` has a threshold structure if there is m ∈ N₀ ∪ {∞} with
π_{k+1} = λ π_k for all k < m and π_{k+1} = λ_H π_k for all k > m. The first disjunct is m = ∞. -/
def HasThresholdStructure (M : Model) (π : ℕ → ℝ) : Prop :=
  (∀ k, π (k + 1) = M.lam * π k) ∨
    ∃ m : ℕ, (∀ k, k < m → π (k + 1) = M.lam * π k) ∧ ∀ k, m < k → π (k + 1) = M.lamH * π k

/-- Definition 2 (p. 14), threshold at most `y`: `π` has a threshold structure at a finite
m ∈ N₀ whose threshold x = m + a, a = (π_{m+1} − λ_H π_m)/(λ_L π_m), satisfies x ≤ y. -/
def HasThresholdAtMost (M : Model) (π : ℕ → ℝ) (y : ℝ) : Prop :=
  ∃ m : ℕ, ((∀ k, k < m → π (k + 1) = M.lam * π k) ∧ ∀ k, m < k → π (k + 1) = M.lamH * π k) ∧
    (m : ℝ) + (π (m + 1) - M.lamH * π m) / (M.lamL * π m) ≤ y

/-- m_fi, the smallest integer k with u_L(k) < 0 (p. 12, (a)); the set is nonempty under
`Model.Standing`. -/
noncomputable def mfi (M : Model) : ℕ := sInf {k | M.uL k < 0}

/-- The threshold policy π_x for x ≥ 0 (Definition 2, p. 14; p. 16): with m = ⌊x⌋, a = x − m and
λ_a = λ_H + a λ_L, the distribution proportional to λ^k for k ≤ m and λ^m λ_a λ_H^{k−m−1} for
k > m (the normalizer of the proof of Lemma 5, p. 38). -/
noncomputable def thresholdPolicy (M : Model) (x : ℝ) : ℕ → ℝ :=
  let m := ⌊x⌋₊
  let la := M.lamH + Int.fract x * M.lamL
  let w : ℕ → ℝ := fun k => if k ≤ m then M.lam ^ k else M.lam ^ m * la * M.lamH ^ (k - m - 1)
  fun k => w k / ∑' j, w j

/-- The full-information mechanism fi = π_{m_fi} (p. 12, (a)): π_{n+1} = λ π_n for n < m_fi and
π_{n+1} = λ_H π_n otherwise. -/
noncomputable def fi (M : Model) : ℕ → ℝ := thresholdPolicy M (mfi M)

end NeedPersuasion.FirstBest


