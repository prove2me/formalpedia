-- Prove2me | Definitions.Def_NeedPersuasion_Homog_Model
-- name    : NeedPersuasion_Homog_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:17.775993+00:00
-- url     : https://prove2.me/theorems/0dc71027-8676-499f-83d7-185197aeec1b
-- title:
--   §2, pp. 9–16 — primitives, Assumption 1, Π_AP, Π_SM, (JOIN), (LEAVE), welfare (2)–(3), Pareto efficiency, threshold structure, threshold policies π_x, m_fi and fi
-- statement:
--   This definition file sets up the model of information design in a congested service (Anunrojwong, Iyer and Manshadi, §2).
--
--   A single server with unit-rate exponential service times serves, first come first served, an **unobservable** queue. Users of two types arrive as independent Poisson processes: **high-need** users (type H, rate $\lambda_H$) have no outside option and always join; **low-need** users (type L, rate $\lambda_L$) may leave for an outside option of utility $0$. A type-$i$ user who joins with $n$ users already present receives utility $u_i(n)$, and $\lambda = \lambda_L + \lambda_H$ is the total arrival rate.
--
--   1. **Standing assumptions** (p. 9 and Assumption 1, pp. 9–10): $\lambda_L > 0$, $\lambda_H \ge 0$, $\lambda \le 1$; $u_i(0) > 0$ and $\lim_k u_i(k) < 0$, encoded as "$u_i(k) < 0$ for some $k$"; each $u_i$ is strictly decreasing; and $u_L(n) - u_L(n+1)$ is non-increasing in $n$.
--   2. **Admission policies** $\Pi_{AP}$ (Lemma 1, p. 11; p. 13): probability distributions $\pi$ on $\mathbb N_0$ with the detailed-balance constraints
--   $$\lambda_H \pi_n \le \pi_{n+1} \le \lambda \pi_n \qquad (n \ge 0),$$
--   and with finite welfare: the series $\sum_n \pi_n u_L(n)$ and $\sum_n \pi_n u_H(n)$ converge.
--   3. **Obedience** (p. 11): $J(\pi) = \sum_{n\ge 0} (\pi_{n+1} - \lambda_H\pi_n) u_L(n)$ and $L(\pi) = \sum_{n\ge0} (\lambda\pi_n - \pi_{n+1}) u_L(n)$. The **signaling mechanisms** $\Pi_{SM}$ are the admission policies with $J(\pi) \ge 0$ (JOIN) and $L(\pi) \le 0$ (LEAVE).
--   4. **Welfare** (2)–(3), p. 12: $W_L(\pi) = \sum_{n} (\pi_{n+1} - \lambda_H \pi_n) u_L(n)$ and $W_H(\pi) = \lambda_H \sum_n \pi_n u_H(n)$; the weighted welfare is $W(\pi,\theta) = \theta W_L(\pi) + (1-\theta) W_H(\pi)$ (p. 13).
--   5. **Pareto efficiency** (Definition 1, p. 12): $\hat\pi$ Pareto-dominates $\pi$ if $W_i(\hat\pi) \ge W_i(\pi)$ for both types, strictly for at least one; $\pi$ is Pareto-efficient within a class $S$ if $\pi \in S$ and no member of $S$ dominates it.
--   6. **Threshold structure** (Definition 2, p. 14): $\pi$ has a threshold structure if either $\pi_{k+1} = \lambda \pi_k$ for all $k$ (threshold $\infty$), or there is $m \in \mathbb N_0$ with $\pi_{k+1} = \lambda\pi_k$ for $k < m$ and $\pi_{k+1} = \lambda_H \pi_k$ for $k > m$; its threshold is then $x = m + a$ with $a = (\pi_{m+1} - \lambda_H\pi_m)/(\lambda_L\pi_m)$. "Threshold at most $y$" means a finite $m$ with $m + a \le y$.
--   7. **Threshold policies** (p. 16): for $x \ge 0$ write $m = \lfloor x\rfloor$, $a = x - m$, $\lambda_a = \lambda_H + a\lambda_L$. The policy $\pi_x$ is proportional to $\lambda^k$ for $k \le m$ and to $\lambda^m \lambda_a \lambda_H^{k-m-1}$ for $k > m$, normalized to total mass $1$. As in the paper, $W_L(x)$, $W_H(x)$, $J(x)$, $L(x)$ denote the corresponding quantities of $\pi_x$.
--   8. **Full information** (p. 12): $m_{fi}$ is the smallest $k$ with $u_L(k) < 0$, and $\mathrm{fi} = \pi_{m_{fi}}$.
--
--   Every statement of the mission is phrased in terms of these objects.
--
--   **Formalization Note** Queue lengths are natural numbers and distributions are functions $\mathbb N \to \mathbb R$. Membership in $\Pi_{AP}$ includes summability of $\pi_n u_L(n)$ and $\pi_n u_H(n)$, because Lean's `tsum` of a non-summable series is $0$; the paper treats these welfare sums as finite. $W_L$ is written in the right-hand form of (2), without the division by $\lambda_L \pi_n$. The threshold policy is defined from its weights, never through a closed-form welfare. For $x < 0$ the threshold policy is a meaningless value and is never used.
-- source:
--   arXiv:2005.07253v3, §2, pp. 9–13 (Assumption 1, Lemma 1, (JOIN), (LEAVE), (2), (3), Definition 1, full-information mechanism (a)); Definition 2, p. 14; §4, p. 16 (threshold policies); normalizer of π_x, proof of Lemma 5, p. 38

import Mathlib

namespace NeedPersuasion.Homog

/-- Primitives of the congested-service model (§2, p. 9): the arrival rates `lamL`, `lamH`
of low-need (L) and high-need (H) users, and their utilities `uL n`, `uH n` of joining a
queue with `n` users already in the system. -/
structure Model where
  lamL : ℝ
  lamH : ℝ
  uL : ℕ → ℝ
  uH : ℕ → ℝ

/-- Total arrival rate `λ = λ_L + λ_H`. -/
def Model.lam (M : Model) : ℝ := M.lamL + M.lamH

/-- Standing assumptions of §2 (p. 9) and Assumption 1 (pp. 9–10): `λ_L > 0`, `λ_H ≥ 0`,
`λ ≤ 1`, `u_i(0) > 0`, `lim_k u_i(k) < 0` (encoded as `∃ k, u_i k < 0`), `u_i` strictly
decreasing, and `u_L(n) - u_L(n+1)` non-increasing. -/
def Model.Standing (M : Model) : Prop :=
  0 < M.lamL ∧ 0 ≤ M.lamH ∧ M.lam ≤ 1 ∧ 0 < M.uL 0 ∧ 0 < M.uH 0 ∧
    (∃ k, M.uL k < 0) ∧ (∃ k, M.uH k < 0) ∧ StrictAnti M.uL ∧ StrictAnti M.uH ∧
    Antitone (fun n => M.uL n - M.uL (n + 1))

/-- Admission policies `Π_AP` (Lemma 1 (1)–(2), p. 11; p. 13): probability distributions on
`ℕ` satisfying the detailed-balance constraints `λ_H π_n ≤ π_{n+1} ≤ λ π_n`, with finite
welfare of both types (the series `∑ π_n u_i(n)` are summable). -/
def PiAP (M : Model) : Set (ℕ → ℝ) :=
  {π | (∀ n, 0 ≤ π n) ∧ HasSum π 1 ∧
    (∀ n, M.lamH * π n ≤ π (n + 1) ∧ π (n + 1) ≤ M.lam * π n) ∧
    Summable (fun n => π n * M.uL n) ∧ Summable (fun n => π n * M.uH n)}

/-- `J(π) = ∑_n (π_{n+1} - λ_H π_n) u_L(n)`, the left side of (JOIN), p. 11. -/
noncomputable def joinVal (M : Model) (π : ℕ → ℝ) : ℝ :=
  ∑' n, (π (n + 1) - M.lamH * π n) * M.uL n

/-- `L(π) = ∑_n (λ π_n - π_{n+1}) u_L(n)`, the left side of (LEAVE), p. 11. -/
noncomputable def leaveVal (M : Model) (π : ℕ → ℝ) : ℝ :=
  ∑' n, (M.lam * π n - π (n + 1)) * M.uL n

/-- Signaling mechanisms `Π_SM` (p. 12): admission policies satisfying (JOIN) and (LEAVE). -/
def PiSM (M : Model) : Set (ℕ → ℝ) :=
  {π | π ∈ PiAP M ∧ 0 ≤ joinVal M π ∧ leaveVal M π ≤ 0}

/-- Welfare of L-type users, (2), p. 12 (right-hand form). -/
noncomputable def WL (M : Model) (π : ℕ → ℝ) : ℝ :=
  ∑' n, (π (n + 1) - M.lamH * π n) * M.uL n

/-- Welfare of H-type users, (3), p. 12. -/
noncomputable def WH (M : Model) (π : ℕ → ℝ) : ℝ :=
  M.lamH * ∑' n, π n * M.uH n

/-- Weighted welfare `W(π, θ) = θ W_L(π) + (1 - θ) W_H(π)` (p. 13). -/
noncomputable def W (M : Model) (θ : ℝ) (π : ℕ → ℝ) : ℝ :=
  θ * WL M π + (1 - θ) * WH M π

/-- `π'` Pareto-dominates `π` (Definition 1, p. 12). -/
def Dominates (M : Model) (π' π : ℕ → ℝ) : Prop :=
  WL M π' ≥ WL M π ∧ WH M π' ≥ WH M π ∧ (WL M π' > WL M π ∨ WH M π' > WH M π)

/-- `π` is Pareto-efficient within the class `S` (Definition 1, p. 12; p. 13). -/
def ParetoEfficientIn (M : Model) (S : Set (ℕ → ℝ)) (π : ℕ → ℝ) : Prop :=
  π ∈ S ∧ ∀ π' ∈ S, ¬ Dominates M π' π

/-- Threshold structure (Definition 2, p. 14); the first disjunct is the threshold `m = ∞`. -/
def HasThresholdStructure (M : Model) (π : ℕ → ℝ) : Prop :=
  (∀ k, π (k + 1) = M.lam * π k) ∨
    ∃ m : ℕ, (∀ k < m, π (k + 1) = M.lam * π k) ∧ ∀ k, m < k → π (k + 1) = M.lamH * π k

/-- `π` has a threshold structure with a finite threshold `x = m + a ≤ y`, where
`a = (π_{m+1} - λ_H π_m)/(λ_L π_m)` (Definition 2, p. 14). -/
def HasThresholdAtMost (M : Model) (π : ℕ → ℝ) (y : ℝ) : Prop :=
  ∃ m : ℕ, (∀ k < m, π (k + 1) = M.lam * π k) ∧ (∀ k, m < k → π (k + 1) = M.lamH * π k) ∧
    (m : ℝ) + (π (m + 1) - M.lamH * π m) / (M.lamL * π m) ≤ y

/-- The full-information threshold `m_fi`, the smallest `k` with `u_L(k) < 0` (p. 12). -/
noncomputable def mfi (M : Model) : ℕ := sInf {k | M.uL k < 0}

/-- The threshold policy `π_x` for `x ≥ 0` (Definition 2, p. 14; p. 16): with `m = ⌊x⌋`,
`a = x - m` and `λ_a = λ_H + a λ_L`, the unnormalized weights are `λ^k` for `k ≤ m` and
`λ^m λ_a λ_H^{k-m-1}` for `k > m`, divided by their sum (the normalizer of p. 38). -/
noncomputable def thresholdPolicy (M : Model) (x : ℝ) : ℕ → ℝ :=
  let w : ℕ → ℝ := fun k =>
    if k ≤ ⌊x⌋₊ then M.lam ^ k
    else M.lam ^ ⌊x⌋₊ * (M.lamH + Int.fract x * M.lamL) * M.lamH ^ (k - ⌊x⌋₊ - 1)
  fun k => w k / ∑' j, w j

/-- The full-information mechanism `fi = π_{m_fi}` (p. 12, (a)). -/
noncomputable def fi (M : Model) : ℕ → ℝ := thresholdPolicy M (mfi M)

/-- `W_L(x) = W_L(π_x)` (p. 16). -/
noncomputable def WLx (M : Model) (x : ℝ) : ℝ := WL M (thresholdPolicy M x)

/-- `W_H(x) = W_H(π_x)` (p. 16). -/
noncomputable def WHx (M : Model) (x : ℝ) : ℝ := WH M (thresholdPolicy M x)

/-- `J(x) = J(π_x)` (p. 16). -/
noncomputable def joinValx (M : Model) (x : ℝ) : ℝ := joinVal M (thresholdPolicy M x)

/-- `L(x) = L(π_x)` (p. 16). -/
noncomputable def leaveValx (M : Model) (x : ℝ) : ℝ := leaveVal M (thresholdPolicy M x)

end NeedPersuasion.Homog


