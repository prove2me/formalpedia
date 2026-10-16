-- Prove2me | Definitions.Def_NeedPersuasion_FullInfo_Model
-- name    : NeedPersuasion_FullInfo_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:20.709094+00:00
-- url     : https://prove2.me/theorems/e11de25c-b6d7-4e84-aa43-eb3450ba1e2a
-- title:
--   §2, pp. 9–14 — primitives, Assumption 1, Π_AP, Π_SM, (JOIN), (LEAVE), welfare (2)–(3), Pareto efficiency, threshold structure, threshold policies, m_fi and fi
-- statement:
--   This file fixes the queueing model of Anunrojwong, Iyer and Manshadi's information-design problem for a congested social service.
--
--   **Primitives.** A single-server FCFS queue with unit-rate exponential service receives two independent Poisson streams: low-need users (type L) at rate $\lambda_L$ and high-need users (type H) at rate $\lambda_H$; write $\lambda=\lambda_L+\lambda_H$. A type-$i$ user who joins with $n$ users already in the system receives utility $u_i(n)$; L users have an outside option worth $0$, H users always join. The **standing assumptions** (p. 9 and Assumption 1, pp. 9–10) are
--   1. $\lambda_L>0$, $\lambda_H\ge 0$, $\lambda\le 1$;
--   2. $u_i(0)>0$ and $\lim_{k\to\infty}u_i(k)<0$ for $i\in\{L,H\}$;
--   3. each $u_i$ is strictly decreasing;
--   4. the increment $u_L(n)-u_L(n+1)$ is non-increasing in $n$.
--
--   **Admission policies and signaling mechanisms.** An *admission policy* is a distribution $\pi=(\pi_n)_{n\ge0}$ on $\mathbb N_0$ with
--   $$\pi_n\ge 0,\qquad \sum_{n\ge0}\pi_n=1,\qquad \lambda_H\pi_n\le\pi_{n+1}\le\lambda\pi_n\quad(n\ge0),$$
--   and with finite welfare: $\sum_n\pi_nu_L(n)$ and $\sum_n\pi_nu_H(n)$ converge. Their set is $\Pi_{AP}$. A *signaling mechanism* is a $\pi\in\Pi_{AP}$ satisfying the obedience constraints
--   $$J(\pi)=\sum_{n\ge0}(\pi_{n+1}-\lambda_H\pi_n)u_L(n)\ge0,\qquad L(\pi)=\sum_{n\ge0}(\lambda\pi_n-\pi_{n+1})u_L(n)\le0,$$
--   (JOIN) and (LEAVE); their set is $\Pi_{SM}\subseteq\Pi_{AP}$.
--
--   **Welfare and Pareto efficiency.** The welfare of the two types is (2)–(3)
--   $$W_L(\pi)=\sum_{n\ge0}(\pi_{n+1}-\lambda_H\pi_n)u_L(n),\qquad W_H(\pi)=\lambda_H\sum_{n\ge0}\pi_nu_H(n),$$
--   and $W(\pi,\theta)=\theta W_L(\pi)+(1-\theta)W_H(\pi)$. A distribution $\hat\pi$ *Pareto-dominates* $\pi$ if $W_i(\hat\pi)\ge W_i(\pi)$ for both types, strictly for at least one; $\pi$ is *Pareto-efficient within a class* $S$ if $\pi\in S$ and no element of $S$ Pareto-dominates it (Definition 1).
--
--   **Threshold structure.** A distribution $\pi\in\Pi_{AP}$ has a *threshold structure* (Definition 2) if there is $m\in\mathbb N_0\cup\{\infty\}$ with $\pi_{k+1}=\lambda\pi_k$ for $k<m$ and $\pi_{k+1}=\lambda_H\pi_k$ for $k>m$; for finite $m$ with $\pi_m>0$ its threshold is $x=m+a$ with $a=(\pi_{m+1}-\lambda_H\pi_m)/(\lambda_L\pi_m)\in[0,1]$. For $x\ge0$, with $m=\lfloor x\rfloor$, $a=x-m$ and $\lambda_a=\lambda_H+a\lambda_L$, the *threshold policy* $\pi_x$ is proportional to the weights $\lambda^k$ for $k\le m$ and $\lambda^m\lambda_a\lambda_H^{k-m-1}$ for $k>m$. We write $W_L(x)=W_L(\pi_x)$, $W_H(x)=W_H(\pi_x)$ and $L(x)=L(\pi_x)$.
--
--   **Full information.** $m_{fi}$ is the smallest $k$ with $u_L(k)<0$, and the full-information mechanism is $\mathsf{fi}=\pi_{m_{fi}}$: $\pi_{n+1}=\lambda\pi_n$ for $n<m_{fi}$ and $\pi_{n+1}=\lambda_H\pi_n$ otherwise (p. 12).
--
--   Every statement of this mission is phrased in these terms.
--
--   **Formalization Note** The model is a structure with real fields `lamL`, `lamH` and utilities `uL uH : ℕ → ℝ`; queue lengths are natural numbers. The paper's $\lim_k u_i(k)<0$ is encoded as $\exists k,\ u_i(k)<0$, which is equivalent for a strictly decreasing sequence. Membership in $\Pi_{AP}$ additionally requires the two welfare series to be summable: the paper treats every welfare as a finite number, and Lean's `tsum` would otherwise assign the value $0$ to a divergent series. $W_L$ is the right-hand form of (2), without the division by $\lambda_L\pi_n$. "Threshold at most $y$" requires a finite $m$ with $\pi_m>0$ and $a\in[0,1]$, so it excludes the threshold $\infty$ and division by zero. The threshold policy is defined directly from its weights (divided by their sum), never through a closed-form welfare.
-- source:
--   arXiv:2005.07253v3, §2, pp. 9–13 (Assumption 1, Lemma 1, (JOIN), (LEAVE), (2)–(3), Definition 1, (a)); Definition 2, p. 14; Lemma 5's proof, p. 38

import Mathlib

namespace NeedPersuasion.FullInfo

/-- The primitives of §2, p. 9: the arrival rates `λ_L`, `λ_H` of low-need (L) and high-need (H)
users, and their utilities `u_L(n)`, `u_H(n)` for joining with `n` users already in the system. -/
structure Model where
  lamL : ℝ
  lamH : ℝ
  uL : ℕ → ℝ
  uH : ℕ → ℝ

namespace Model

/-- The total arrival rate `λ = λ_L + λ_H` (p. 9). -/
def lam (M : Model) : ℝ := M.lamL + M.lamH

/-- The standing assumptions of §2 (p. 9) and Assumption 1 (pp. 9–10): `λ_L > 0`, `λ_H ≥ 0`,
`λ ≤ 1`, `u_i(0) > 0`, `lim_k u_i(k) < 0` (encoded as `∃ k, u_i k < 0`, equivalent for a strictly
decreasing sequence), `u_i` strictly decreasing, and `u_L(n) − u_L(n+1)` non-increasing. -/
def Standing (M : Model) : Prop :=
  0 < M.lamL ∧ 0 ≤ M.lamH ∧ M.lam ≤ 1 ∧ 0 < M.uL 0 ∧ 0 < M.uH 0 ∧
    (∃ k, M.uL k < 0) ∧ (∃ k, M.uH k < 0) ∧ StrictAnti M.uL ∧ StrictAnti M.uH ∧
    Antitone (fun n => M.uL n - M.uL (n + 1))

end Model

/-- Admission policies `Π_AP` (Lemma 1 (1)–(2), p. 11, and p. 13): distributions `π` on `ℕ`
with `λ_H π_n ≤ π_{n+1} ≤ λ π_n`, and with finite welfare (both `π_n u_L(n)` and `π_n u_H(n)`
summable). -/
def PiAP (M : Model) : Set (ℕ → ℝ) :=
  {π | (∀ n, 0 ≤ π n) ∧ HasSum π 1 ∧
    (∀ n, M.lamH * π n ≤ π (n + 1) ∧ π (n + 1) ≤ M.lam * π n) ∧
    Summable (fun n => π n * M.uL n) ∧ Summable (fun n => π n * M.uH n)}

/-- `J(π) = ∑_n (π_{n+1} − λ_H π_n) u_L(n)`, the left-hand side of (JOIN), p. 11. -/
noncomputable def joinVal (M : Model) (π : ℕ → ℝ) : ℝ :=
  ∑' n, (π (n + 1) - M.lamH * π n) * M.uL n

/-- `L(π) = ∑_n (λ π_n − π_{n+1}) u_L(n)`, the left-hand side of (LEAVE), p. 11. -/
noncomputable def leaveVal (M : Model) (π : ℕ → ℝ) : ℝ :=
  ∑' n, (M.lam * π n - π (n + 1)) * M.uL n

/-- Signaling mechanisms `Π_SM` (p. 12): admission policies satisfying (JOIN) and (LEAVE). -/
def PiSM (M : Model) : Set (ℕ → ℝ) :=
  {π | π ∈ PiAP M ∧ 0 ≤ joinVal M π ∧ leaveVal M π ≤ 0}

/-- Welfare of L users, (2), p. 12, in its right-hand form `∑_n (π_{n+1} − λ_H π_n) u_L(n)`. -/
noncomputable def WL (M : Model) (π : ℕ → ℝ) : ℝ :=
  ∑' n, (π (n + 1) - M.lamH * π n) * M.uL n

/-- Welfare of H users, (3), p. 12: `λ_H ∑_n π_n u_H(n)`. -/
noncomputable def WH (M : Model) (π : ℕ → ℝ) : ℝ :=
  M.lamH * ∑' n, π n * M.uH n

/-- The weighted welfare `W(π, θ) = θ W_L(π) + (1 − θ) W_H(π)` (p. 13). -/
noncomputable def W (M : Model) (θ : ℝ) (π : ℕ → ℝ) : ℝ :=
  θ * WL M π + (1 - θ) * WH M π

/-- Definition 1, p. 12: `π'` Pareto-dominates `π`. -/
def Dominates (M : Model) (π' π : ℕ → ℝ) : Prop :=
  WL M π ≤ WL M π' ∧ WH M π ≤ WH M π' ∧ (WL M π < WL M π' ∨ WH M π < WH M π')

/-- Definition 1, p. 12 (and p. 13 for `Π_AP`): `π` is Pareto-efficient within the class `S`. -/
def ParetoEfficientIn (M : Model) (S : Set (ℕ → ℝ)) (π : ℕ → ℝ) : Prop :=
  π ∈ S ∧ ∀ π' ∈ S, ¬ Dominates M π' π

/-- Definition 2, p. 14: threshold structure for `π ∈ Π_AP`; the first disjunct is `m = ∞`. -/
def HasThresholdStructure (M : Model) (π : ℕ → ℝ) : Prop :=
  π ∈ PiAP M ∧
    ((∀ k, π (k + 1) = M.lam * π k) ∨
      ∃ m : ℕ, (∀ k < m, π (k + 1) = M.lam * π k) ∧
        ∀ k, m < k → π (k + 1) = M.lamH * π k)

/-- Definition 2, p. 14: `π ∈ Π_AP` has a finite threshold `x = m + a ≤ y`, with
`π_m > 0` and `a = (π_{m+1} − λ_H π_m)/(λ_L π_m) ∈ [0,1]`. -/
def HasThresholdAtMost (M : Model) (π : ℕ → ℝ) (y : ℝ) : Prop :=
  π ∈ PiAP M ∧
    ∃ m : ℕ, 0 < π m ∧
      (∀ k < m, π (k + 1) = M.lam * π k) ∧
      (∀ k, m < k → π (k + 1) = M.lamH * π k) ∧
      0 ≤ (π (m + 1) - M.lamH * π m) / (M.lamL * π m) ∧
      (π (m + 1) - M.lamH * π m) / (M.lamL * π m) ≤ 1 ∧
      (m : ℝ) + (π (m + 1) - M.lamH * π m) / (M.lamL * π m) ≤ y

/-- The full-information threshold `m_fi`, the smallest `k` with `u_L(k) < 0` (p. 12). -/
noncomputable def mfi (M : Model) : ℕ := sInf {k | M.uL k < 0}

/-- The threshold policy `π_x`, `x ≥ 0` (Definition 2, p. 14; normalizer of Lemma 5's proof,
p. 38): with `m = ⌊x⌋`, `a = x − m`, `λ_a = λ_H + a λ_L`, unnormalized weights `λ^k` for `k ≤ m`
and `λ^m λ_a λ_H^{k−m−1}` for `k > m`, divided by their sum. -/
noncomputable def thresholdPolicy (M : Model) (x : ℝ) : ℕ → ℝ :=
  let m := ⌊x⌋₊
  let la := M.lamH + Int.fract x * M.lamL
  let w : ℕ → ℝ := fun k => if k ≤ m then M.lam ^ k else M.lam ^ m * la * M.lamH ^ (k - m - 1)
  fun k => w k / ∑' j, w j

/-- The full-information mechanism `fi = π_{m_fi}` (p. 12, (a)). -/
noncomputable def fi (M : Model) : ℕ → ℝ := thresholdPolicy M (mfi M)

/-- `W_L(x) = W_L(π_x)` (p. 16). -/
noncomputable def WLx (M : Model) (x : ℝ) : ℝ := WL M (thresholdPolicy M x)

/-- `W_H(x) = W_H(π_x)` (p. 16). -/
noncomputable def WHx (M : Model) (x : ℝ) : ℝ := WH M (thresholdPolicy M x)

/-- `L(x) = L(π_x)`. -/
noncomputable def leaveValx (M : Model) (x : ℝ) : ℝ := leaveVal M (thresholdPolicy M x)

end NeedPersuasion.FullInfo


