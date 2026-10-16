-- Prove2me | Definitions.Def_NeedPersuasion_Threshold_Model
-- name    : NeedPersuasion_Threshold_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:16.066975+00:00
-- url     : https://prove2.me/theorems/c25ff6d2-037e-4e04-99b2-b9fa2a861cf3
-- title:
--   §2, pp. 9–14 — primitives, Assumption 1, Π_AP, Π_SM, (JOIN), (LEAVE), welfare (2)–(3), Pareto efficiency, threshold structure, m_fi and fi
-- statement:
--   This file fixes the model of Anunrojwong, Iyer and Manshadi for information design in a congested social service.
--
--   **Primitives.** A single server serves, first-come-first-served and at unit exponential rate, users of two types arriving by independent Poisson processes: low-need users (type $\mathsf L$) at rate $\lambda_{\mathsf L}$ and high-need users (type $\mathsf H$) at rate $\lambda_{\mathsf H}$; the total rate is $\lambda=\lambda_{\mathsf L}+\lambda_{\mathsf H}$. A type-$i$ user who joins with $n\in\mathbb N_0$ users already in the system gets utility $u_i(n)$. High-need users always join; low-need users may take an outside option worth $0$.
--
--   **Standing assumptions** (§2 and Assumption 1):
--   1. $\lambda_{\mathsf L}>0$, $\lambda_{\mathsf H}\ge 0$ and $\lambda\le 1$;
--   2. $u_i(0)>0$ and $\lim_{k\to\infty}u_i(k)<0$ for $i\in\{\mathsf L,\mathsf H\}$;
--   3. $u_{\mathsf L}$ and $u_{\mathsf H}$ are strictly decreasing, and $u_{\mathsf L}(n)-u_{\mathsf L}(n+1)$ is non-increasing in $n$.
--
--   **Admission policies and signaling mechanisms.** $\Pi_{\mathsf{AP}}$ is the set of sequences $\pi=(\pi_n)_{n\ge0}$ with $\pi_n\ge0$, $\sum_n\pi_n=1$ and the detailed-balance constraints
--   $$\lambda_{\mathsf H}\pi_n\le\pi_{n+1}\le\lambda\pi_n\qquad(n\ge0),$$
--   and with finite welfare ($\sum_n\pi_n|u_{\mathsf L}(n)|<\infty$, $\sum_n\pi_n|u_{\mathsf H}(n)|<\infty$). With
--   $$J(\pi)=\sum_{n\ge0}(\pi_{n+1}-\lambda_{\mathsf H}\pi_n)u_{\mathsf L}(n),\qquad L(\pi)=\sum_{n\ge0}(\lambda\pi_n-\pi_{n+1})u_{\mathsf L}(n),$$
--   the signaling mechanisms $\Pi_{\mathsf{SM}}$ are the $\pi\in\Pi_{\mathsf{AP}}$ satisfying the obedience constraints $J(\pi)\ge0$ (JOIN) and $L(\pi)\le0$ (LEAVE). By Lemma 1 of the paper (Lingenbrink and Iyer 2019) these are exactly the steady-state distributions of obedient binary signaling mechanisms.
--
--   **Welfare and Pareto efficiency.** The welfare of the two types is
--   $$W_{\mathsf L}(\pi)=\sum_{n\ge0}(\pi_{n+1}-\lambda_{\mathsf H}\pi_n)u_{\mathsf L}(n)=J(\pi),\qquad W_{\mathsf H}(\pi)=\lambda_{\mathsf H}\sum_{n\ge0}\pi_nu_{\mathsf H}(n),$$
--   and $W(\pi,\theta)=\theta W_{\mathsf L}(\pi)+(1-\theta)W_{\mathsf H}(\pi)$. A sequence $\hat\pi$ Pareto-dominates $\pi$ if $W_i(\hat\pi)\ge W_i(\pi)$ for both $i$ with at least one inequality strict; $\pi$ is Pareto-efficient within a class $S$ if $\pi\in S$ and no $\hat\pi\in S$ Pareto-dominates it (Definition 1).
--
--   **Threshold structure** (Definition 2). $\pi$ has a threshold structure if for some $m\in\mathbb N_0\cup\{\infty\}$, $\pi_{k+1}=\lambda\pi_k$ for all $k<m$ and $\pi_{k+1}=\lambda_{\mathsf H}\pi_k$ for all $k>m$; for finite $m$ its threshold is $x=m+a$ with $a=(\pi_{m+1}-\lambda_{\mathsf H}\pi_m)/(\lambda_{\mathsf L}\pi_m)$. "$\pi$ has a threshold structure with threshold at most $y$" means: at some finite $m$, with $m+a\le y$.
--
--   **Full information.** $m_{\mathsf{fi}}$ is the smallest $k$ with $u_{\mathsf L}(k)<0$. For $x\ge0$ with $m=\lfloor x\rfloor$, $a=x-m$ and $\lambda_a=\lambda_{\mathsf H}+a\lambda_{\mathsf L}$, the threshold policy $\pi^x$ is proportional to $\lambda^k$ for $k\le m$ and to $\lambda^m\lambda_a\lambda_{\mathsf H}^{k-m-1}$ for $k>m$; the full-information mechanism is $\pi^{\mathsf{fi}}=\pi^{m_{\mathsf{fi}}}$, i.e. $\pi^{\mathsf{fi}}_{n+1}=\lambda\pi^{\mathsf{fi}}_n$ for $n<m_{\mathsf{fi}}$ and $\pi^{\mathsf{fi}}_{n+1}=\lambda_{\mathsf H}\pi^{\mathsf{fi}}_n$ otherwise.
--
--   These objects are the vocabulary of Theorem 1 and of every lemma of its proof.
--
--   **Formalization Note** Queue lengths are natural numbers and all quantities are real. "$\lim_k u_i(k)<0$" is encoded as "$u_i(k)<0$ for some $k$", which is equivalent for a strictly decreasing sequence and allows the limit $-\infty$. Finite welfare is part of $\Pi_{\mathsf{AP}}$: the paper treats the sums (2)–(3) as real numbers, and Lean's `tsum` would assign $0$ to a divergent sum; under the standing assumptions it also makes the sums $J$ and $L$ absolutely convergent. $W_{\mathsf L}$ is the right-hand form of (2), which never divides by $\lambda_{\mathsf L}\pi_n$. The threshold $m=\infty$ is the first disjunct of the threshold-structure predicate; "threshold at most $y$" requires a finite $m$. The threshold policy is only used for $x\ge0$ and is normalized by its own sum.
-- source:
--   arXiv:2005.07253v3, §2, pp. 9–13 (Assumption 1, (1), Lemma 1, (JOIN), (LEAVE), (2), (3), Definition 1, (a), Π_AP); Definition 2, p. 14; threshold policies π_x, p. 16 and proof of Lemma 5, p. 38

import Mathlib

namespace NeedPersuasion.Threshold

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

end NeedPersuasion.Threshold


