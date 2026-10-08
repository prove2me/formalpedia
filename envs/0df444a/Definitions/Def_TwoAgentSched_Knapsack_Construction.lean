-- Prove2me | Definitions.Def_TwoAgentSched_Knapsack_Construction
-- name    : TwoAgentSched_Knapsack_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:59.963999+00:00
-- url     : https://prove2.me/theorems/f45ce610-48b1-4c20-853d-d4ede0189603
-- title:
--   Proof of Theorem 5.2 — the instance $p^A_i=u_i$, $w^A_i=w_i$, $p^B_1=\hat w\hat u$ and the thresholds $Q_A$, $Q_B$
-- statement:
--   The construction in the proof of Theorem 5.2 of Agnetis, Mirchandani, Pacciarelli and Pacifici. Given a KNAPSACK instance $(u_1,\dots,u_n;\ w_1,\dots,w_n;\ b,W)$, put
--
--   $$\hat u=\sum_{i=1}^n u_i,\qquad \hat w=\sum_{i=1}^n w_i .$$
--
--   The two-agent instance has
--   1. $n_A=n$ jobs of agent $A$ with processing times $p^A_i=u_i$ and weights $w^A_i=w_i$, $i=1,\dots,n$;
--   2. a single job of agent $B$ with processing time $p^B_1=\hat w\hat u$;
--
--   and the thresholds are the integers
--
--   $$Q_B=b+p^B_1,\qquad Q_A=\hat w\hat u+(\hat w-W)\,p^B_1 \;\bigl(=(1+\hat w-W)\,p^B_1\bigr).$$
--
--   The file also names the $A$-job $J^A_i$ and the single $B$-job $J^B_1$ of the constructed instance.
--
--   This instance is what the two directions (1) and (2) of the proof, and the reduction of Theorem 5.2, are about.
--
--   **Formalization Note** The thresholds are integers: $Q_B<0$ when $b<-p^B_1$, and $Q_A<0$ when $W>\hat w+1$ and $p^B_1>0$. Statements compare completion times with these thresholds cast to $\mathbb R$. The A-job $J^A_{i+1}$ is `Sum.inl i` and the B-job is `Sum.inr 0` (0-based).
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 233, proof of Theorem 5.2

import Mathlib
import Definitions.Def_TwoAgentSched_Knapsack_Model

namespace TwoAgentSched.Knapsack

/-- `û = ∑_{i=1}^n u_i` (proof of Theorem 5.2, p. 233). -/
def uHat {n : ℕ} (u : Fin n → ℕ) : ℕ := ∑ i, u i

/-- `ŵ = ∑_{i=1}^n w_i` (proof of Theorem 5.2, p. 233). -/
def wHat {n : ℕ} (w : Fin n → ℕ) : ℕ := ∑ i, w i

/-- The processing time `p^B_1 = ŵû` of the single B-job (proof of Theorem 5.2, p. 233). -/
def pB1 {n : ℕ} (u w : Fin n → ℕ) : ℕ := wHat w * uHat u

/-- The two-agent instance built from a KNAPSACK instance in the proof of Theorem 5.2 (p. 233):
agent A has `n_A = n` jobs with `p^A_i = u_i` and `w^A_i = w_i`; agent B has one job with
`p^B_1 = ŵû`. -/
def construction {n : ℕ} (u w : Fin n → ℕ) : Instance where
  nA := n
  nB := 1
  pA := u
  wA := w
  pB := fun _ => pB1 u w

/-- The threshold `Q_B = b + p^B_1` (proof of Theorem 5.2, p. 233), an integer, negative when
`b < -p^B_1`. -/
def QB {n : ℕ} (u w : Fin n → ℕ) (b : ℤ) : ℤ := b + (pB1 u w : ℤ)

/-- The threshold `Q_A = ŵû + (ŵ - W) p^B_1` (proof of Theorem 5.2, p. 233; it equals
`(1 + ŵ - W) p^B_1`), an integer, negative when `W > ŵ + 1` and `p^B_1 > 0`. -/
def QA {n : ℕ} (u w : Fin n → ℕ) (W : ℤ) : ℤ :=
  ((wHat w * uHat u : ℕ) : ℤ) + ((wHat w : ℤ) - W) * (pB1 u w : ℤ)

/-- The A-job `J^A_{i+1}` of the constructed instance. -/
def aJob {n : ℕ} (u w : Fin n → ℕ) (i : Fin n) :
    Fin (construction u w).nA ⊕ Fin (construction u w).nB :=
  Sum.inl i

/-- The single B-job `J^B_1` of the constructed instance. -/
def bJob {n : ℕ} (u w : Fin n → ℕ) :
    Fin (construction u w).nA ⊕ Fin (construction u w).nB :=
  Sum.inr ⟨0, Nat.one_pos⟩

end TwoAgentSched.Knapsack


