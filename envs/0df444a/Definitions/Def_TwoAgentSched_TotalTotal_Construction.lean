-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_Construction
-- name    : TwoAgentSched_TotalTotal_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:13.339525+00:00
-- url     : https://prove2.me/theorems/26c87e26-49e9-443d-9b1e-e3a3b9e21422
-- title:
--   Proof of Theorem 9.2 — identical job sets $p_1,\dots,p_k$, $T$, $Q_A=Q_B$, and the SPT schedules
-- statement:
--   The construction in the proof of Theorem 9.2 of Agnetis, Mirchandani, Pacciarelli and Pacifici. Given a PARTITION instance, the integers $p_1,\dots,p_k$, put
--
--   $$P=\sum_{i=1}^kp_i,\qquad T=3P+4\sum_{i=1}^k(k-i)p_i .$$
--
--   1. The two-agent instance has identical job sets: agent $A$ and agent $B$ each have $k$ jobs, of lengths $p_1,\dots,p_k$.
--   2. The thresholds are $Q_A=Q_B=\tfrac32P+2\sum_{i=1}^k(k-i)p_i$, a real number (a half-integer when $P$ is odd).
--   3. Write $J[i]$ for the pair of jobs $J^A_i,J^B_i$, both of length $p_i$. For a choice, in every pair, of which agent goes first ($A\prec_iB$ or $B\prec_iA$), the **SPT schedule** processes $J[1],J[2],\dots,J[k]$ in this order, the two jobs of each pair consecutively in the chosen order. There are $2^k$ such schedules.
--   4. For such a schedule, $x(0,p_h)=0$ if $A\prec_hB$ and $x(0,p_h)=p_h$ if $B\prec_hA$, and $x=\sum_{h=1}^kx(0,p_h)$.
--
--   These are the objects that the proof of Theorem 9.2 computes with: (5), (6), the value $T$ of every SPT schedule, and the equivalence with PARTITION.
--
--   **Formalization Note** The integers are $p:\mathrm{Fin}\,k\to\mathbb N$, 0-based, so the paper's weight $k-i$ for the 1-based index $i$ is $k-(i+1)$ for the 0-based index. The paper numbers the integers in nondecreasing order; the construction does not sort, and the theorems that use it assume the order as a hypothesis. An SPT schedule is given by $x:\mathrm{Fin}\,k\to\mathrm{Bool}$, with `true` meaning $B\prec_iA$. The paper's alternative reading of "SPT" (lengths nondecreasing along the sequence) is used, explicitly, only in the statement that feasible schedules are SPT.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 237, proof of Theorem 9.2 (construction; SPT schedules; x(0, p_h))

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Model

namespace TwoAgentSched.TotalTotal

/-- The two-agent instance built from the PARTITION integers `p_1, …, p_k` in the proof of
Theorem 9.2 (p. 237): the job sets `J^A` and `J^B` are identical, each with `k` jobs of lengths
`p_1, …, p_k`. Here `p : Fin k → ℕ` is 0-based (`p i` is `p_{i+1}`). -/
def construction {k : ℕ} (p : Fin k → ℕ) : Instance where
  nA := k
  nB := k
  pA := p
  pB := p

/-- `P = ∑_{i=1}^k p_i` (Problem 9.1, p. 237). -/
def bigP {k : ℕ} (p : Fin k → ℕ) : ℕ := ∑ i, p i

/-- `∑_{i=1}^k (k - i) p_i` (proof of Theorem 9.2, p. 237). With 0-based `i : Fin k` the
paper's index is `i + 1`, so the weight is `k - (i + 1)`, which is at most `k - 1`. -/
def weightedSum {k : ℕ} (p : Fin k → ℕ) : ℕ := ∑ i : Fin k, (k - (i.val + 1)) * p i

/-- `T = 3P + 4 ∑_{i=1}^k (k - i) p_i` (proof of Theorem 9.2, p. 237). -/
def bigT {k : ℕ} (p : Fin k → ℕ) : ℕ := 3 * bigP p + 4 * weightedSum p

/-- The common threshold `Q_A = Q_B = (3/2) P + 2 (∑_{i=1}^k (k - i) p_i)` chosen in the proof
of Theorem 9.2 (p. 237), as a real number (a half-integer when `P` is odd). -/
noncomputable def thresholdQ {k : ℕ} (p : Fin k → ℕ) : ℝ :=
  (3 / 2 : ℝ) * (bigP p : ℝ) + 2 * (weightedSum p : ℝ)

/-- The SPT schedule of the constructed instance determined by the choice `x : Fin k → Bool`
(proof of Theorem 9.2, p. 237): the two jobs `J^A_i`, `J^B_i` of length `p_i` (the pair `J[i]`)
are scheduled consecutively, the pairs in the order `J[1], J[2], …, J[k]`; inside `J[i]`,
`x i = false` means `A ≺_i B` (`J^A_i` first) and `x i = true` means `B ≺_i A` (`J^B_i` first).
The `2^k` choices of `x` give the `2^k` SPT schedules. -/
def sptSeq {k : ℕ} (x : Fin k → Bool) : List (Fin k ⊕ Fin k) :=
  (List.finRange k).flatMap
    (fun i => if x i then [Sum.inr i, Sum.inl i] else [Sum.inl i, Sum.inr i])

/-- `x = ∑_{h=1}^k x(0, p_h)` for the SPT schedule given by `x` (proof of Theorem 9.2, p. 237):
`x(0, p_h) = 0` if `A ≺_h B` and `x(0, p_h) = p_h` if `B ≺_h A`. -/
def xSum {k : ℕ} (p : Fin k → ℕ) (x : Fin k → Bool) : ℕ :=
  ∑ h, if x h then p h else 0

end TwoAgentSched.TotalTotal


