-- Prove2me | Definitions.Def_GTWSched_NPC_Schedules
-- name    : GTWSched_NPC_Schedules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:11:54.856+00:00
-- url     : https://prove2.me/theorems/7deb65bc-5a67-4ef7-8382-76210033a799
-- title:
--   §1, §2.1, pp. 330–336 — one-processor schedules, midtimes, total discrepancy, A(S), B(S), ordered, no gaps, brackets, and k
-- statement:
--   This file fixes the scheduling objects of §1 and §2.1 of Garey, Tarjan and Wilfong (1988).
--
--   **Schedules.** There are $N$ tasks $T_1,\dots,T_N$; task $T_i$ has a length $l_i$. A **schedule** $S$ assigns every task a starting time $s_i\ge 0$ such that the execution intervals $[s_i,s_i+l_i]$ and $[s_j,s_j+l_j]$ of two distinct tasks intersect at most in endpoints, i.e. $s_i+l_i\le s_j$ or $s_j+l_j\le s_i$. All times are real numbers. The **midtime** of $T_i$ in $S$ is $m_i(S)=s_i+l_i/2$.
--
--   **Total discrepancy.** Given preferred midtimes $M_1,\dots,M_N$, the cost of $S$ is
--   $$\mathrm{cost}(S)=\sum_{i=1}^N |m_i(S)-M_i|,$$
--   and the question of the total discrepancy problem with threshold $k$ is whether some schedule has $\mathrm{cost}(S)\le k$.
--
--   **The special case of Lemmas 2–6 (p. 333).** For tasks $T_0,T_1,\dots,T_{2n}$ sharing one preferred midtime $M$, the cost is $\mathrm{cost}(S)=\sum_{i=0}^{2n}|M-m_i(S)|$; a **minimum cost schedule** is a schedule whose cost is at most that of every schedule of the same tasks. The file defines
--   1. $A(S)=\{T_i : m_i(S)<M\}$ and $B(S)=\{T_i : m_i(S)>M\}$;
--   2. $S$ is **ordered** if $T_i,T_j\in A(S)$ and $l_i<l_j$ imply $m_i(S)>m_j(S)$, and $T_i,T_j\in B(S)$ and $l_i<l_j$ imply $m_i(S)<m_j(S)$;
--   3. $S$ has **no gaps** if every task either starts first or starts exactly when another task finishes;
--   4. the **bracket schedule** $[A_n,\dots,A_1,T_0@M,B_1,\dots,B_n]$ (p. 334): $T_0$ has midtime $M$, the tasks $B_1,B_2,\dots$ follow it and the tasks $A_1,A_2,\dots$ precede it (with $A_1$ nearest), packed without gaps, so $T_0$ starts at $M-l_0/2$, $B_k$ at $M+l_0/2+\sum_{j<k}l(B_j)$ and $A_k$ at $M-l_0/2-\sum_{j\le k}l(A_j)$;
--   5. the threshold of p. 336,
--   $$k=\sum_{i=1}^n (l_{2i}+l_{2i-1})\left(n-i+\tfrac12\right)+l_0\,n .$$
--
--   These are the objects of the NP-completeness proof of THEOREM 1.
--
--   **Formalization Note** Tasks are indexed by `Fin N`, 0-based. In the special case the tasks are `Fin (2n+1)` and $T_i$ is index $i$, so $T_0$ is index `0`; the paper's $T_{2i-1}$ and $T_{2i}$ ($1\le i\le n$) are `oddTask k` and `evenTask k` with $k=i-1$, the indices $2k+1$ and $2k+2$. In `kStar` the summand for $k=i-1$ is $(l_{2k+2}+l_{2k+1})(n-k-\tfrac12)$, which is the paper's $(l_{2i}+l_{2i-1})(n-i+\tfrac12)$. Nonnegative starting times are a standing assumption the paper uses but does not write into its model ("scheduled between 0 and $M-l_0/2$", p. 336; "illegally starting a task before time 0", p. 337). The nonoverlap condition "intersect only at their endpoints" is read as "one task finishes before the other starts"; for a task of length zero this also forbids sitting strictly inside another task. A bracket is given by injective maps `A B : Fin n → Fin (2n+1)` with disjoint ranges avoiding `0` (`IsBracket`), and `A k` is the paper's $A_{k+1}$. The paper defines the bracket as "the minimum cost schedule that has the tasks scheduled in the order indicated and that has task $T$ scheduled with its midtime at $M$"; `centered` is the packed schedule, which is that schedule because packing places every task as near to $M$ as the order allows.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 330 §1 (model); p. 332 §2.1 (midtimes, total discrepancy); p. 333 (special case, A(S), B(S), no gaps, ordered); p. 334 (bracket notation); p. 336 (threshold k)

import Mathlib

namespace GTWSched.NPC

/-! # One-processor schedules, midtimes and the total discrepancy (Garey, Tarjan & Wilfong 1988, §1, §2.1)

Tasks are indexed by `Fin N` (0-based). Every task `i` has a length `l i` and a schedule assigns it a
starting time `s i`; all times are real numbers. -/

noncomputable section

/-- A schedule of tasks with lengths `l` on one processor (§1, p. 330): every starting time is
nonnegative, and the execution intervals `[s i, s i + l i]` and `[s j, s j + l j]` of two distinct
tasks intersect at most in endpoints, i.e. one task finishes before the other starts. -/
def IsSchedule {N : ℕ} (l s : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ s i) ∧ ∀ i j, i ≠ j → s i + l i ≤ s j ∨ s j + l j ≤ s i

/-- The actual midtime `mᵢ(S) = sᵢ + lᵢ/2` of task `i` in the schedule `s` (§2.1, p. 332). -/
def mid {N : ℕ} (l s : Fin N → ℝ) (i : Fin N) : ℝ := s i + l i / 2

/-- The total discrepancy `cost(S) = ∑ᵢ |mᵢ(S) − Mᵢ|` of the schedule `s` with respect to the
preferred midtimes `M` (§2.1, p. 332). -/
def midCost {N : ℕ} (l M s : Fin N → ℝ) : ℝ := ∑ i, |mid l s i - M i|

/-- The question of the total discrepancy problem (§2.1, p. 332) for lengths `l`, preferred midtimes
`M` and threshold `k`: is there a schedule `S` with `cost(S) ≤ k`? Starting times are real. -/
def TDYesReal {N : ℕ} (l M : Fin N → ℝ) (k : ℝ) : Prop :=
  ∃ s, IsSchedule l s ∧ midCost l M s ≤ k

/-! ## The special case of Lemmas 2–6 (p. 333): one common preferred midtime `M` -/

/-- The cost `cost(S) = ∑ᵢ |M − mᵢ(S)|` of a schedule when all tasks share the preferred midtime
`M` (p. 333). -/
def commonCost {N : ℕ} (l : Fin N → ℝ) (M : ℝ) (s : Fin N → ℝ) : ℝ := ∑ i, |M - mid l s i|

/-- `s` is a minimum cost schedule for the common preferred midtime `M`: it is a schedule, and no
schedule of the same tasks has smaller cost. -/
def IsMinCost {N : ℕ} (l : Fin N → ℝ) (M : ℝ) (s : Fin N → ℝ) : Prop :=
  IsSchedule l s ∧ ∀ s', IsSchedule l s' → commonCost l M s ≤ commonCost l M s'

/-- `A(S) = {Tᵢ : mᵢ(S) < M}` (p. 333). -/
def setA {N : ℕ} (l : Fin N → ℝ) (M : ℝ) (s : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => mid l s i < M

/-- `B(S) = {Tᵢ : mᵢ(S) > M}` (p. 333). -/
def setB {N : ℕ} (l : Fin N → ℝ) (M : ℝ) (s : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => M < mid l s i

/-- `s` is ordered (p. 333): if `Tᵢ, Tⱼ ∈ A(S)` and `lᵢ < lⱼ` then `mᵢ(S) > mⱼ(S)`, and if
`Tᵢ, Tⱼ ∈ B(S)` and `lᵢ < lⱼ` then `mᵢ(S) < mⱼ(S)`. -/
def Ordered {N : ℕ} (l : Fin N → ℝ) (M : ℝ) (s : Fin N → ℝ) : Prop :=
  (∀ i j, i ∈ setA l M s → j ∈ setA l M s → l i < l j → mid l s j < mid l s i) ∧
  (∀ i j, i ∈ setB l M s → j ∈ setB l M s → l i < l j → mid l s i < mid l s j)

/-- `s` has no gaps between tasks (p. 333): every task either starts first (no task starts
earlier) or starts exactly when another task finishes. -/
def NoGaps {N : ℕ} (l s : Fin N → ℝ) : Prop :=
  ∀ i, (∀ j, s i ≤ s j) ∨ ∃ j, j ≠ i ∧ s j + l j = s i

/-- The task `T_{2i−1}` of the paper, for the paper's `i = k + 1` (`k : Fin n` is 0-based): the
index `2k + 1` of `Fin (2n+1)`. -/
def oddTask {n : ℕ} (k : Fin n) : Fin (2 * n + 1) := ⟨2 * k.val + 1, by have := k.isLt; omega⟩

/-- The task `T_{2i}` of the paper, for the paper's `i = k + 1` (`k : Fin n` is 0-based): the
index `2k + 2` of `Fin (2n+1)`. -/
def evenTask {n : ℕ} (k : Fin n) : Fin (2 * n + 1) := ⟨2 * k.val + 2, by have := k.isLt; omega⟩

/-- The paper's threshold `k = ∑ᵢ₌₁ⁿ (l₂ᵢ + l₂ᵢ₋₁)(n − i + 1/2) + (l₀)n` (p. 336) for tasks
`T₀, …, T₂ₙ`. With the 0-based `j = i − 1` the summand is `(l_{2j+2} + l_{2j+1})(n − j − 1/2)`. -/
def kStar {n : ℕ} (l : Fin (2 * n + 1) → ℝ) : ℝ :=
  (∑ j : Fin n, (l (evenTask j) + l (oddTask j)) * ((n : ℝ) - (j : ℝ) - 1 / 2)) + l 0 * n

/-- `A, B : Fin n → Fin (2n+1)` list the tasks of a bracket `[Aₙ, …, A₁, T₀@M, B₁, …, Bₙ]`
(p. 334, 0-based: the paper's `Aᵢ` is `A (i − 1)`): both are injective, no task is in both lists,
and `T₀` (index `0`) is in neither. Then together with `T₀` they list every task exactly once. -/
def IsBracket {n : ℕ} (A B : Fin n → Fin (2 * n + 1)) : Prop :=
  Function.Injective A ∧ Function.Injective B ∧ (∀ i j, A i ≠ B j) ∧ ∀ i, A i ≠ 0 ∧ B i ≠ 0

/-- The schedule `[Aₙ, …, A₁, T₀@M, B₁, …, Bₙ]` (p. 334): `T₀` has its midtime at `M`, the tasks
`B₁, B₂, …` follow it in this order and the tasks `A₁, A₂, …` precede it in this order (`A₁`
nearest to `T₀`), all without gaps. This is the minimum cost schedule with this order and `T₀` at
`M`, since packing the tasks against `T₀` puts each one as near to `M` as the order allows.
Starting times: `M − l₀/2` for `T₀`; `M + l₀/2 + ∑_{j<k} l(B_j)` for `B_k`;
`M − l₀/2 − ∑_{j≤k} l(A_j)` for `A_k`. -/
def centered {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (A B : Fin n → Fin (2 * n + 1))
    (t : Fin (2 * n + 1)) : ℝ :=
  if hA : ∃ k, A k = t then
    M - l 0 / 2 - ∑ j ∈ Finset.univ.filter (fun j => j ≤ hA.choose), l (A j)
  else if hB : ∃ k, B k = t then
    M + l 0 / 2 + ∑ j ∈ Finset.univ.filter (fun j => j < hB.choose), l (B j)
  else M - l 0 / 2

end

end GTWSched.NPC


