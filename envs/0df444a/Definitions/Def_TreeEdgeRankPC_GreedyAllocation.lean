-- Prove2me | Definitions.Def_TreeEdgeRankPC_GreedyAllocation
-- name    : TreeEdgeRankPC_GreedyAllocation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:25.339204+00:00
-- url     : https://prove2.me/theorems/5e6db9e6-5755-456e-9613-7c613e586199
-- title:
--   GreedyAllocation and the greedy procedure
-- statement:
--   An instance of **GreedyAllocation** is an integer $K\ge 1$ and $d\ge 1$ positive integer requirements $q_1,\dots,q_d$. It is **feasible** if there is a partition $X_1,\dots,X_d$ of $[K]$ with
--   $$\sum_{x\in X_j}2^{x-1}\ge q_j\qquad(j=1,\dots,d).$$
--
--   The **greedy procedure** maintains a residual for each requirement, initially $q_i$; a requirement is covered when its residual becomes zero, and it is then removed. It processes the clocks $e=K-1,\dots,0$. At clock $e$:
--
--   1. **Reject** if some residual is at least $2^{e+1}$, or two residuals are at least $2^e$.
--   2. **Subtract** otherwise, if exactly one residual is at least $2^e$: subtract $2^e$ from it.
--   3. **Cover** otherwise, if a positive residual remains: give $2^e$ to a requirement with the largest residual and cover it, breaking ties arbitrarily.
--
--   If no positive residual remains, the remaining weights are allocated arbitrarily.
--
--   GreedyAllocation is the intermediate problem of the reduction, and the greedy procedure is what the circuit simulation runs on.
--
--   **Formalization Note** The ranks $x\in[K]$ appear 0-based as `x : Fin K`, with weight $2^x$. A map $\sigma:[K]\to[d]$ is a partition into labelled parts. Residuals form a multiset of positive integers: covering any one of several equal residuals leaves the same multiset, so the procedure is a function of the multiset and tie-breaking disappears. The value `none` is rejection. `runClocks hi lo` processes clocks $hi, hi-1,\dots,lo$, both ends included. `encGA K q` is `encNat K` followed by `encNat` of each requirement.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Definition 4.2, p.14; Definition 4.7, pp.16–17

import Mathlib
import Definitions.Def_TreeEdgeRankPC_Circuit

namespace TreeEdgeRankPC

/-- An instance `⟨K; q₁, …, q_d⟩` as specified in **GreedyAllocation**, Definition 4.2, p.14
(arXiv:2610.12438, held version of 2026-11-02, sha256 9e04ca7b…): "an integer K ≥ 1 and d ≥ 1 positive
integer requirements q1, ..., qd". -/
def GAValid (K : ℕ) (q : List ℕ) : Prop := 1 ≤ K ∧ q ≠ [] ∧ ∀ a ∈ q, 1 ≤ a

/-- Feasibility in **GreedyAllocation**, Definition 4.2, p.14: "there exists a partition X1, ..., Xd of
[K], such that Σ_{x∈Xj} 2^{x−1} ≥ qj for each j = 1, ..., d."

**Formalization Note.** The 0-based `x : Fin K` stands for the paper's rank `x + 1 ∈ [K]`, with weight
`2^x = 2^{(x+1)−1}`. A map `σ : Fin K → Fin d` is a partition into `d` labelled parts. A part may be
empty a priori, but positive requirements force every part to be nonempty on a valid instance. -/
def GAFeasible (K : ℕ) (q : List ℕ) : Prop :=
  ∃ σ : Fin K → Fin q.length, ∀ j : Fin q.length,
    q[j] ≤ ∑ x ∈ Finset.univ.filter (fun x => σ x = j), 2 ^ (x : ℕ)

/-- The binary code of `⟨K; q₁, …, q_d⟩`: `encNat K` followed by `encNat qᵢ` in order. It is injective
because `encNat` is prefix-free. Numbers are in binary, as Lemma 4.6's "O(m) bits each" requires. -/
def encGA (K : ℕ) (q : List ℕ) : List Bool := encNat K ++ q.flatMap encNat

/-- The **language GreedyAllocation** over `{0, 1}`: codes of valid feasible instances. -/
def GreedyAllocation : Set (List Bool) :=
  {s | ∃ (K : ℕ) (q : List ℕ), GAValid K q ∧ s = encGA K q ∧ GAFeasible K q}

/-- Clock `e` of the **greedy procedure**, Definition 4.7, p.17: "Reject. If some residual is at least
2^{e+1}, or two residuals are at least 2^e, reject. Subtract. Otherwise, if exactly one residual is at
least 2^e, subtract 2^e from it. Cover. Otherwise, if a positive residual remains, give 2^e to a
requirement with the largest residual and cover it. Break ties arbitrarily." Result `none` is rejection.

**Formalization Note.** Residuals form a multiset of positive integers: "A requirement is covered when
its residual becomes zero and is then removed" (pp.16–17). Covering any one of several equal residuals
leaves the same multiset, so the procedure is a function of the multiset and tie-breaking disappears. -/
def greedyStep (e : ℕ) (M : Multiset ℕ) : Option (Multiset ℕ) :=
  if 1 ≤ M.countP (2 ^ (e + 1) ≤ ·) ∨ 2 ≤ M.countP (2 ^ e ≤ ·) then none
  else if M.countP (2 ^ e ≤ ·) = 1 then
    some ((M.map fun r => if 2 ^ e ≤ r then r - 2 ^ e else r).filter (0 < ·))
  else some (M.erase M.sup)

/-- Process `n` clocks `e, e - 1, …, e - n + 1` in this order, stopping at the first rejection. -/
def runClocksN : ℕ → ℕ → Multiset ℕ → Option (Multiset ℕ)
  | 0, _, M => some M
  | n + 1, e, M => (greedyStep e M).bind (runClocksN n (e - 1))

/-- Process the clocks `hi, hi - 1, …, lo`, both ends included. -/
def runClocks (hi lo : ℕ) (M : Multiset ℕ) : Option (Multiset ℕ) :=
  runClocksN (hi + 1 - lo) hi M

/-- The **greedy procedure**, Definition 4.7, p.17: clocks `e = K − 1, …, 0` from the initial residuals
`qᵢ`. The run has rejected exactly when the value is `none`.

**Formalization Note.** If no positive residual remains, `greedyStep` leaves the empty multiset alone:
"allocate the remaining weights arbitrarily". -/
def greedyRun (K : ℕ) (q : List ℕ) : Option (Multiset ℕ) :=
  runClocksN K (K - 1) (q : Multiset ℕ)

end TreeEdgeRankPC


