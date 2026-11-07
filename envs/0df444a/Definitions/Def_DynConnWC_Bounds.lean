-- Prove2me | Definitions.Def_DynConnWC_Bounds
-- name    : DynConnWC_Bounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:39:33.797293+00:00
-- url     : https://prove2.me/theorems/e01a6bf1-4180-4a22-ac42-e885683644a9
-- title:
--   The resource and correctness predicates of Theorem 1
-- statement:
--   For one tape and one operation sequence, `TimeBounds` says that the program reaches every read and answers every query with $0$ or $1$, that initialization takes at most $Cn\log_2^2n$ steps, each update at most $C\log_2^3n$, and each query at most $C\max(1,\log_2n/\log_2\log_2n)$. `SpaceBound` says that every memory cell touched is below $Cn\log_2^2n$. `DictSpaceBound` says that the cells touched during initialization are below $Cn\log_2^2n$ and those touched during operation $t$ are below $C(m_t+n\log_2^2n)$.
--
--   `PositiveCorrect` says that an answer $1$ to a query is correct. `AdvAllCorrect` says that in the first $N$ rounds against an adversary, every query received the correct answer for the operations actually issued. `Implements` says that a program answers each query as the abstract algorithm does, and `PushesToUniform` says that a map from tapes to random choices turns the tape law into the uniform law.
--
--   These predicates make the statements of Theorem 1, Lemma 24 and Remark 26 readable.
--
--   **Formalization Note** The maximum with $1$ in the query bound is there because $\log_2\log_22=0$, and division by zero would give $0$ at $n=2$; for $n\ge4$ it is inert.
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Theorem 1, p.1 (PDF 2); Lemma 24, p.24 (PDF 25); Remark 26, p.25 (PDF 26)

import Mathlib
import Definitions.Def_DynConnWC_Adversary
import Definitions.Def_DynConnWC_Events

set_option autoImplicit false

namespace DynConnWC

/-! # The resource and correctness predicates of Theorem 1

King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027
submission, sha256 9d16c13e…), Theorem 1, p.1: "O(log³ n) worst-case update time,
O(log n/ log log n) worst-case query time, O(n log² n) words of space, and O(n log² n)
initialization time"; "With an additional dictionary of the current edges, the space is
O(m + n log² n) words, the time bounds are unchanged, and every positive query answer is correct
regardless of the random choices." Lemma 24, p.24.

**Formalization Note.** `log` is `Real.logb 2` (p.4). The query bound is
`C · max(1, log₂ n / log₂ log₂ n)`: at `n = 2`, `log₂ log₂ 2 = 0` and Lean's division by zero would
give `0`; for `n ≥ 4` the maximum is inert. `TimeBounds` says, for one tape and one operation
sequence, that the run reaches every read, answers each query with `0` or `1`, and meets the time
bounds per operation. `SpaceBound` bounds every memory cell touched over the whole run;
`DictSpaceBound` bounds the cells touched during initialization by `C n log² n` and during operation
`t` by `C (m_t + n log² n)`, with `m_t` the number of edges after operation `t`. -/

variable {n : ℕ}

/-- The update bound `C log³ n`. -/
noncomputable def updateBound (C n : ℕ) : ℝ := C * Real.logb 2 n ^ 3

/-- The query bound `C · max(1, log n / log log n)`. -/
noncomputable def queryBound (C n : ℕ) : ℝ :=
  C * max 1 (Real.logb 2 n / Real.logb 2 (Real.logb 2 n))

/-- The space and initialization bound `C n log² n`. -/
noncomputable def spaceBound (C n : ℕ) : ℝ := C * n * Real.logb 2 n ^ 2

/-- On tape `ω` and the sequence `σ`, `Q` reaches every read and answers every query with a word
`0` or `1`; initialization takes at most `C n log² n` steps, every update at most `C log³ n`, every
query at most `C max(1, log n / log log n)`. -/
def TimeBounds (C W : ℕ) (Q : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)) : Prop :=
  RunsThrough W Q n ω σ ∧
  (initTime W Q n ω σ : ℝ) ≤ spaceBound C n ∧
  ∀ (t : ℕ) (ht : t < σ.length),
    (σ[t].IsUpdate → (opTime W Q n ω σ (t + 1) : ℝ) ≤ updateBound C n) ∧
    (¬ σ[t].IsUpdate → (opTime W Q n ω σ (t + 1) : ℝ) ≤ queryBound C n ∧
      (answer W Q n ω σ (t + 1) = some 0 ∨ answer W Q n ω σ (t + 1) = some 1))

/-- On tape `ω` and the sequence `σ`, every memory cell touched is below `C n log² n`. -/
def SpaceBound (C W : ℕ) (Q : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)) : Prop :=
  ∀ a ∈ addrs W Q n ω σ, (a : ℝ) < spaceBound C n

/-- The dictionary space bound: every cell touched during initialization is below `C n log² n`, and
every cell touched during operation `t` is below `C (m_t + n log² n)`. -/
def DictSpaceBound (C W : ℕ) (Q : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)) : Prop :=
  (∀ a ∈ addrsInit W Q n ω σ, (a : ℝ) < spaceBound C n) ∧
  ∀ t, t < σ.length → ∀ a ∈ addrsDuring W Q n ω σ (t + 1),
    (a : ℝ) < C * ((edgeCount σ (t + 1) : ℝ) + n * Real.logb 2 n ^ 2)

/-- Every positive answer of `Q` on `σ` is correct: if the answer to the query `σ[t] = (u, v)` is
`1`, then `u` and `v` are connected in the graph at that time. -/
def PositiveCorrect (W : ℕ) (Q : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)) : Prop :=
  ∀ (t : ℕ) (ht : t < σ.length) (u v : Fin n), σ[t] = .query u v →
    answer W Q n ω σ (t + 1) = some 1 → (graphAt σ t).Reachable u v

/-- In the first `N` rounds of the adversary `A` against `Q` on tape `ω`, every query received the
correct answer for the graph of the operations actually issued before it. -/
def AdvAllCorrect (W : ℕ) (Q : Program) (A : Adversary n) (N : ℕ) (ω : ℕ → Fin (2 ^ W)) : Prop :=
  ∀ (t : ℕ) (ht : t < (advHist A Q W ω N).length) (u v : Fin n),
    ((advHist A Q W ω N)[t]).1 = .query u v →
    ((advHist A Q W ω N)[t]).2 = some (correctBit (graphAt (advOps A Q W ω N) t) u v)

/-- The program `Q` carries out the algorithm with setup `S` and random choices `R` on the sequence
`ops`: it reaches every read, and its answer to each query is the algorithm's answer. -/
def Implements (W : ℕ) (Q : Program) (n : ℕ) (ω : ℕ → Fin (2 ^ W)) (ops : List (Op n))
    (S : AlgSetup n) (R : RandChoices S) : Prop :=
  RunsThrough W Q n ω ops ∧
  ∀ (t : ℕ) (ht : t < ops.length) (u v : Fin n), ops[t] = .query u v →
    answer W Q n ω ops (t + 1) = some (algBit S R ops t u v)

/-- The map `ρ` from tapes to random choices turns the law of the tape into the uniform law on the
random choices: each fibre is an event of the probability of that outcome. -/
def PushesToUniform (W : ℕ) (S : AlgSetup n) (ρ : (ℕ → Fin (2 ^ W)) → RandChoices S) : Prop :=
  ∀ R, MeasurableSet {ω | ρ ω = R} ∧ tapeLaw W {ω | ρ ω = R} = randLaw S R

end DynConnWC


