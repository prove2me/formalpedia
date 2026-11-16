-- Prove2me | Definitions.Def_LocalPush_Supplement_QueryAlg
-- name    : LocalPush_Supplement_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:18:57.006333+00:00
-- url     : https://prove2.me/theorems/c5c15715-1098-40c3-a10f-d4239ebb2168
-- title:
--   Randomized adaptive query algorithms, success probability and expected query cost
-- statement:
--   The model of the lower bounds (Theorems 7.1 and 7.4). An **input** is a graph on nodes $\{0,\dots,N-1\}$ given by adjacency lists, together with two marked nodes $s,t$. An algorithm may ask four kinds of **queries**:
--
--   1. the degree $d(v)$ of a node $v$;
--   2. the $i$-th entry of the adjacency list of $v$ ($-1$ if there is none);
--   3. whether $\{u,v\}$ is an edge;
--   4. a uniformly random node, independent of everything else.
--
--   A **randomized adaptive query algorithm** receives $s,t$ and a fair-coin tape, and maps the history of (query, answer) pairs to its next query or to a halt with a real output; its internal computation is unrestricted. Every probability distribution over deterministic adaptive strategies has this form. Its decisions are required to be measurable functions of the coin tape, so that success probabilities are probabilities of events.
--
--   The algorithm **succeeds** on an input for a given error criterion if, with probability at least $2/3$ over its coins and the uniform samples, it halts with an output meeting the criterion. Its **cost** on an input is the expected number of queries made before halting, which is $+\infty$ if it fails to halt with positive probability.
--
--   **Formalization Note** A query is encoded as a triple $(\mathrm{tag},a,b)\in\{0,1,2,3\}\times\mathbb N\times\mathbb N$; answers are integers (degree and neighbour answers as in the base machine, $-1$ on invalid arguments; adjacency $1/0$; samples drawn from a tape of independent uniform reals in $[0,1]$).
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), Theorem 7.1, p.38 (PDF p.38) (query types); Theorem 7.4, p.42 (PDF p.42) ("with unrestricted internal computation")

import Mathlib
import Definitions.Def_LocalPush_Supplement_SampleMachine

open MeasureTheory

namespace LocalPush

namespace Supplement

/-!
# Randomized adaptive query algorithms and their expected query cost (lower-bound model)

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), Theorem 7.1, p.38 (PDF p.38): "The
algorithm can be given the values of n and m, can use degree queries, neighbor queries, adjacency queries, and
uniform node samples, and can also access the neighbor lists sorted by degree"; Theorem 7.4, p.42 (PDF p.42):
"The algorithm may use degree queries, indexed-neighbor queries, adjacency tests, and uniform node samples,
with unrestricted internal computation."

**Formalization Note.**
* An input `QInput` is a graph on `Fin N` given by adjacency lists, with two marked nodes `s`, `t`.
* A query is a triple `(tag, a, b) ∈ Fin 4 × ℕ × ℕ`: tag `0` is a degree query on node `a`; tag `1` asks for
  entry `b` (0-based) of the list of node `a`; tag `2` asks whether `{a, b}` is an edge; tag `3` asks for a
  uniformly random node (`a`, `b` ignored). The answers (`answer`) are the base `degAnswer` / `nbrAnswer`
  (`−1` on an invalid node or position), `1`/`0` for adjacency (`0` on invalid nodes), and the index
  `uniformIndex (σ_j) N` for the `j`-th sample, where `σ` is a tape of independent uniform reals in `[0, 1]`
  independent of everything else.
* A randomized algorithm `A : QueryAlg` maps its fair-coin tape `ω`, the two marked nodes, and the history of
  (query, answer) pairs to the next query (`Sum.inl`) or to a halt with a real output (`Sum.inr`). Internal
  computation is unrestricted (any function). Any probability distribution over deterministic strategies is
  of this form, as the space of strategies is standard Borel. `IsMeasurable` asks that each decision be a
  measurable function of the coin tape, so that success probabilities are probabilities of events.
* `queriesToHalt` is the number of queries made before halting (`∞` if the algorithm never halts), and
  `qcost A I` is its expectation over `jointTape` (coins `ω` and samples `σ`), in `ℝ≥0∞`.
* `Succeeds A I good`: with probability at least `2/3` the algorithm halts with an output satisfying `good`.
-/

/-- An input of the lower-bound model: adjacency lists on `Fin N` and two marked nodes. -/
structure QInput where
  N : ℕ
  nbrs : Fin N → List (Fin N)
  s : Fin N
  t : Fin N

/-- A query `(tag, a, b)`: degree (`0`), neighbor (`1`), adjacency (`2`), uniform node sample (`3`). -/
abbrev Query := Fin 4 × ℕ × ℕ

/-- A history: the list of (query, answer) pairs so far. -/
abbrev History := List (Query × ℤ)

/-- A randomized adaptive query algorithm with unrestricted internal computation. -/
abbrev QueryAlg := (ℕ → Bool) → ℕ → ℕ → History → Query ⊕ ℝ

/-- Each decision of the algorithm is a measurable function of its coin tape. -/
def QueryAlg.IsMeasurable (A : QueryAlg) : Prop :=
  ∀ (a b : ℕ) (h : History), Measurable fun ω => A ω a b h

/-- The answer to query `q` on input `I`, given the uniform tape `σ` and the history `h` so far. -/
noncomputable def answer (I : QInput) (σ : ℕ → unitInterval) (h : History) (q : Query) : ℤ :=
  if q.1 = 0 then degAnswer I.nbrs (q.2.1 : ℤ)
  else if q.1 = 1 then nbrAnswer I.nbrs (q.2.1 : ℤ) (q.2.2 : ℤ)
  else if q.1 = 2 then
    match nodeOf I.N (q.2.1 : ℤ), nodeOf I.N (q.2.2 : ℤ) with
    | some u, some v => if v ∈ I.nbrs u then 1 else 0
    | _, _ => 0
  else uniformIndex (σ (h.filter fun x => x.1.1 = 3).length) (I.N : ℤ)

/-- The history after `k` rounds: each round appends the next query and its answer, until `A` halts. -/
noncomputable def hist (A : QueryAlg) (I : QInput) (ω : ℕ → Bool) (σ : ℕ → unitInterval) : ℕ → History
  | 0 => []
  | k + 1 =>
    match A ω I.s I.t (hist A I ω σ k) with
    | .inl q => hist A I ω σ k ++ [(q, answer I σ (hist A I ω σ k) q)]
    | .inr _ => hist A I ω σ k

/-- The number of queries made before halting, or `∞` if `A` never halts. -/
noncomputable def queriesToHalt (A : QueryAlg) (I : QInput) (p : (ℕ → Bool) × (ℕ → unitInterval)) :
    ENNReal :=
  ⨅ (k : ℕ) (_ : (A p.1 I.s I.t (hist A I p.1 p.2 k)).isRight = true), (k : ENNReal)

/-- The expected number of queries of `A` on `I`. -/
noncomputable def qcost (A : QueryAlg) (I : QInput) : ENNReal :=
  ∫⁻ p, queriesToHalt A I p ∂jointTape

/-- With probability at least `2/3`, `A` halts on `I` with an output satisfying `good`. -/
def Succeeds (A : QueryAlg) (I : QInput) (good : ℝ → Prop) : Prop :=
  (2 / 3 : ENNReal) ≤ jointTape {p | ∃ (k : ℕ) (y : ℝ),
    A p.1 I.s I.t (hist A I p.1 p.2 k) = Sum.inr y ∧ good y}

end Supplement

end LocalPush


