-- Prove2me | Definitions.Def_ComplexScheduling_JobShop
-- name    : ComplexScheduling_JobShop
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T16:15:38.528771+00:00
-- url     : https://prove2.me/theorems/7dc4a791-44c9-448c-8d1d-9f7490b6630b
-- title:
--   The disjunctive graph model: selections, critical paths, blocks
-- statement:
--   This file fixes the **disjunctive graph model** of the job-shop problem, as used throughout
--   Brucker and Knust's Chapter 4.
--
--   **The graph.** A disjunctive graph $G=(V,C,D)$ is a mixed graph. The vertices $V$ are the
--   operations, including a dummy start $0$ and a dummy end $n+1$, each weighted by its processing
--   time $p_i$. The **conjunctions** $C$ are directed arcs $i\to j$ recording that $j$ is the next
--   operation of the same job, and a conjunction $i\to j$ demands $S_i+p_i\le S_j$ of any feasible
--   schedule. The **disjunctions** $D$ are undirected arcs between operations sharing a machine; a
--   disjunction $i-j$ demands that a feasible schedule satisfy $S_i+p_i\le S_j$ *or*
--   $S_j+p_j\le S_i$.
--
--   **Selections.** Fixing a direction for every disjunction gives a **complete selection** $S$. It
--   is **consistent** when $G(S)=(V,\,C\cup S)$ is acyclic, and the feasible schedules of the job
--   shop are exactly those given by complete consistent selections.
--
--   **Schedules and makespan.** A schedule respects an arc set when every arc $i\to j$ gives
--   $S_i+p_i\le S_j$; the **earliest start schedule** of an arc set is the pointwise smallest such
--   schedule, which is the schedule $S_i:=r_i$ of the source with $r_i$ the length of a longest path
--   from $0$ to $i$. The **length of a path** is the sum of the weights of all its vertices, the last
--   excluded, and a **critical path** is a longest path from $0$ to $n+1$; its length is the
--   makespan.
--
--   **Blocks and critical arcs.** A **machine block** of a critical path is a stretch of at least two
--   consecutive operations of the path that all run on the same machine and that cannot be extended
--   at either end without leaving that machine. A **critical arc** is an arc of the selection joining
--   two operations adjacent on a critical path, and reversing one such arc produces a neighbour in
--   the neighbourhood $N_{ca}$. A selection is **optimal** when no complete consistent selection has
--   a shorter critical path.
--
--   **Formalization Note** Operations are `Fin N` and arcs are `Finset`s of ordered pairs; an
--   undirected disjunction $i-j$ is recorded once in `D`, as a pair, and a complete selection fixes
--   exactly one of its two orientations. Acyclicity is stated directly as "no vertex reaches itself",
--   via the transitive closure of the arc relation, rather than through any path construction. A path
--   is a list of vertices with consecutive entries joined by arcs, so `pathLength` drops the last
--   entry, matching the source's "vertex $i$ excluded". A block is presented as a decomposition
--   `path = pre ++ B ++ post`, which is what makes "consecutive" and "not extendable" expressible;
--   `pre.reverse.take 1` and `post.take 1` are the neighbouring operations, empty at the ends of the
--   path. The machine assignment is a map into an arbitrary type, and the dummy operations are
--   expected to carry machines of their own so that they never extend a block. Makespan appears as
--   the length of an explicitly given critical path rather than as a function of the selection, so
--   that no choice principle or longest-path construction is needed to state a theorem.
-- source:
--   Peter Brucker and Sigrid Knust, Complex Scheduling, 2nd ed., Springer 2012, https://doi.org/10.1007/978-3-642-23929-8 — Section 4.1.2 "The disjunctive graph model", printed pp. 240-241 (PDF pp. 250-251) for the graph, selections, consistency, path lengths and earliest start schedules; Section 4.2, printed pp. 243-245 (PDF pp. 253-255) for critical paths, the neighbourhood N_ca and machine blocks.

import Mathlib

namespace ComplexScheduling

variable {N : ℕ} {M : Type*}

/-- The arc relation of a finite set of directed arcs. -/
def ArcRel (A : Finset (Fin N × Fin N)) : Fin N → Fin N → Prop := fun i j => (i, j) ∈ A

/-- A directed arc set is **acyclic** when no vertex reaches itself along a nonempty path.
Brucker and Knust, *Complex Scheduling*, §4.1.2, p. 241. -/
def AcyclicArcs (A : Finset (Fin N × Fin N)) : Prop :=
  ∀ i : Fin N, ¬ Relation.TransGen (ArcRel A) i i

/-- A **complete selection** for the disjunction set `D`: for each undirected disjunction
`i - j`, listed in `D` as the pair `(i, j)`, exactly one of the two orientations is fixed in `S`,
and `S` fixes nothing else.  Brucker and Knust §4.1.2, p. 241. -/
def CompleteSelection (D S : Finset (Fin N × Fin N)) : Prop :=
  (∀ e ∈ S, e ∈ D ∨ (e.2, e.1) ∈ D) ∧
    ∀ e ∈ D, (e ∈ S ∧ (e.2, e.1) ∉ S) ∨ (e ∉ S ∧ (e.2, e.1) ∈ S)

/-- A complete selection is **consistent** when `G(S) = (V, C ∪ S)` is acyclic.  Brucker and
Knust §4.1.2, p. 241. -/
def ConsistentSelection (Cn D S : Finset (Fin N × Fin N)) : Prop :=
  CompleteSelection D S ∧ AcyclicArcs (Cn ∪ S)

/-- A schedule **respects** an arc set when every arc `i → j` gives `S i + p i ≤ S j`. -/
def RespectsArcs (p : Fin N → ℕ) (A : Finset (Fin N × Fin N)) (St : Fin N → ℕ) : Prop :=
  ∀ e ∈ A, St e.1 + p e.1 ≤ St e.2

/-- `St` is **the earliest start schedule** of the arc set `A`: it respects `A` and starts every
operation no later than any schedule that respects `A`.  This is the schedule `S_i := r_i` of
Brucker and Knust §4.1.2, p. 241, where `r_i` is the length of a longest path from `0` to `i`. -/
def IsEarliestStart (p : Fin N → ℕ) (A : Finset (Fin N × Fin N)) (St : Fin N → ℕ) : Prop :=
  RespectsArcs p A St ∧ ∀ St' : Fin N → ℕ, RespectsArcs p A St' → ∀ i, St i ≤ St' i

/-- A list of vertices is a **path** of the arc set `A` when consecutive entries are joined by
arcs.  The empty list is not a path. -/
def IsPath (A : Finset (Fin N × Fin N)) : List (Fin N) → Prop
  | [] => False
  | [_] => True
  | a :: b :: t => (a, b) ∈ A ∧ IsPath A (b :: t)

/-- The **length of a path**: the sum of the weights of all its vertices, the last excluded.
Brucker and Knust §4.1.2, p. 241. -/
def pathLength (p : Fin N → ℕ) (l : List (Fin N)) : ℕ := (l.dropLast.map p).sum

/-- A **critical path** of `G(S)`: a longest path from the initial dummy operation `src` to the
terminal dummy operation `snk`.  Its length is the makespan.  Brucker and Knust §4.1.2, p. 241
and §4.2, p. 243. -/
def IsCriticalPath (p : Fin N → ℕ) (A : Finset (Fin N × Fin N)) (src snk : Fin N)
    (l : List (Fin N)) : Prop :=
  IsPath A l ∧ l.head? = some src ∧ l.getLast? = some snk ∧
    ∀ l' : List (Fin N), IsPath A l' → l'.head? = some src → l'.getLast? = some snk →
      pathLength p l' ≤ pathLength p l

/-- A **machine block** of the critical path `path`: a contiguous stretch `B` of at least two
operations, all on the same machine, that cannot be extended at either end without leaving that
machine.  The surrounding stretches `pre` and `post` witness the position of `B` in the path, and
`pre.reverse.take 1` and `post.take 1` are the single neighbouring operations, if any.
Brucker and Knust §4.2, p. 245. -/
def IsBlock (μ : Fin N → M) (path pre B post : List (Fin N)) : Prop :=
  path = pre ++ B ++ post ∧ 2 ≤ B.length ∧
    (∀ x ∈ B, ∀ y ∈ B, μ x = μ y) ∧
    (∀ x ∈ pre.reverse.take 1, ∀ y ∈ B, μ x ≠ μ y) ∧
    (∀ x ∈ post.take 1, ∀ y ∈ B, μ x ≠ μ y)

/-- An arc of the selection `S` lying on the critical path — that is, a pair of operations
adjacent on the path: the **critical arcs**, whose reversal generates the neighbourhood `N_ca`.
Brucker and Knust §4.2, p. 244. -/
def IsCriticalArc (S : Finset (Fin N × Fin N)) (l : List (Fin N)) (e : Fin N × Fin N) : Prop :=
  e ∈ S ∧ e ∈ l.zip l.tail

/-- The selection obtained from `S` by reversing the arc `e`. -/
def reverseArc (S : Finset (Fin N × Fin N)) (e : Fin N × Fin N) : Finset (Fin N × Fin N) :=
  insert (e.2, e.1) (S.erase e)

/-- `S'` is a neighbour of `S` in the **critical-arc neighbourhood** `N_ca`: it is obtained from
`S` by reversing a single arc of `S` lying on a critical path of `G(S)`.  Brucker and Knust
§4.2, p. 244. -/
def NcaNeighbour (p : Fin N → ℕ) (Cn : Finset (Fin N × Fin N)) (src snk : Fin N)
    (S S' : Finset (Fin N × Fin N)) : Prop :=
  ∃ (l : List (Fin N)) (e : Fin N × Fin N),
    IsCriticalPath p (Cn ∪ S) src snk l ∧ IsCriticalArc S l e ∧ S' = reverseArc S e

/-- A complete consistent selection is **optimal** when no complete consistent selection has a
shorter critical path, that is, a smaller makespan.  Brucker and Knust §4.1.2, p. 241. -/
def IsOptimalSelection (p : Fin N → ℕ) (Cn D : Finset (Fin N × Fin N)) (src snk : Fin N)
    (S : Finset (Fin N × Fin N)) : Prop :=
  ConsistentSelection Cn D S ∧
    ∀ (T : Finset (Fin N × Fin N)) (l lT : List (Fin N)), ConsistentSelection Cn D T →
      IsCriticalPath p (Cn ∪ S) src snk l → IsCriticalPath p (Cn ∪ T) src snk lT →
        pathLength p l ≤ pathLength p lT

end ComplexScheduling


