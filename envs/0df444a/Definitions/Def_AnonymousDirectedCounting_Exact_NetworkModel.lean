-- Prove2me | Definitions.Def_AnonymousDirectedCounting_Exact_NetworkModel
-- name    : AnonymousDirectedCounting_Exact_NetworkModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:03.11983+00:00
-- url     : https://prove2.me/theorems/3c6bc3ac-b44c-429b-8cd5-17be108ef6ec
-- title:
--   Anonymous directed networks and silent-halting protocol executions
-- statement:
--   A dynamic network has a fixed set $V$ of $n$ agents, a nonempty set $L$ of leaders, and a directed multigraph $G_r$ in each communication round $r\ge1$. Put $\ell=|L|$. The graph is represented by natural arc multiplicities $e_r(x,y)$, allowing loops, parallel arcs and arbitrary finite degrees. Admissibility requires $n\ge1$ and the cut condition
--   $$
--   \sum_{x\in X}\sum_{y\in V\setminus X} e_r(x,y)>0
--   \qquad(\varnothing\ne X\subsetneq V,\ r\ge1).
--   $$
--   A protocol has an arbitrary state space. All agents use the same initial-state, update and output rules. The only common parameter is $\ell$; the initial state depends on the agent's leader status. In round $r$, an active agent receives the multiset of old states sent by active agents and then learns its current outdegree. It updates and may output a natural number. An output is stored permanently, and the agent subsequently neither sends nor updates. No vertex is removed from the exogenous graphs.
--
--   The definitions include universal Counting correctness and simultaneous termination at a round, the arc promise, the structural clause of Theorem 4, the arc bundles of the Lemma 8 graph, and the function $T(n,\ell)$, which is $n$ when $n=\ell$, $2n-1$ when $n>\ell=1$, and $2n-2$ otherwise. $T$ is a formula, not a definition of an optimum.
--
--   **Formalization Note** `Fin n` is external indexing only: neither indices nor $n$ occur in protocol inputs. The initial states are an arbitrary relabeling of the source's $1$ and $0$. Round zero of the schedule is unused.
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Section 2, printed p. 3 (PDF p. 5); Lemma 8 and Theorem 4, printed p. 21 (PDF p. 23)

import Mathlib

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Section 2, printed p. 3 (PDF p. 5). Multiplicities are arbitrary finite naturals.
Round zero of the schedule is unused. Vertex indices belong only to the semantics. -/
structure NetworkModel (n : ℕ) where
  arcs : ℕ → Fin n → Fin n → ℕ
  leaders : Finset (Fin n)

def outdegree {n : ℕ} (G : NetworkModel n) (r : ℕ) (x : Fin n) : ℕ :=
  ∑ y : Fin n, G.arcs r x y

/-- The paper's cut condition, including its vacuous singleton case. -/
def StronglyConnected {n : ℕ} (e : Fin n → Fin n → ℕ) : Prop :=
  ∀ X : Finset (Fin n), X.Nonempty → X ≠ Finset.univ →
    0 < ∑ x ∈ X, ∑ y ∈ Finset.univ \ X, e x y

def Admissible {n : ℕ} (G : NetworkModel n) : Prop :=
  0 < n ∧ G.leaders.Nonempty ∧ ∀ r : ℕ, 1 ≤ r → StronglyConnected (G.arcs r)

/-- An unrestricted deterministic anonymous protocol. The common parameter is the
leader count, never the population or a vertex name. The update sees degree only after
the old states have been sent. Initial states depend solely on leader status. -/
structure Protocol (S : Type*) where
  initial : Bool → S
  update : ℕ → S → Multiset S → ℕ → S
  output : S → ℕ → Option ℕ

/-- The second component records the unique output, if any. -/
abbrev Cell (S : Type*) := S × Option ℕ

noncomputable def received {n : ℕ} {S : Type*} (G : NetworkModel n)
    (r : ℕ) (s : Fin n → Cell S) (x : Fin n) : Multiset S := by
  classical
  exact ∑ y : Fin n,
    if (s y).2.isSome then 0 else Multiset.replicate (G.arcs r y x) (s y).1

/-- Silent halting: a halted cell is frozen and contributes no messages thereafter.
Exogenous graphs still include all vertices. Outputs are tested only after an update. -/
noncomputable def execution {n : ℕ} {S : Type*} (A : Protocol S)
    (G : NetworkModel n) : ℕ → Fin n → Cell S
  | 0, x => (A.initial (decide (x ∈ G.leaders)), none)
  | t + 1, x =>
    let old := execution A G t
    if (old x).2.isSome then old x
    else
      let s := A.update G.leaders.card (old x).1
        (received G (t + 1) old x) (outdegree G (t + 1) x)
      (s, A.output s G.leaders.card)

/-- Correctness is universal in size, leader set, and schedule. A wrong early output
cannot later be corrected because execution freezes the cell. -/
def SolvesCounting {S : Type*} (A : Protocol S) : Prop :=
  ∀ n : ℕ, ∀ G : NetworkModel n, Admissible G →
    ∀ x : Fin n, ∃ t : ℕ, 1 ≤ t ∧ (execution A G t x).2 = some n

def AllHalted {n : ℕ} {S : Type*} (A : Protocol S)
    (G : NetworkModel n) (t : ℕ) : Prop :=
  ∀ x : Fin n, (execution A G t x).2.isSome = true

def SimultaneousCountingAt {n : ℕ} {S : Type*} (A : Protocol S)
    (G : NetworkModel n) (t : ℕ) : Prop :=
  1 ≤ t ∧ ∀ x : Fin n,
    (∀ r : ℕ, r < t → (execution A G r x).2 = none) ∧
      (execution A G t x).2 = some n

/-- The arc promise of the complexity clause: every round has at most `B` arcs in total. -/
def ArcsPerRoundAtMost {n : ℕ} (G : NetworkModel n) (B : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∑ x : Fin n, ∑ y : Fin n, G.arcs r x y ≤ B

/-- Theorem 4's structural clause (printed p. 21, PDF p. 23): every round graph is loopless, with
arc multiplicities at most `ell` and outdegrees at most `ell ^ 2`. -/
def LooplessBoundedRounds {n : ℕ} (G : NetworkModel n) (ell : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → (∀ x : Fin n, G.arcs r x x = 0) ∧
    (∀ x y : Fin n, G.arcs r x y ≤ ell) ∧ ∀ x : Fin n, outdegree G r x ≤ ell ^ 2

/-- The graph of Lemma 8 (printed p. 21, PDF p. 23), exactly the four arc bundles
`z -c-> W`, `z' -1-> U`, `U \ {z} -(ell/c)-> z`, `W \ {z'} -ell-> z`, each adding to the multiplicity. -/
def gadgetArcs {n : ℕ} (U W : Finset (Fin n)) (z z' : Fin n) (c ell : ℕ) :
    Fin n → Fin n → ℕ := fun x y =>
  (if x = z ∧ y ∈ W then c else 0) + (if x = z' ∧ y ∈ U then 1 else 0) +
    (if x ∈ U ∧ x ≠ z ∧ y = z then ell / c else 0) +
    (if x ∈ W ∧ x ≠ z' ∧ y = z then ell else 0)

/-- The claimed formula, used as a bound only; it does not define an optimum. -/
def sharpTime (n ell : ℕ) : ℕ :=
  if n = ell then n else if ell = 1 then 2 * n - 1 else 2 * n - 2

end AnonymousDirectedCounting.Exact


