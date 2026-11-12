-- Prove2me | Definitions.Def_PDynTreeEmbed_Main_Dynamic
-- name    : PDynTreeEmbed_Main_Dynamic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:31:18.45873+00:00
-- url     : https://prove2.me/theorems/bd93b0e3-89e1-432b-9236-621ff41e2449
-- title:
--   Partially dynamic algorithms on the word RAM: input words, online runs, total time, recourse, and the maintained tree, partition and estimates as replays of change records
-- statement:
--   Algorithms run on the published word RAM `DynBrooks_Machine`: a program is a finite list of instructions over words of $a\lceil\log_2(n+2)\rceil$ bits (the constant $a$ is fixed with the program), with unit-cost arithmetic, a `coin` instruction that reads the next word of a tape of independent uniform random words, a `write` instruction that appends a word to the output, and a `read` instruction that takes the next pending input word and **blocks** when none is pending. A **completed state** is one blocked at a `read` with nothing pending.
--
--   **Runs.** A run starts with the initialization words pending: $n$, $W$, the kind ($0$ insertions, $1$ deletions), one parameter word, the number of initial edges, and each initial edge as $u,v,w(uv)$ (in any order and orientation). After the completed state of initialization, each update is delivered as its words ($0,u,v,c$ inserts $\{u,v\}$ with weight $c$; $1,u,v$ deletes $\{u,v\}$) to the completed state reached after the previous one; the program never sees an update before it has finished the previous one. Time $t$ is the completed state after initialization ($t=0$) or after update $t$. The **total time** is the number of steps of initialization and of all updates, $\infty$ if some step never completes. The **recourse** is the number of words written over the whole run. The coin tape follows the product of uniform laws.
--
--   **Maintained objects.** The object at time $t$ is obtained by replaying every record written up to the completed state at time $t$, malformed records skipped:
--   - a **tree**: nodes are natural numbers, node $v<n$ is the vertex $v$ and is present from the start; `0,x` creates node $x$, `1,x` deletes node $x\ge n$ and its edges, `2,x,y,c` adds edge $\{x,y\}$ or changes its weight to $c$, `3,x,y` deletes edge $\{x,y\}$;
--   - a **partition**: the pair `v,q` puts vertex $v$ into the cluster labelled $q$ (all vertices start with label $0$);
--   - **distance estimates**: the pair `v,q` sets the estimate of $v$ to $\infty$ if $q=0$ and to $q-1$ otherwise (all start at $\infty$).
--
--   An **SSSP instance** with source $s$ has integer edge lengths at most $W$, positive except on edges incident to $s$, and updates of one kind; it need not be connected.
--
--   **Formalization Note.** The machine adds no hypothesis: `Program`, `Config`, `time`, `complete`, `feed` and `coinMeasure` are reused from `DynBrooks_Machine`; the update and output layers here replace `DynBrooks_Protocol`, whose updates are unweighted. Counting words rather than records changes recourse by a factor at most $4$. The parameter word is $0$ for the tree, the source $s$ for SSSP, and $\min(D,nW)$ for the LDD.
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), Theorems 1.1, 1.2 (p. 4); Theorem 3.1 (p. 13); oblivious adversary and recourse (p. 3)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_PDynTreeEmbed_Main_Graphs

namespace PDynTreeEmbed.Main

/-! # Partially dynamic algorithms on the word RAM: input words, runs, total time, and the
maintained object as a replay of change records

Dorkofikis, Probst Gutenberg, *Tight Low-Diameter Decompositions and Tree Embeddings in Partially
Dynamic Graphs*, STOC 2027 submission (manuscript sha256 bf7ba5b2…): Theorems 1.1, 1.2 (p. 4),
Theorem 3.1 (p. 13), the oblivious adversary (p. 3), recourse (p. 3).

**Formalization Note.**
* The machine is the published word RAM `DynBrooks.Program` with words of `a·⌈log₂(n+2)⌉` bits
  (the constant `a` is fixed with the program), unit-cost uniform random words (`coin`), and a `read`
  that blocks until input is pending, so an online program cannot look ahead.
* A run starts with the initialization words pending: `n`, `W`, the kind (`0` insertions, `1`
  deletions), an extra parameter word where a theorem needs one (the source `s` of Theorem 3.1, the
  diameter parameter of Theorem 1.1), the number of initial edges, then each initial edge as the three
  words `u, v, w(uv)`. After the completed state of initialization, each update is delivered as words
  (`0, u, v, c` inserts `{u, v}` with weight `c`; `1, u, v` deletes `{u, v}`) to the completed state
  after the previous update. Time `t` is the completed state after initialization (`t = 0`) or after
  update `t`.
* The total time is the number of steps of initialization and of every update, `∞` if some run never
  completes. The recourse is the number of words the program writes over the whole run.
* The maintained object at time `t` is the replay of every change record written up to the completed
  state at time `t`. Malformed records are skipped. -/

open DynBrooks

/-- The word size `a·⌈log₂(n+2)⌉` used for an `n`-vertex graph. -/
def wordSize (a n : ℕ) : ℕ := a * Nat.clog 2 (n + 2)

/-- The word coding the kind: `0` for insertions, `1` for deletions. -/
def Kind.code : Kind → ℕ
  | Kind.incr => 0
  | Kind.decr => 1

/-- The words of an update: `0, u, v, c` inserts `{u, v}` with weight `c`; `1, u, v` deletes. -/
def Upd.words {n : ℕ} : Upd n → List ℕ
  | .ins u v c => [0, u.val, v.val, c]
  | .del u v => [1, u.val, v.val]

/-- `es` lists each edge of `G` exactly once, in any order and orientation. -/
def IsEdgeListing {n : ℕ} (G : WGraph (Fin n)) (es : List (Fin n × Fin n)) : Prop :=
  (es.map fun e => s(e.1, e.2)).Nodup ∧
    ∀ e : Sym2 (Fin n), e ∈ G.adj.edgeSet ↔ e ∈ es.map fun e => s(e.1, e.2)

/-- The initialization words: `n`, `W`, the kind, the parameter word `extra`, the number of edges,
and every edge as `u, v, w(uv)`. -/
def initWords {n : ℕ} (W : ℕ) (κ : Kind) (extra : ℕ) (G : WGraph (Fin n))
    (es : List (Fin n × Fin n)) : List ℕ :=
  [n, W, κ.code, extra, es.length] ++ es.flatMap fun e => [e.1.val, e.2.val, G.wt s(e.1, e.2)]

/-- The starting configuration: program counter `0`, memory zero, coin cursor `0`, nothing written,
the initialization words pending. -/
def initConfig (w : ℕ) (inp : List ℕ) : Config w :=
  ⟨0, fun _ => 0, inp, 0, [], ∅⟩

/-- The state after a list of operations (each given by its words) from an optional completed
state, if every one of them completes. -/
noncomputable def stateFrom {w : ℕ} (P : Program) (ω : ℕ → BitVec w) :
    Option (Config w) → List (List ℕ) → Option (Config w)
  | none, _ => none
  | some c, [] => some c
  | some c, op :: ops => stateFrom P ω (complete P ω (feed c op)) ops

/-- The steps spent on a list of operations from an optional completed state: the sum of their
times, and `∞` once one of them does not complete. -/
noncomputable def workFrom {w : ℕ} (P : Program) (ω : ℕ → BitVec w) :
    Option (Config w) → List (List ℕ) → ℕ∞
  | none, _ => ⊤
  | some _, [] => 0
  | some c, op :: ops => time P ω (feed c op) + workFrom P ω (complete P ω (feed c op)) ops

/-- The completed state at time `t` (after initialization on `inp` and the first `t` updates of
`σ`) on tape `ω`, if it is reached. -/
noncomputable def stateAt (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ) {n : ℕ}
    (σ : List (Upd n)) (t : ℕ) : Option (Config w) :=
  stateFrom P ω (complete P ω (initConfig w inp)) ((σ.take t).map Upd.words)

/-- The total time: every step of initialization and of every update of `σ` (`∞` if some run does
not complete). -/
noncomputable def totalTime (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ) {n : ℕ}
    (σ : List (Upd n)) : ℕ∞ :=
  time P ω (initConfig w inp) + workFrom P ω (complete P ω (initConfig w inp)) (σ.map Upd.words)

/-- Every word written up to the completed state at time `t` (empty if it is not reached). -/
noncomputable def outputAt (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ) {n : ℕ}
    (σ : List (Upd n)) (t : ℕ) : List ℕ :=
  match stateAt P ω inp σ t with
  | some s => s.output
  | none => []

/-- The total recourse: the number of words written over the whole run. -/
noncomputable def recourse (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ) {n : ℕ}
    (σ : List (Upd n)) : ℕ :=
  (outputAt P ω inp σ σ.length).length

/-- A weighted tree under construction: its nodes (natural numbers; node `v < n` is the vertex
`v`), its edges and their weights. -/
structure TreeState where
  /-- The current nodes. -/
  nodes : Finset ℕ
  /-- The current edges. -/
  edges : Finset (Sym2 ℕ)
  /-- The edge weights. -/
  wt : Sym2 ℕ → ℕ

/-- The empty structure: the vertex nodes `0, …, n−1` and no edge. -/
def TreeState.init (n : ℕ) : TreeState := ⟨Finset.range n, ∅, fun _ => 0⟩

/-- Replay tree change records: `0, x` creates node `x`; `1, x` deletes node `x ≥ n` and its
edges; `2, x, y, c` adds the edge `{x, y}` (`x ≠ y`) or changes its weight, to `c`; `3, x, y`
deletes the edge `{x, y}`. Any other word is skipped. -/
def applyTreeLog (n : ℕ) : TreeState → List ℕ → TreeState
  | T, 0 :: x :: rest => applyTreeLog n { T with nodes := insert x T.nodes } rest
  | T, 1 :: x :: rest =>
      applyTreeLog n
        (if n ≤ x then { T with nodes := T.nodes.erase x, edges := T.edges.filter fun e => x ∉ e }
          else T) rest
  | T, 2 :: x :: y :: c :: rest =>
      applyTreeLog n
        (if x ≠ y then { T with edges := insert s(x, y) T.edges, wt := Function.update T.wt s(x, y) c }
          else T) rest
  | T, 3 :: x :: y :: rest => applyTreeLog n { T with edges := T.edges.erase s(x, y) } rest
  | T, _ :: rest => applyTreeLog n T rest
  | T, [] => T

/-- A tree state as a weighted graph on the nodes `ℕ`. -/
def TreeState.toWGraph (T : TreeState) : WGraph ℕ :=
  ⟨SimpleGraph.fromEdgeSet (T.edges : Set (Sym2 ℕ)), T.wt⟩

/-- The maintained tree `T^(t)`: every tree change record written up to time `t`, replayed. -/
noncomputable def treeAt (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ) {n : ℕ}
    (σ : List (Upd n)) (t : ℕ) : TreeState :=
  applyTreeLog n (TreeState.init n) (outputAt P ω inp σ t)

/-- Replay cluster records: the pair `v, q` puts vertex `v` into the cluster labelled `q`. A pair
whose first word is not a vertex is skipped, as is a single trailing word. -/
def applyLabelLog {n : ℕ} : (Fin n → ℕ) → List ℕ → (Fin n → ℕ)
  | lab, v :: q :: rest =>
      applyLabelLog (if h : v < n then Function.update lab ⟨v, h⟩ q else lab) rest
  | lab, _ => lab

/-- The maintained partition at time `t`, as cluster labels (all vertices start with label `0`). -/
noncomputable def labelsAt (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ) {n : ℕ}
    (σ : List (Upd n)) (t : ℕ) : Fin n → ℕ :=
  applyLabelLog (fun _ => 0) (outputAt P ω inp σ t)

/-- Replay distance-estimate records: the pair `v, q` sets the estimate of vertex `v` to `∞` if
`q = 0` and to `q − 1` otherwise. Malformed records are skipped. -/
def applyEstLog {n : ℕ} : (Fin n → ℕ∞) → List ℕ → (Fin n → ℕ∞)
  | d, v :: q :: rest =>
      applyEstLog
        (if h : v < n then Function.update d ⟨v, h⟩ (if q = 0 then ⊤ else ((q - 1 : ℕ) : ℕ∞))
          else d) rest
  | d, _ => d

/-- The maintained estimates `d̃_t` at time `t` (all `∞` before any record). -/
noncomputable def estAt (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ) {n : ℕ}
    (σ : List (Upd n)) (t : ℕ) : Fin n → ℕ∞ :=
  applyEstLog (fun _ => ⊤) (outputAt P ω inp σ t)

/-- An instance of Theorem 3.1 with source `s`: integer edge lengths at most `W`, positive except
on edges incident to `s`; the updates are all insertions or all deletions (no connectivity is
required). -/
def IsSSSPInstance {n : ℕ} (W : ℕ) (s : Fin n) (G₀ : WGraph (Fin n)) (κ : Kind)
    (σ : List (Upd n)) : Prop :=
  (∀ u v, G₀.adj.Adj u v → G₀.wt s(u, v) ≤ W ∧ (1 ≤ G₀.wt s(u, v) ∨ u = s ∨ v = s)) ∧
    IsLegalSeq (fun u v c => c ≤ W ∧ (1 ≤ c ∨ u = s ∨ v = s)) κ G₀ σ

end PDynTreeEmbed.Main


