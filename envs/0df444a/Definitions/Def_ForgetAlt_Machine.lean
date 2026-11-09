-- Prove2me | Definitions.Def_ForgetAlt_Machine
-- name    : ForgetAlt_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:21:41.418907+00:00
-- url     : https://prove2.me/theorems/87433d2e-b02b-4740-8d7f-8e4cca58d0f2
-- title:
--   The double path and matching problems on the word RAM; running within a bound
-- statement:
--   Algorithms are programs of the published word RAM `EndStatement`: instructions `one, add, sub, mul, load, store, bltz, accept, reject` on $W$-bit words, one step each. A run starts with the instance size in cell 0 and the input words after it; the output is read from the cells after the input.
--
--   * **Matching problem.** Input: $m$, then the $m$ edges of $G$ on vertices $0,\dots,n-1$ as triples $(u,v,\text{flag})$, flag $1$ for a matching edge (no loops, no repeated edge, flagged edges pairwise disjoint). Output: the number of paths, then each path as its length and vertices. Correct if the paths are vertex-disjoint shortest augmenting paths (and maximal, for the maximal version).
--   * **Double path problem.** Input: the arcs, $N$ sink flags, the bridges. Output: the number of double paths, then for each $(P,Q,y,z)$: $y,z,|P|,P,|Q|,Q$. Correct if they are pairwise vertex-disjoint double paths (and maximal).
--
--   A program runs within a bound $g$ if, on every valid instance and at every word width $W\ge b(\lfloor\log_2\text{size}\rfloor+1)$, it halts within $g$ steps with a correct output. $\hat T(n,m)=\max\{T(a,b): a\le n,\ b\le m\}$ is the monotone envelope of $T$.
--
--   **Formalization Note** Isolated vertices are allowed in the matching problem. The size is $n+m+2$, resp. $N+|E(H)|+|E_c|+2$.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Theorem 1.1, printed pp.3–4 (PDF pp.4–5)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Definitions.Def_ForgetAlt_Matching
import Definitions.Def_ForgetAlt_DPInstance

namespace ForgetAlt

/-!
# The two problems of Theorem 1.1 on the published word RAM, and running-time bounds

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Theorem 1.1, printed pp.3–4 (PDF pp.4–5).

**Formalization Notes.**
* The machine is the published word RAM `EndStatement` (`exec`, `loadWords`, `Problem`,
  `Problem.SolvedBy`): programs are `List EndStatement.Instr`, the time of a run is its number of
  steps, a run starts with `n` in cell 0 and the input after it, and the output is read from the
  cells after the input. Words have `W` bits, and a program must work at every width
  `W ≥ b·(⌊log₂ size⌋ + 1)` for a constant `b` of its choice (a word RAM with `O(log size)`-bit
  words).
* **Matching input.** `n` vertices `Fin n` (isolated vertices allowed), then `m` and the `m`
  edges as triples `u, v, flag`, `flag = 1` for a matching edge. `Valid`: no loops, no edge listed
  twice (in either order), matching edges pairwise vertex-disjoint. `G` is the graph of the list
  and `M` its flagged edges (as a subgraph whose vertices are the matched ones).
  **Output**: the number of paths, then for each path its number of vertices and its vertices.
* **Double path input.** `N` vertices, then the number of arcs and the arcs as pairs, then `N`
  flags (`1` for `u ∈ U`), then the number of bridges and the bridges as pairs.
  **Output**: the number of double paths, then for each `(P, Q, y, z)`: `y, z, |P|, P, |Q|, Q`.
* `Tenv T n m = max {T(a, b) | a ≤ n, b ≤ m}`, the monotone envelope of `T`; it equals
  `T(n, m)` for every `T` nondecreasing in both arguments.
* "`O(g)`" is read as `≤ C·(g + 1)` for a constant `C`; the `+ 1` only matters where `g = 0`.
-/

open EndStatement

/-! ## The matching problem -/

/-- A graph on `Fin n` with a matching, as a list of edges with a matching flag. -/
structure AugInstance (n : ℕ) where
  edges : List (Fin n × Fin n × Bool)

/-- Valid input: no loops, no repeated edge, matching edges pairwise vertex-disjoint. -/
def AugInstance.Valid {n : ℕ} (x : AugInstance n) : Prop :=
  (∀ e ∈ x.edges, e.1 ≠ e.2.1) ∧
    x.edges.Pairwise (fun e e' => s(e.1, e.2.1) ≠ s(e'.1, e'.2.1)) ∧
    (x.edges.filter (fun e => e.2.2)).Pairwise
      (fun e e' => e.1 ≠ e'.1 ∧ e.1 ≠ e'.2.1 ∧ e.2.1 ≠ e'.1 ∧ e.2.1 ≠ e'.2.1)

/-- The graph `G` of the instance. -/
def AugInstance.graph {n : ℕ} (x : AugInstance n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b => ∃ e ∈ x.edges, e.1 = a ∧ e.2.1 = b)

/-- The graph of the flagged edges. -/
def AugInstance.matchGraph {n : ℕ} (x : AugInstance n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b => ∃ e ∈ x.edges, e.2.2 = true ∧ e.1 = a ∧ e.2.1 = b)

/-- The matching `M` of the instance, as a subgraph of `G` whose vertices are the matched ones. -/
def AugInstance.matching {n : ℕ} (x : AugInstance n) : x.graph.Subgraph where
  verts := {v | ∃ w, x.matchGraph.Adj v w}
  Adj := x.matchGraph.Adj
  adj_sub := by
    intro a b h
    simp only [AugInstance.matchGraph, AugInstance.graph, SimpleGraph.fromRel_adj] at h ⊢
    obtain ⟨hne, ⟨e, he, -, h1, h2⟩ | ⟨e, he, -, h1, h2⟩⟩ := h
    · exact ⟨hne, Or.inl ⟨e, he, h1, h2⟩⟩
    · exact ⟨hne, Or.inr ⟨e, he, h1, h2⟩⟩
  edge_vert := fun h => ⟨_, h⟩
  symm := x.matchGraph.symm

/-- The input words of the matching instance (cell 0, holding `n`, is added by `SolvedBy`). -/
def augInput {n : ℕ} (x : AugInstance n) : List ℤ :=
  (x.edges.length : ℤ) ::
    x.edges.flatMap (fun e => [((e.1 : ℕ) : ℤ), ((e.2.1 : ℕ) : ℤ), if e.2.2 then 1 else 0])

/-- `out` starts with the words `enc`. -/
def Decodes (out : ℕ → ℤ) (enc : List ℤ) : Prop :=
  ∀ i (h : i < enc.length), out i = enc[i]

/-- The output words for a list of paths. -/
def encPaths {n : ℕ} (A : List (List (Fin n))) : List ℤ :=
  (A.length : ℤ) :: A.flatMap (fun l => (l.length : ℤ) :: l.map (fun v => ((v : ℕ) : ℤ)))

/-- The size of a matching instance, `n + m + 2`, which sets the word width. -/
def augSize {n : ℕ} (x : AugInstance n) : ℕ := n + x.edges.length + 2

/-- The problem of Theorem 1.1's conclusion: output a set of vertex-disjoint shortest augmenting
paths of `(G, M)`, maximal if `maximal = true`. -/
def AugProblem (maximal : Bool) : Problem where
  Instance n := {x : AugInstance n // x.Valid}
  input x := augInput x.1
  output x out := ∃ A, Decodes out (encPaths A) ∧ IsDisjointSAPFamily x.1.matching A ∧
    (maximal = true → IsMaximalSAPFamily x.1.matching A)

/-! ## The double path problem -/

/-- The input words of a double path instance. -/
def dpInput {N : ℕ} (I : DPInstance N) : List ℤ :=
  ((I.arcs.length : ℤ) :: I.arcs.flatMap (fun a => [((a.1 : ℕ) : ℤ), ((a.2 : ℕ) : ℤ)])) ++
    List.ofFn (fun i : Fin N => if i ∈ I.sinkSet then (1 : ℤ) else 0) ++
    ((I.bridges.length : ℤ) :: I.bridges.flatMap (fun a => [((a.1 : ℕ) : ℤ), ((a.2 : ℕ) : ℤ)]))

/-- The output words for a list of double paths `(P, Q, y, z)`. -/
def encDP {N : ℕ} (D : List (List (Fin N) × List (Fin N) × Fin N × Fin N)) : List ℤ :=
  (D.length : ℤ) :: D.flatMap (fun d =>
    [((d.2.2.1 : ℕ) : ℤ), ((d.2.2.2 : ℕ) : ℤ), (d.1.length : ℤ)] ++ d.1.map (fun v => ((v : ℕ) : ℤ)) ++
      (d.2.1.length : ℤ) :: d.2.1.map (fun v => ((v : ℕ) : ℤ)))

/-- The size of a double path instance, `N + |E(H)| + |E_c| + 2`, which sets the word width. -/
def dpSize {N : ℕ} (I : DPInstance N) : ℕ := N + I.arcs.length + I.bridges.length + 2

/-- The double path problem of Theorem 1.1's hypothesis: output a set of vertex-disjoint double
paths, maximal if `maximal = true`. -/
def DPProblem (maximal : Bool) : Problem where
  Instance N := {I : DPInstance N // I.Valid}
  input I := dpInput I.1
  output I out := ∃ D, Decodes out (encDP D) ∧ I.1.IsDisjointFamily D ∧
    (maximal = true → I.1.IsMaximalFamily D)

/-! ## Running within a time bound -/

/-- The program `A` solves the double path problem at every width `W ≥ b·(⌊log₂ size⌋ + 1)`,
halting within `bound N I` steps on every valid instance `I`. -/
def DPRunsWithin (maximal : Bool) (A : List Instr) (b : ℕ)
    (bound : (N : ℕ) → DPInstance N → ℕ) : Prop :=
  ∀ (N : ℕ) (I : DPInstance N) (hI : I.Valid) (W : ℕ), b * (Nat.log2 (dpSize I) + 1) ≤ W →
    ∃ t ≤ bound N I, (DPProblem maximal).SolvedBy (n := N) ⟨I, hI⟩ A W t

/-- The program `B` solves the matching problem at every width `W ≥ b·(⌊log₂ size⌋ + 1)`,
halting within `bound n x` steps on every valid instance `x`. -/
def AugRunsWithin (maximal : Bool) (B : List Instr) (b : ℕ)
    (bound : (n : ℕ) → AugInstance n → ℕ) : Prop :=
  ∀ (n : ℕ) (x : AugInstance n) (hx : x.Valid) (W : ℕ), b * (Nat.log2 (augSize x) + 1) ≤ W →
    ∃ t ≤ bound n x, (AugProblem maximal).SolvedBy (n := n) ⟨x, hx⟩ B W t

/-- The monotone envelope `T̂(n, m) = max {T(a, b) | a ≤ n, b ≤ m}`. -/
def Tenv (T : ℕ → ℕ → ℕ) (n m : ℕ) : ℕ :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (m + 1))).sup (fun p => T p.1 p.2)

/-- A run of `P` on `n` and `input` (laid out as in `Problem.SolvedBy`) halts within `t` steps,
and the words after the input satisfy `out`. -/
def RunOutputs (P : List Instr) (W t n : ℕ) (input : List ℤ) (out : (ℕ → ℤ) → Prop) : Prop :=
  ∃ verdict m, exec P t 0 (loadWords W ((n : ℤ) :: input)) = some (verdict, m) ∧
    out (fun a => (m (1 + input.length + a : ℕ)).toInt)

end ForgetAlt


