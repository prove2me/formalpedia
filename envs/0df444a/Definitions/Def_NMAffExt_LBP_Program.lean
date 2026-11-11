-- Prove2me | Definitions.Def_NMAffExt_LBP_Program
-- name    : NMAffExt_LBP_Program
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:06.459119+00:00
-- url     : https://prove2.me/theorems/cf730fa0-ec51-4134-9306-1a1dd9431ac1
-- title:
--   Linear branching programs over $\mathbb F_2$, $\mathrm{Pre}(v)$, weakly read-once and full programs (Definition 4.1)
-- statement:
--   A **linear branching program** on $\mathbb F_2^N$ is a finite directed acyclic graph with a unique source and sinks labelled by bits. Every internal node $v$ queries a linear form $q_v:\mathbb F_2^N\to\mathbb F_2$ and has two outgoing edges, labelled $0$ and $1$, which may have the same destination. On input $x$ the computation starts at the source and follows the edge labelled $q_v(x)$ until it reaches a sink, whose bit is the output $P(x)$. The **size** of the program is its number of vertices (sinks included). The computation on $x$ **reaches** $v$ if $v$ lies on this computation path; the subprogram started at $v$ is the same procedure begun at $v$.
--
--   For a node $v$, $\mathrm{Pre}(v)$ is the span of all linear forms queried on all directed source-to-$v$ paths, excluding $q_v$ itself; it ranges over every such path, not only the path followed by a particular input. The **query span** of a path to $v$ is the span of the forms queried at its vertices before $v$; its **prefix span** also includes the form queried at its last vertex.
--
--   **Definition 4.1.** The program is **weakly read-once** if $q_v\notin\mathrm{Pre}(v)$ for every internal node $v$. It is **full** if every path to an internal node $v$ has query span $\mathrm{Pre}(v)$.
--
--   A program "on $(X,R)\in\mathbb F_2^n\times\mathbb F_2^t$" is a program on $\mathbb F_2^{n+t}$ evaluated at the concatenation of $x$ and $r$.
--
--   **Formalization Note.** `Program N s` has vertex set `Fin s` (so its size is `s`), labels `node : Fin s → Node N s` (`Node.sink b` or `Node.query q next0 next1`), a designated `root`, a proof that the edge relation has no cycle, and a proof that every vertex is reachable from `root` (in a finite acyclic graph, equivalent to `root` being the unique vertex without incoming edges). A linear form is given by its coefficient vector $\lambda\in\mathbb F_2^N$, the form $x\mapsto\langle\lambda,x\rangle$; this is a bijection with the linear forms. `eval`/`evalFrom v` follow the edges with fuel `s`, which suffices for an acyclic graph on `s` vertices. `Reaches x v`, `IsPathTo l v` (a list of vertices from the root to `v` joined by edges), `pathSpan`, `prefixSpan`, `Pre`, `IsWeaklyReadOnce`, `IsFull`, and `RowsBasis Q W` (the rows of the matrix `Q`, i.e. the coordinate forms of $x\mapsto Qx$, form a basis of $W$).
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 55 (PDF 57), §4.1 and Definition 4.1; p. 57 (PDF 59), Lemma 4.6; p. 101 (PDF 103), §A.1

import Mathlib
import Definitions.Def_NMAffExt_LBP_Basic

/-!
# Linear branching programs over 𝔽₂, Pre(v), weakly read-once and full programs

Xin Li, Yan Zhong, *Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds*,
arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 55 (PDF 57), §4.1 and
Definition 4.1 ([GPT22, Definition 1]); p. 57 (PDF 59), Lemma 4.6 (reaching a node, query span of a
path); p. 101 (PDF 103), §A.1 (programs on (X, R)).

"A linear branching program on 𝔽₂ⁿ is a finite directed acyclic graph with a unique source and
sinks labeled by bits. Every internal node v queries a linear form q_v : 𝔽₂ⁿ → 𝔽₂ and has two
outgoing edges, labeled 0 and 1. Evaluation follows the edge labeled q_v(x). We count all vertices
in its size and allow the two outgoing edges to have the same destination."

Conventions.
* The vertex set is `Fin s`, so the size (number of vertices, sinks included) is `s`.
* A vertex is either a sink carrying a bit, or an internal node carrying its query and its two
  successors `next0` (edge labelled 0) and `next1` (edge labelled 1); they may coincide.
* A linear form on `N` bits is given by its coefficient vector `λ ∈ 𝔽₂ᴺ`, the form `x ↦ ⟨λ, x⟩`;
  every linear form `𝔽₂ᴺ → 𝔽₂` is of this form for exactly one `λ`. Spans of forms are spans of
  coefficient vectors.
* Acyclic: no vertex reaches itself by a nonempty directed path. Unique source: every vertex is
  reachable from the designated `root` (in a finite DAG this is equivalent to `root` being the only
  vertex without incoming edges).
* `runFrom fuel v x` follows the computation from `v`; `evalFrom v x` runs it with fuel `s`, which
  suffices because a directed path of an acyclic graph on `s` vertices has at most `s` vertices (the
  value `0` at fuel `0` is never reached). `eval x = P(x)` starts at the root.
* A path to `v` is a list of vertices starting at the root, ending at `v`, consecutive vertices
  joined by an edge. Its query span is the span of the queries of its vertices before `v`.
* `Pre(v)` is the span of all forms queried on all source-to-`v` paths, excluding `q_v` itself, over
  every path, not only the path followed by one input.
* A program on `(X, R) ∈ 𝔽₂ⁿ × 𝔽₂ᵗ` is a program on `n + t` bits, read at `Fin.append x r`.
-/

namespace NMAffExt.LBP

/-- A vertex of a linear branching program on `N` input bits whose vertices are `Fin s`: a sink
labelled by a bit, or an internal node querying the linear form with coefficient vector `q` and
moving to `next0` on answer `0` and to `next1` on answer `1`. -/
inductive Node (N s : ℕ) where
  | sink (b : ZMod 2) : Node N s
  | query (q : Fin N → ZMod 2) (next0 next1 : Fin s) : Node N s

/-- The directed edges determined by the vertex labels: `u → v` when `u` is internal and `v` is one
of its two successors. -/
def Edge {N s : ℕ} (node : Fin s → Node N s) (u v : Fin s) : Prop :=
  ∃ (q : Fin N → ZMod 2) (v0 v1 : Fin s), node u = Node.query q v0 v1 ∧ (v = v0 ∨ v = v1)

/-- A **linear branching program** on `N` bits with `s` vertices: a finite directed acyclic graph on
`Fin s` with a unique source `root` (every vertex is reachable from it), sinks labelled by bits, and
internal nodes querying linear forms with two outgoing edges labelled `0` and `1`. -/
structure Program (N s : ℕ) where
  node : Fin s → Node N s
  root : Fin s
  acyclic : ∀ v, ¬ Relation.TransGen (Edge node) v v
  rooted : ∀ v, Relation.ReflTransGen (Edge node) root v

namespace Program

variable {N s : ℕ}

/-- The size of a program: its number of vertices. -/
def size (_P : Program N s) : ℕ := s

/-- The coefficient vector of the form queried at `v` (`0` at a sink, which queries nothing). -/
def qvec (P : Program N s) (v : Fin s) : Fin N → ZMod 2 :=
  match P.node v with
  | Node.sink _ => 0
  | Node.query q _ _ => q

/-- Run the program from vertex `v` on input `x` with `fuel` steps. -/
def runFrom (P : Program N s) : ℕ → Fin s → (Fin N → ZMod 2) → ZMod 2
  | 0, _, _ => 0
  | fuel + 1, v, x =>
    match P.node v with
    | Node.sink b => b
    | Node.query q v0 v1 => if ip q x = 0 then P.runFrom fuel v0 x else P.runFrom fuel v1 x

/-- The output of the subprogram started at `v` on input `x`. -/
def evalFrom (P : Program N s) (v : Fin s) (x : Fin N → ZMod 2) : ZMod 2 :=
  P.runFrom s v x

/-- The output `P(x)` of the program on input `x`. -/
def eval (P : Program N s) (x : Fin N → ZMod 2) : ZMod 2 :=
  P.evalFrom P.root x

/-- The computation on input `x` reaches vertex `v`. -/
inductive Reaches (P : Program N s) (x : Fin N → ZMod 2) : Fin s → Prop where
  | root : Reaches P x P.root
  | step {u : Fin s} {q : Fin N → ZMod 2} {v0 v1 : Fin s} :
      Reaches P x u → P.node u = Node.query q v0 v1 → Reaches P x (if ip q x = 0 then v0 else v1)

/-- `l` is a directed path from the source to `v`. -/
def IsPathTo (P : Program N s) (l : List (Fin s)) (v : Fin s) : Prop :=
  l.head? = some P.root ∧ l.getLast? = some v ∧ l.IsChain (Edge P.node)

/-- The query span of a path to `v`: the span of the forms queried at its vertices before `v`. -/
def pathSpan (P : Program N s) (l : List (Fin s)) : Submodule (ZMod 2) (Fin N → ZMod 2) :=
  Submodule.span (ZMod 2) {μ | ∃ w ∈ l.dropLast, P.qvec w = μ}

/-- The prefix span of a path including the form queried at its last vertex. -/
def prefixSpan (P : Program N s) (l : List (Fin s)) : Submodule (ZMod 2) (Fin N → ZMod 2) :=
  Submodule.span (ZMod 2) {μ | ∃ w ∈ l, P.qvec w = μ}

/-- `Pre(v)`: the span of all linear forms queried on all directed source-to-`v` paths, excluding
`q_v` itself. -/
def Pre (P : Program N s) (v : Fin s) : Submodule (ZMod 2) (Fin N → ZMod 2) :=
  Submodule.span (ZMod 2) {μ | ∃ l, P.IsPathTo l v ∧ ∃ w ∈ l.dropLast, P.qvec w = μ}

/-- **Definition 4.1.** `P` is **weakly read-once**: `q_v ∉ Pre(v)` for every internal node `v`. -/
def IsWeaklyReadOnce (P : Program N s) : Prop :=
  ∀ (v : Fin s) (q : Fin N → ZMod 2) (v0 v1 : Fin s), P.node v = Node.query q v0 v1 → q ∉ P.Pre v

/-- `P` is **full**: every path to an internal node `v` has query span `Pre(v)`. -/
def IsFull (P : Program N s) : Prop :=
  ∀ (v : Fin s) (q : Fin N → ZMod 2) (v0 v1 : Fin s), P.node v = Node.query q v0 v1 →
    ∀ l, P.IsPathTo l v → P.pathSpan l = P.Pre v

end Program

/-- The rows of the matrix `Q` (the coordinate forms of the linear map `x ↦ Q x`) form a basis of
the space of forms `W`. -/
def RowsBasis {d N : ℕ} (Q : Matrix (Fin d) (Fin N) (ZMod 2))
    (W : Submodule (ZMod 2) (Fin N → ZMod 2)) : Prop :=
  LinearIndependent (ZMod 2) (fun i => Q i) ∧ Submodule.span (ZMod 2) (Set.range fun i => Q i) = W

end NMAffExt.LBP


