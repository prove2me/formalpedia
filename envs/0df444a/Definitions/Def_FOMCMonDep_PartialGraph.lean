-- Prove2me | Definitions.Def_FOMCMonDep_PartialGraph
-- name    : FOMCMonDep_PartialGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:04.387635+00:00
-- url     : https://prove2.me/theorems/2edecec7-a3fd-4ffb-8662-f946e9c1fdec
-- title:
--   Partial graphs, their structure, distances, merges and resolves
-- statement:
--   A **partial graph** $G$ on the vertex set $\{0,\dots,n-1\}$ consists of two disjoint sets $E(G),N(G)$ of unordered pairs of distinct vertices (**edges** and **non-edges**) and a coloring that gives every vertex exactly one color $Y\in\mathbb N$; the nonempty color classes $Y_G$ are the **parts**. The pairs in $R(G)=E(G)\cup N(G)$ are **resolved**. A partial graph is a relational structure with the binary relations $E,N$ and a unary relation for every color.
--
--   1. **Distances and balls** $\mathrm{dist}_G$, $\mathrm{Ball}^G_r(v)$ are measured in the graph $(V,R(G))$ of resolved pairs, with $\infty$ between different components.
--   2. **Merge.** For colors $P\ne Q$, $\mathrm{merge}_{P,Q}(G)$ recolors every vertex of color $Q$ to $P$.
--   3. **Resolves.** With $P_GQ_G=\{xy: x\in P_G,\ y\in Q_G,\ x\ne y\}$, $\mathrm{resolve}^+_{P,Q}(G)$ adds $P_GQ_G-N(G)$ to $E$ and $\mathrm{resolve}^-_{P,Q}(G)$ adds $P_GQ_G-E(G)$ to $N$; afterwards every pair in $P_GQ_G$ is resolved. $P=Q$ is allowed.
--   4. **Initial partial graph.** Vertex $v$ has color $v$ and nothing is resolved.
--   5. **Codes.** A partial graph is input as $n$, the $n$ colors and the $0/1$ matrices of $E$ and $N$; its distance matrix $D_G$ is input row by row with $\infty$ written as $-1$.
--
--   Construction sequences, the model checking dynamic programming and the definability results of Part II are all about partial graphs.
--
--   **Formalization Note** Colors are named by natural numbers; every vertex has exactly one color, so the nonempty color classes partition the vertex set, as in §2.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §2, p.5 (PDF 7); §3, p.12 (PDF 14); Part III, p.38 (PDF 40)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

open FirstOrder FirstOrder.Language

namespace FOMCMonDep

/-- **Partial graphs.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §2, p.5 (PDF 7): "A partial graph H consists of a finite vertex
set V = V(H), two disjoint sets E(H), N(H) ⊆ (V choose 2) of edges and non-edges, and a partition of V whose parts we
treat as colors." Part III, p.38 (PDF 40): "To track parts over time, we give them names. Fix a countably infinite set
of unary symbols, called colors. We regard a partial graph G as a relational structure with the two symmetric binary
relations E and N and a unary relation Y for every color Y. The vertices of color Y form its color class Y_G, and the
nonempty color classes are the parts of G."

**Formalization Note.** The vertex set is `Fin n`. Colors are named by natural numbers, and `color v` is the one
color of `v` ("As every vertex has exactly one color", p.50), so the nonempty color classes form a partition of the
vertex set. `E` and `N` are simple graphs (symmetric, irreflexive) and are disjoint. -/
structure PartialGraph (n : ℕ) where
  color : Fin n → ℕ
  E : SimpleGraph (Fin n)
  N : SimpleGraph (Fin n)
  disj : Disjoint E N

/-- The relation symbols of partial graphs: the binary `E`, `N`, and one unary symbol for every color `c ∈ ℕ`. -/
inductive PGRel : ℕ → Type
  | E : PGRel 2
  | N : PGRel 2
  | col : ℕ → PGRel 1

/-- **The signature of partial graphs** (Part III, p.38): no function symbols, the binary relations `E`, `N`, and a
unary relation for every color. -/
def PGLang : Language where
  Functions := fun _ => Empty
  Relations := PGRel

namespace PartialGraph

variable {n : ℕ}

/-- A partial graph as a first-order structure over `PGLang`: `E`, `N` as given, and the color symbol `c` holds
of the vertices of color `c`. -/
@[instance_reducible]
def toStructure (G : PartialGraph n) : PGLang.Structure (Fin n) where
  funMap := fun f _ => Empty.elim f
  RelMap := fun {l} R xs =>
    match l, R, xs with
    | _, .E, xs => G.E.Adj (xs 0) (xs 1)
    | _, .N, xs => G.N.Adj (xs 0) (xs 1)
    | _, .col c, xs => G.color (xs 0) = c

/-- The graph `(V, R(H))` of resolved pairs, `R(H) := E(H) ∪ N(H)` (p.5): the Gaifman graph of the structure. -/
def resolved (G : PartialGraph n) : SimpleGraph (Fin n) := G.E ⊔ G.N

/-- `dist_G(u, v)`, "measured in the Gaifman graph (V, R(H)), the graph of resolved pairs" (p.5), in `ℕ∞` (`⊤` when
there is no path). -/
noncomputable def dist (G : PartialGraph n) (u v : Fin n) : ℕ∞ := G.resolved.edist u v

/-- `Ball^G_r(v)`: the vertices at distance at most `r` from `v` in the graph of resolved pairs. -/
def ball (G : PartialGraph n) (r : ℕ) (v : Fin n) : Set (Fin n) := {w | G.dist v w ≤ (r : ℕ∞)}

/-- The pairs `P_G Q_G = {xy : x ∈ P_G, y ∈ Q_G, x ≠ y}` between the color classes of `P` and `Q` (§3, p.10:
"XY := {xy : x ∈ X, y ∈ Y, x ≠ y}"), as a graph. -/
def cross (G : PartialGraph n) (P Q : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y => G.color x = P ∧ G.color y = Q

/-- **Merge.** Part III, p.38 (PDF 40): "merge_{P,Q}(G): P_H := P_G ∪ Q_G, Q_H := ∅ for P ≠ Q" (all other relations
unchanged): every vertex of color `Q` gets color `P`. -/
def merge (G : PartialGraph n) (P Q : ℕ) : PartialGraph n where
  color := fun v => if G.color v = Q then P else G.color v
  E := G.E
  N := G.N
  disj := G.disj

/-- **Resolves.** Part III, p.38 (PDF 40): "resolve⁺_{P,Q}(G): E(H) := E(G) ∪ (P_G Q_G − N(G)), resolve⁻_{P,Q}(G):
N(H) := N(G) ∪ (P_G Q_G − E(G)). After either resolve, every pair in P_G Q_G is resolved." `pos = true` is the positive
resolve. `P = Q` is allowed (§2: "For two parts P, Q of H (possibly P = Q)"). -/
def resolve (G : PartialGraph n) (pos : Bool) (P Q : ℕ) : PartialGraph n :=
  if pos then
    { color := G.color, E := G.E ⊔ (G.cross P Q \ G.N), N := G.N,
      disj := disjoint_sup_left.2 ⟨G.disj, disjoint_sdiff_self_left⟩ }
  else
    { color := G.color, E := G.E, N := G.N ⊔ (G.cross P Q \ G.E),
      disj := disjoint_sup_right.2 ⟨G.disj, disjoint_sdiff_self_right⟩ }

/-- The first partial graph of every construction sequence (§2, p.6: "G₁ has no resolved pairs and only singleton
parts"): vertex `v` has color `v`, and `E = N = ∅`. -/
def initial (n : ℕ) : PartialGraph n where
  color := fun v => (v : ℕ)
  E := ⊥
  N := ⊥
  disj := disjoint_bot_left

open Classical in
/-- **A partial graph as an input** (Part III, p.38: "∥G∥ := |V(G)| + |R(G)| for the size of the representation"):
`n`, the `n` colors, then the `0/1` matrices of `E` and of `N`, row by row (published `rowByRow`). -/
noncomputable def code (G : PartialGraph n) : List ℤ :=
  (n : ℤ) :: (List.ofFn fun v => ((G.color v : ℕ) : ℤ)) ++
    TrulySubcubicAPSP.rowByRow (fun u v => if G.E.Adj u v then 1 else 0) ++
    TrulySubcubicAPSP.rowByRow (fun u v => if G.N.Adj u v then 1 else 0)

/-- **The distance matrix** `D_G` (Part III, p.38: "the |G| × |G| matrix D_G with entries D_G(u, v) := dist_G(u, v) ∈
N ∪ {∞}") as an input, row by row, with `∞` written as `−1`. -/
noncomputable def distCode (G : PartialGraph n) : List ℤ :=
  TrulySubcubicAPSP.rowByRow fun u v => match G.dist u v with
    | ⊤ => -1
    | (d : ℕ) => (d : ℤ)

end PartialGraph

end FOMCMonDep


