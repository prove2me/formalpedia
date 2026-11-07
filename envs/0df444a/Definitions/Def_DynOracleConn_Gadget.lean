-- Prove2me | Definitions.Def_DynOracleConn_Gadget
-- name    : DynOracleConn_Gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:50:20.148229+00:00
-- url     : https://prove2.me/theorems/62530fdf-a983-46f0-a188-2cba56879f72
-- title:
--   The hard instance $\mathcal G_n(\pi,z)$ and the input stream
-- statement:
--   For an instance $(\pi,z)$, the graph $\mathcal G_n(\pi,z)$ has named vertices $s$, $t$, slot vertices $l^b_j,r^b_j$ and item vertices $u^b_i,v^b_i$ for $b\in\{0,1\}$ and $i,j\in[d]$; any other vertex of $[n]$ is isolated. Its **fixed edges** are $\{s,l^0_1\}$, $\{r^b_j,l^b_{j+1}\}$ and $\{u^b_i,v^b_i\}$. Its **variable edges** are, for item $i$ in slot $j=\pi(i)$,
--
--   $$\{l^b_j,u^{b\oplus z_j}_i\}\quad\text{and}\quad\{v^b_i,r^b_j\}.$$
--
--   The **input stream** inserts these $8d-1$ edges, and then, for each queried item $i$, inserts $\{t,v^0_i\}$ and deletes it again.
--
--   **Formalization Note** The named vertices form a type `GV d` (0-based), and the graph lives on `Fin n` through any injection $e$ of them into `Fin n`. The paper's $d=\lfloor(n-2)/8\rfloor$ is one choice for which an injection exists, and an injection can send $s,t$ to any two given vertices. The insertion order, which the paper leaves open, is the fixed edges and then the variable edges item by item. `epochGraph` names the two graphs that an epoch's probes see.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §3.1, p.20 and §3.1.1, p.20

import Mathlib
import Definitions.Def_DynOracleConn_GraphAfter
import Definitions.Def_DynOracleConn_PPHP

namespace DynOracleConn

/-!
# The hard instance 𝒢ₙ(π, z) and the input stream

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §3.1, p.20 and §3.1.1, p.20:

"Vertices. V = {s, t} ∪ {l⁰ⱼ, l¹ⱼ, r⁰ⱼ, r¹ⱼ | j ∈ [d]} ∪ {u⁰ᵢ, u¹ᵢ, v⁰ᵢ, v¹ᵢ | i ∈ [d]} ∪ D, where D is
a set of isolated vertices such that |V| = n. … Fixed edges. The edge {s, l⁰₁}; the edges
{rᵇⱼ, lᵇⱼ₊₁} for j ∈ [d − 1] and b ∈ {0, 1}, which join consecutive slots; and the edges {uᵇᵢ, vᵇᵢ} for
i ∈ [d] and b ∈ {0, 1}. Variable edges. For every item i, with j = π(i), and every b ∈ {0, 1}, the
edges {lᵇⱼ, u^{b⊕zⱼ}ᵢ} and {vᵇᵢ, rᵇⱼ}."

"In the first 8d−1 updates, edges of 𝒢n(π, z) are inserted. … Then, for the next N epochs do the
following: (1) insert edge eᵢ = {t, v⁰_{Iᵢ}}; (2) query connectivity of s and t; and (3) delete eᵢ."

**Formalization Note.**
1. The named vertices form the type `GV d` (slots and items 0-based, bits as `Bool`); the graph
   lives on `Fin n` through an injection `e : GV d ↪ Fin n`, and the vertices outside the range of
   `e` form `D`. The paper's `d = ⌊(n − 2)/8⌋` is one choice of `d` for which such an `e` exists.
2. The insertion phase inserts the edges in the order of `gadgetEdges`: the fixed edges, then the
   variable edges item by item (the paper does not fix the order).
3. `withT e X i` is the graph during epoch `i` after the insertion of `{t, v⁰ᵢ}`; `epochGraph e X`
   is `gadget e X` (`none`) or `withT e X i` (`some i`), the two graphs an epoch's probes can see.
-/

/-- The named vertices of 𝒢ₙ(π, z): `s`, `t`, the slot vertices `lᵇⱼ, rᵇⱼ` and the item vertices
`uᵇᵢ, vᵇᵢ` (0-based `j, i : Fin d`, `b : Bool`). -/
inductive GV (d : ℕ) : Type where
  | s : GV d
  | t : GV d
  | l (b : Bool) (j : Fin d) : GV d
  | r (b : Bool) (j : Fin d) : GV d
  | u (b : Bool) (i : Fin d) : GV d
  | v (b : Bool) (i : Fin d) : GV d
  deriving DecidableEq

/-- The fixed edges: `{s, l⁰₀}`, `{rᵇⱼ, lᵇⱼ₊₁}` for consecutive slots, and `{uᵇᵢ, vᵇᵢ}`. -/
def fixedEdges (d : ℕ) : List (GV d × GV d) :=
  (if h : 0 < d then [((GV.s : GV d), GV.l false ⟨0, h⟩)] else []) ++
  ((List.finRange d).flatMap fun j : Fin d =>
    if h : j.val + 1 < d then
      [((GV.r false j : GV d), GV.l false ⟨j.val + 1, h⟩),
       ((GV.r true j : GV d), GV.l true ⟨j.val + 1, h⟩)]
    else []) ++
  ((List.finRange d).flatMap fun i : Fin d =>
    [((GV.u false i : GV d), GV.v false i), ((GV.u true i : GV d), GV.v true i)])

/-- The variable edges of instance `X = (π, z)`: for item `i` in slot `j = π i` and `b : Bool`,
`{lᵇⱼ, u^{b ⊕ zⱼ}ᵢ}` and `{vᵇᵢ, rᵇⱼ}`. -/
def variableEdges {d : ℕ} (X : PPHPInst d) : List (GV d × GV d) :=
  (List.finRange d).flatMap fun i : Fin d =>
    [((GV.l false (X.1 i) : GV d), GV.u (xor false (X.2 (X.1 i))) i),
     ((GV.l true (X.1 i) : GV d), GV.u (xor true (X.2 (X.1 i))) i),
     ((GV.v false i : GV d), GV.r false (X.1 i)),
     ((GV.v true i : GV d), GV.r true (X.1 i))]

/-- All edges of 𝒢ₙ(π, z), in insertion order. -/
def gadgetEdges {d : ℕ} (X : PPHPInst d) : List (GV d × GV d) :=
  fixedEdges d ++ variableEdges X

/-- The graph 𝒢ₙ(π, z) on `Fin n`, the named vertices placed by the injection `e`. -/
def gadget {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {x | ∃ p ∈ gadgetEdges X, x = s(e p.1, e p.2)}

/-- 𝒢ₙ(π, z) with the epoch edge `{t, v⁰ᵢ}` added. -/
def withT {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (i : Fin d) : SimpleGraph (Fin n) :=
  gadget e X ⊔ SimpleGraph.fromEdgeSet {s(e GV.t, e (GV.v false i))}

/-- The graph seen by the probes of an epoch update: `gadget e X` before the insertion of
`{t, v⁰ᵢ}` (`none`), `withT e X i` before its deletion (`some i`). -/
def epochGraph {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) : Option (Fin d) → SimpleGraph (Fin n)
  | none => gadget e X
  | some i => withT e X i

/-- The input stream of §3.1.1 for instance `X` and query sequence `ℐ`: insert the edges of
𝒢ₙ(π, z), then for each queried item `i`, insert `{t, v⁰ᵢ}` and delete it again. -/
def hardSeq {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (ℐ : List (Fin d)) : List (PunctSketch.Update n) :=
  (gadgetEdges X).map (fun p => ⟨e p.1, e p.2, true⟩) ++
    ℐ.flatMap (fun i => [⟨e GV.t, e (GV.v false i), true⟩, ⟨e GV.t, e (GV.v false i), false⟩])

end DynOracleConn


