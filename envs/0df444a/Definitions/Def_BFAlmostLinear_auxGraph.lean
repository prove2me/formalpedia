-- Prove2me | Definitions.Def_BFAlmostLinear_auxGraph
-- name    : BFAlmostLinear_auxGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:28.868108+00:00
-- url     : https://prove2.me/theorems/302b9021-c224-4877-9290-84c0fc3683da
-- title:
--   The auxiliary graph $G'$ of Lemma 4.2 ($2h+1$ copies, gadget $r^{\mathrm{tail}}\to r^{\mathrm{head}}$ of weight $-2hM$)
-- statement:
--   Let $G$ be a weighted graph with frozen flags, levels $i:V\to\mathbb N$, a set $U$ of vertices, a hop bound $h$ and a number $M$. The graph $G'$ has
--
--   1. $2h+1$ copies of $G$, written $G_0$, $G^{\mathrm{fwd}}_1,\dots,G^{\mathrm{fwd}}_h$, $G^{\mathrm{bwd}}_1,\dots,G^{\mathrm{bwd}}_h$ (with $G^{\mathrm{fwd}}_0=G^{\mathrm{bwd}}_0=G_0$); every arc is copied with its weight and flag, and flagged arcs become auxiliary;
--   2. for every flagged arc $(u,v)$ and $0\le j<h$, arcs of weight $M+\omega(u,v)$ from $u^{\mathrm{fwd}}_j$ to $v^{\mathrm{fwd}}_{j+1}$ and from $u^{\mathrm{bwd}}_{j+1}$ to $v^{\mathrm{bwd}}_j$;
--   3. for every vertex $v$ of level $0$ and $0\le j<h$, self arcs of weight $M$ from $v^{\mathrm{fwd}}_j$ to $v^{\mathrm{fwd}}_{j+1}$ and from $v^{\mathrm{bwd}}_{j+1}$ to $v^{\mathrm{bwd}}_j$;
--   4. for every $r\in U$, new vertices $r^{\mathrm{tail}}$, $r^{\mathrm{head}}$ of level $0$, zero-weight arcs $r^{\mathrm{fwd}}_h\to r^{\mathrm{tail}}$ and $r^{\mathrm{head}}\to r^{\mathrm{bwd}}_h$, and a real flagged arc $r^{\mathrm{tail}}\to r^{\mathrm{head}}$ of weight $-2hM$.
--
--   All arcs of items 2–4 are real; only the arcs $r^{\mathrm{tail}}\to r^{\mathrm{head}}$ are flagged among them. Copies of a vertex keep its level.
--
--   **Formalization Note** The data structure of Lemma 3.1 that the paper attaches to each copy is not modelled; the copies contain every arc of $G$, including its shortcut arcs.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), proof of Lemma 4.2, pp.13–14, Figure 2

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

/-!
# The auxiliary graph `G′` of Lemma 4.2

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), proof of Lemma 4.2, pp.13–14, Figure 2.

"We start with 2h + 1 copies of G⁺, denoted as G₀, G^forward_1, …, G^forward_h, and G^backward_1, …,
G^backward_h." The copies keep every arc of `G`, with negative arcs turned auxiliary.

**Formalization Note.** `G^forward_k` is `fwdAt h k` and `G^backward_k` is `bwdAt h k`, for `k = 0, …, h`,
with `G^forward_0 = G^backward_0 = G₀`. Thus the printed pairs "`u₀` to `v^forward_1`, `u^forward_i` to
`v^forward_{i+1}`" are the single family `fwdAt h i → fwdAt h (i+1)` for `i < h`, and similarly backward.
The data structure of Lemma 3.1 is not modeled.
-/

/-- The name of a copy of `G`: `G₀`, `G^forward_{i+1}` and `G^backward_{i+1}` for `i : Fin h`. -/
inductive Layer (h : ℕ) : Type
  | base
  | fwd (i : Fin h)
  | bwd (i : Fin h)

/-- `G^forward_k`, for `k ≤ h`; `k = 0` is `G₀`. -/
def fwdAt (h k : ℕ) : Layer h :=
  if k = 0 then .base
  else if hk' : k - 1 < h then .fwd ⟨k - 1, hk'⟩ else .base

/-- `G^backward_k`, for `k ≤ h`; `k = 0` is `G₀`. -/
def bwdAt (h k : ℕ) : Layer h :=
  if k = 0 then .base
  else if hk' : k - 1 < h then .bwd ⟨k - 1, hk'⟩ else .base

variable {V E : Type}

/-- The vertices of `G′`: a copy of each vertex in each layer, and `v_tail`, `v_head` for `v ∈ U`. -/
inductive AuxVertex (V : Type) (U : Finset V) (h : ℕ) : Type
  | copy (l : Layer h) (v : V)
  | tl (r : U)
  | hd (r : U)

/-- The arcs of `G′`, p.14:

* `copy l e`: the copy of the arc `e` in the layer `l`;
* `fwdStep i e`, `bwdStep i e`: for a real or auxiliary negative arc `e = (u, v)`, the arcs of weight
  `M + ω(u, v)` from `u` in `G^forward_i` to `v` in `G^forward_{i+1}`, and from `u` in
  `G^backward_{i+1}` to `v` in `G^backward_i`;
* `fwdSelf i v`, `bwdSelf i v`: for an original vertex `v ∈ S₀`, the self arcs of weight `M` between the same
  layers;
* `gIn r`, `gNeg r`, `gOut r`: for `r ∈ U`, the zero-weight arc from `r^forward_h` to `r_tail`, the real
  negative arc of weight `−2hM` from `r_tail` to `r_head`, and the zero-weight arc from `r_head` to
  `r^backward_h`. -/
inductive AuxArc (G : WGraph V E) (level : V → ℕ) (U : Finset V) (h : ℕ) : Type
  | copy (l : Layer h) (e : E)
  | fwdStep (i : Fin h) (e : {e : E // G.neg e = true})
  | bwdStep (i : Fin h) (e : {e : E // G.neg e = true})
  | fwdSelf (i : Fin h) (v : {v : V // level v = 0})
  | bwdSelf (i : Fin h) (v : {v : V // level v = 0})
  | gIn (r : U)
  | gNeg (r : U)
  | gOut (r : U)

/-- The auxiliary graph `G′` of Lemma 4.2, pp.13–14, for the set `U`, the hop bound `h` and the value `M`
("larger than the absolute value of any (real or auxiliary) negative edge weight"). A flagged arc of `G`
stays flagged in each copy and becomes auxiliary ("All negative edges in these copies are treated as
auxiliary edges"). The arcs `gNeg r` are flagged and real ("These are the only negative edges in G′"). All
other new arcs are real and unflagged. -/
def auxGraph (G : WGraph V E) (level : V → ℕ) (U : Finset V) (h : ℕ) (M : ℝ) :
    WGraph (AuxVertex V U h) (AuxArc G level U h) where
  net :=
    { tail := fun a => match a with
        | .copy l e => .copy l (G.net.tail e)
        | .fwdStep i e => .copy (fwdAt h (i : ℕ)) (G.net.tail e.1)
        | .bwdStep i e => .copy (bwdAt h ((i : ℕ) + 1)) (G.net.tail e.1)
        | .fwdSelf i v => .copy (fwdAt h (i : ℕ)) v.1
        | .bwdSelf i v => .copy (bwdAt h ((i : ℕ) + 1)) v.1
        | .gIn r => .copy (fwdAt h h) r.1
        | .gNeg r => .tl r
        | .gOut r => .hd r
      head := fun a => match a with
        | .copy l e => .copy l (G.net.head e)
        | .fwdStep i e => .copy (fwdAt h ((i : ℕ) + 1)) (G.net.head e.1)
        | .bwdStep i e => .copy (bwdAt h (i : ℕ)) (G.net.head e.1)
        | .fwdSelf i v => .copy (fwdAt h ((i : ℕ) + 1)) v.1
        | .bwdSelf i v => .copy (bwdAt h (i : ℕ)) v.1
        | .gIn r => .tl r
        | .gNeg r => .hd r
        | .gOut r => .copy (bwdAt h h) r.1 }
  w := fun a => match a with
    | .copy _ e => G.w e
    | .fwdStep _ e => M + G.w e.1
    | .bwdStep _ e => M + G.w e.1
    | .fwdSelf _ _ => M
    | .bwdSelf _ _ => M
    | .gIn _ => 0
    | .gNeg _ => -(2 * (h : ℝ) * M)
    | .gOut _ => 0
  neg := fun a => match a with
    | .copy _ e => G.neg e
    | .gNeg _ => true
    | _ => false
  aux := fun a => match a with
    | .copy _ e => G.aux e || G.neg e
    | _ => false

/-- The level of a vertex of `G′` (p.13): "For each vertex v ∈ S_i, all copies of v belong to S′_i", and
`v_tail`, `v_head` "are also considered original vertices". -/
def auxLevel {U : Finset V} {h : ℕ} (level : V → ℕ) : AuxVertex V U h → ℕ
  | .copy _ v => level v
  | .tl _ => 0
  | .hd _ => 0

end BFAlmostLinear


