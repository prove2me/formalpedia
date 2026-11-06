-- Prove2me | Definitions.Def_NearLinIsing_PortGraph
-- name    : NearLinIsing_PortGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:53.709813+00:00
-- url     : https://prove2.me/theorems/cb40e19a-bf5d-4e93-9f52-d52a3c96c3a5
-- title:
--   The port graph, nonbacktracking matrix $B_t$, $K$, $z$, $P_H$ and the cycle polymer model
-- statement:
--   The **port graph** $H$ is recorded as the arrays its construction writes: the two ports and the weight $t_e$ of each edge, whether the edge is original (and then its index in $G$) or a path edge, and for each port its vertex, its position $1,\dots,d$ on that vertex's path, and $d$. Directed edges are $2e$ and $2e+1$. For directed edges $a,b$ with physical edge $e(b)$,
--
--   $$(B_t)_{ab}=t_{e(b)}\,\mathbf 1\{\mathrm{head}(a)=\mathrm{tail}(b),\ b\ne\bar a\}.$$
--
--   $K$ keeps the transitions of $B_t$ inside strongly connected components. The vector $z$ is $1$ on original directed edges and, on a directed path edge, $r$ times the number of ports ahead in its direction (the head port and those beyond it), and
--
--   $$P_H(a,b)=K_{ab}\,\frac{z_b}{z_a}.\tag{13}$$
--
--   A **cycle** is a nonempty connected edge set in which every port has degree $0$ or $2$, taken unoriented. The **cycle polymer model** has these cycles as types, activities $w_C=\prod_{e\in C}t_e$, and $C\not\sim C'$ exactly when $V(C)\cap V(C')\ne\emptyset$. The restriction of an edge set to its original edges projects even subgraphs of $H$ to those of $G$.
--
--   **Formalization Note** The mathematical objects $B_t$, $K$, $z$, $P_H$ and the cycle model are defined from the geometric arrays only. The arrays `succ`, `scc`, `z`, `rowP` are what the programs read.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, §4.1, pp. 18–19; §4.2, Eq. (13), p. 19

import Mathlib
import Definitions.Def_NearLinIsing_IncGraph
import Definitions.Def_NearLinIsing_Polymer

namespace NearLinIsing

noncomputable section

open Classical

/-- The **port graph** `H` of the degree reduction (§4.1, p. 18), as the arrays the construction
`buildPort` writes. Ports are `0, …, np − 1`; edges of `H` are `0, …, ne − 1`.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, §4.1, p. 18, Proposition 4.1, and §4.2, Eq. (13), p. 19.

* `eU e`, `eV e`: the two ports of edge `e`; `wt e`: its weight `t_e`; `isOrig e`: whether `e` is an
  original edge of `G` (then `gEdge e` is its index in `G`) or a path edge;
* `portVert p`, `portPos p`, `portDeg p`: the core vertex of port `p`, its position `1, …, d` on the
  path of that vertex, and the core degree `d`;
* directed edges are `a = 2e` (from `eU e` to `eV e`) and `a = 2e + 1` (the reversal);
  `succ a`: the nonbacktracking successors of `a`; `scc a`: its strongly connected component in
  the support of `B_t`; `z a`: the vector `z`; `rowP a`: the row of `P_H` in (13), as pairs
  `(b, P_H(a,b))` over the successors `b` in the same component.

**Formalization Note.** The mathematical objects of Proposition 4.1 and Lemma 4.3 (`Bt`, `Kmat`,
`zMath`, `PHmath`, cycles, the cycle model) are defined below from the geometric arrays
(`eU`, `eV`, `wt`, `isOrig`, `gEdge`, `portPos`, `portDeg`) only; the arrays `succ`, `scc`, `z`,
`rowP` are what the programs read. -/
structure PortGraph where
  np : ℕ
  ne : ℕ
  eU : Array ℕ
  eV : Array ℕ
  wt : Array ℝ
  isOrig : Array Bool
  gEdge : Array ℕ
  portVert : Array ℕ
  portPos : Array ℕ
  portDeg : Array ℕ
  succ : Array (List ℕ)
  scc : Array ℕ
  z : Array ℝ
  rowP : Array (List (ℕ × ℝ))

namespace PortGraph

variable (H : PortGraph)

/-- First port of edge `e`. -/
def u (e : Fin H.ne) : ℕ := H.eU.getD e.val 0

/-- Second port of edge `e`. -/
def v (e : Fin H.ne) : ℕ := H.eV.getD e.val 0

/-- The weight `t_e` of edge `e`. -/
def t (e : Fin H.ne) : ℝ := H.wt.getD e.val 0

/-- The degree of port `p` in `H` (edges counted with multiplicity). -/
def deg (p : ℕ) : ℕ :=
  (Finset.univ.filter fun e => H.u e = p).card + (Finset.univ.filter fun e => H.v e = p).card

/-- The degree of port `p` in the edge set `C`. -/
def degIn (C : Finset (Fin H.ne)) (p : ℕ) : ℕ :=
  (C.filter fun e => H.u e = p).card + (C.filter fun e => H.v e = p).card

/-- `F` is an even subgraph of `H`. -/
def IsEven (F : Finset (Fin H.ne)) : Prop := ∀ p, Even (H.degIn F p)

/-- The ports touched by `C`. -/
def verts (C : Finset (Fin H.ne)) : Finset ℕ := C.image H.u ∪ C.image H.v

/-- Two edges share a port. -/
def Touch (e e' : Fin H.ne) : Prop :=
  H.u e = H.u e' ∨ H.u e = H.v e' ∨ H.v e = H.u e' ∨ H.v e = H.v e'

/-- `C` is (the edge set of) a **cycle** of `H`: nonempty, every port has degree `0` or `2` in `C`,
and `C` is connected. Cycles are unoriented edge sets; two parallel edges may form one (p. 19). -/
def IsCycle (C : Finset (Fin H.ne)) : Prop :=
  C.Nonempty ∧ (∀ p, H.degIn C p = 0 ∨ H.degIn C p = 2) ∧
    ∀ e ∈ C, ∀ e' ∈ C, Relation.ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ H.Touch a b) e e'

/-- The type of cycles of `H`. -/
abbrev Cyc : Type := {C : Finset (Fin H.ne) // H.IsCycle C}

/-- The **cycle polymer model** of §4.1, p. 19: polymers are the cycles `C` of `H`, with
`w_C = ∏_{e ∈ C} t_e`, and `C ≁ C'` iff `V(C) ∩ V(C') ≠ ∅`. -/
def cycleModel : PolymerModel H.Cyc where
  w C := ∏ e ∈ C.1, H.t e
  compat C C' := Disjoint (H.verts C.1) (H.verts C'.1)
  symm _ _ h := h.symm
  irrefl C h := by
    obtain ⟨e, he⟩ := C.2.1
    have hm : H.u e ∈ H.verts C.1 :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
    exact Finset.disjoint_left.mp h hm hm

/-- The **restriction to original edges**: the edges of `G` carried by the original edges of `H`
in `F` (the projection of Proposition 4.1 and of the proof of Theorem 1.1). -/
def restrict (G : IncGraph) (F : Finset (Fin H.ne)) : Finset (Fin G.m) :=
  Finset.univ.filter fun g => ∃ e ∈ F, H.isOrig.getD e.val false = true ∧ H.gEdge.getD e.val 0 = g.val

/-- Tail port of the directed edge `a` (`a = 2e`: `eU e → eV e`; `a = 2e+1`: the reversal). -/
def dTail (a : ℕ) : ℕ := if a % 2 = 0 then H.eU.getD (a / 2) 0 else H.eV.getD (a / 2) 0

/-- Head port of the directed edge `a`. -/
def dHead (a : ℕ) : ℕ := if a % 2 = 0 then H.eV.getD (a / 2) 0 else H.eU.getD (a / 2) 0

/-- The **nonbacktracking matrix** `(B_t)_{ab} = t_{e(b)} 1{head(a) = tail(b), b ≠ ā}` on the
`2 ne` directed edges (§4.1, p. 18); `ā = a xor 1` is the reversal of `a`. -/
def Bt : Matrix (Fin (2 * H.ne)) (Fin (2 * H.ne)) ℝ := fun a b =>
  if H.dHead a.val = H.dTail b.val ∧ b.val ≠ a.val ^^^ 1 then H.wt.getD (b.val / 2) 0 else 0

/-- `b` is reachable from `a` in the support digraph of `B_t`. -/
def Reach (a b : Fin (2 * H.ne)) : Prop := Relation.ReflTransGen (fun x y => H.Bt x y ≠ 0) a b

/-- `K`: `B_t` restricted to transitions within strongly connected components (Proposition 4.1;
a transition `a → b` stays in a component iff `a` is reachable from `b`). -/
def Kmat : Matrix (Fin (2 * H.ne)) (Fin (2 * H.ne)) ℝ := fun a b =>
  if H.Reach b a then H.Bt a b else 0

/-- The explicit vector `z` of §4.1, p. 18: `z_a = 1` on original directed edges; on a directed path
edge, `z_a = r` times the number of ports ahead in its direction (the head port and the ports
beyond it on the same path). -/
def zMath (r : ℝ) (a : Fin (2 * H.ne)) : ℝ :=
  if H.isOrig.getD (a.val / 2) false then 1
  else if H.portPos.getD (H.dTail a.val) 0 < H.portPos.getD (H.dHead a.val) 0 then
    r * ((H.portDeg.getD (H.dHead a.val) 0 : ℝ) - H.portPos.getD (H.dHead a.val) 0 + 1)
  else r * (H.portPos.getD (H.dHead a.val) 0 : ℝ)

/-- The transition probabilities (13), p. 19: `P_H(a,b) = K_{ab} z_b / z_a`. -/
def PHmath (r : ℝ) (a b : Fin (2 * H.ne)) : ℝ := H.Kmat a b * H.zMath r b / H.zMath r a

/-- The edge set of `H` named by a list of edge indices (indices `≥ ne` are dropped). -/
def toEdges (L : List ℕ) : Finset (Fin H.ne) :=
  (L.filterMap fun e => if h : e < H.ne then some (⟨e, h⟩ : Fin H.ne) else none).toFinset

end PortGraph

end

end NearLinIsing


