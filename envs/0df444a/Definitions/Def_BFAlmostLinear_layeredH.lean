-- Prove2me | Definitions.Def_BFAlmostLinear_layeredH
-- name    : BFAlmostLinear_layeredH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:39.410279+00:00
-- url     : https://prove2.me/theorems/2f8a0ac5-5c3a-4b16-8f69-bffcfb9569aa
-- title:
--   The layered graph $H$ of Lemma 4.8 and its potential
-- statement:
--   Let $G$ be a weighted graph with frozen flags and $h\ge0$. Write $G^+$ for $G$ with its flagged arcs removed. The graph $H$ has
--
--   1. $2h+3$ copies $G^{\mathrm{in}}_0,\dots,G^{\mathrm{in}}_h$, $G^{\mathrm{out}}_0,\dots,G^{\mathrm{out}}_{h+1}$ of $G^+$;
--   2. for every flagged arc $(u,v)$, arcs of weight $\omega(u,v)$ from $u^{\mathrm{out}}_j$ to $v^{\mathrm{out}}_{j+1}$ ($0\le j\le h$) and from $u^{\mathrm{in}}_{j+1}$ to $v^{\mathrm{in}}_j$ ($0\le j<h$);
--   3. zero-weight self arcs $v^{\mathrm{out}}_j\to v^{\mathrm{out}}_{j+1}$ and $v^{\mathrm{in}}_{j+1}\to v^{\mathrm{in}}_j$ for every vertex $v$;
--   4. for every negative vertex $r$, vertices $r^{\mathrm{tail}},r^{\mathrm{head}}$ and zero-weight arcs $r^{\mathrm{in}}_0\to r^{\mathrm{tail}}\to r^{\mathrm{head}}\to r^{\mathrm{out}}_0$, of which only the middle one is flagged.
--
--   $H$ is then reweighted by the potential
--   $$\phi(v^{\mathrm{out}}_j)=-\tilde d^{\,h+1-j}(v,V),\quad \phi(v^{\mathrm{in}}_j)=\tilde d^{\,h-j}(V,v),\quad \phi(r^{\mathrm{tail}})=\phi(r^{\mathrm{in}}_0),\quad \phi(r^{\mathrm{head}})=\phi(r^{\mathrm{out}}_0),$$
--   where $\tilde d^{\,k}(v,V)=\min_x\tilde d^{\,k}(v,x)$ and $\tilde d^{\,k}(V,v)=\min_x\tilde d^{\,k}(x,v)$ are computed in $G$.
--
--   **Formalization Note** Unflagged auxiliary arcs of $G$ are ordinary arcs of the copies; $H$ itself has no auxiliary arcs. The distances in $\phi$ are at most $0$ (empty walk) and finite under `Frozen`, so they are taken as reals.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), proof of Lemma 4.8, pp.19–20, Figure 3

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

/-!
# The layered graph `H` of Lemma 4.8

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), proof of Lemma 4.8, pp.19–20, Figure 3.

"First, let G⁺ denote the graph G with all negative edges removed. We start with 2h + 3 copies of G⁺, denoted
as G^in_0, …, G^in_h and G^out_0, …, G^out_{h+1}."

**Formalization Note.** Auxiliary arcs of `G` are ordinary arcs of `H`: `H` has no auxiliary arcs, and the
copies keep all unflagged arcs of `G`, real and auxiliary. The hops of `G` are counted before the reweighting
(p.20).
-/

variable {V E : Type}

/-- The vertices of `H`: `v^out_i` (`i ≤ h + 1`), `v^in_i` (`i ≤ h`), and `v_tail`, `v_head` for a negative
vertex `v`. -/
inductive HVertex (G : WGraph V E) (h : ℕ) : Type
  | out (i : Fin (h + 2)) (v : V)
  | inn (i : Fin (h + 1)) (v : V)
  | tl (r : G.NegVertex)
  | hd (r : G.NegVertex)

/-- The arcs of `H`, pp.19–20:

* `outCopy i e`, `inCopy i e`: the copy of an unflagged arc `e` in `G^out_i`, `G^in_i`;
* `outStep i e`, `inStep i e`: for a flagged arc `e = (u, v)`, the arcs from `u^out_i` to `v^out_{i+1}`
  (`i ≤ h`) and from `u^in_{i+1}` to `v^in_i` (`i < h`), of weight `ω(u, v)`;
* `outSelf i v`, `inSelf i v`: the self arcs from `v^out_i` to `v^out_{i+1}` and from `v^in_{i+1}` to `v^in_i`,
  of weight `0`;
* `gIn r`, `gMid r`, `gOut r`: the zero-weight arcs `(r^in_0, r_tail)`, `(r_tail, r_head)`, `(r_head, r^out_0)`. -/
inductive HArc (G : WGraph V E) (h : ℕ) : Type
  | outCopy (i : Fin (h + 2)) (e : {e : E // G.neg e = false})
  | inCopy (i : Fin (h + 1)) (e : {e : E // G.neg e = false})
  | outStep (i : Fin (h + 1)) (e : {e : E // G.neg e = true})
  | inStep (i : Fin h) (e : {e : E // G.neg e = true})
  | outSelf (i : Fin (h + 1)) (v : V)
  | inSelf (i : Fin h) (v : V)
  | gIn (r : G.NegVertex)
  | gMid (r : G.NegVertex)
  | gOut (r : G.NegVertex)

/-- The graph `H` before the reweighting. Only the arcs `gMid r` are flagged (so that they are the only
candidates for the negative arcs of `H`); there are no auxiliary arcs. -/
def layeredBase (G : WGraph V E) (h : ℕ) : WGraph (HVertex G h) (HArc G h) where
  net :=
    { tail := fun a => match a with
        | .outCopy i e => .out i (G.net.tail e.1)
        | .inCopy i e => .inn i (G.net.tail e.1)
        | .outStep i e => .out i.castSucc (G.net.tail e.1)
        | .inStep i e => .inn i.succ (G.net.tail e.1)
        | .outSelf i v => .out i.castSucc v
        | .inSelf i v => .inn i.succ v
        | .gIn r => .inn 0 r.1
        | .gMid r => .tl r
        | .gOut r => .hd r
      head := fun a => match a with
        | .outCopy i e => .out i (G.net.head e.1)
        | .inCopy i e => .inn i (G.net.head e.1)
        | .outStep i e => .out i.succ (G.net.head e.1)
        | .inStep i e => .inn i.castSucc (G.net.head e.1)
        | .outSelf i v => .out i.succ v
        | .inSelf i v => .inn i.castSucc v
        | .gIn r => .tl r
        | .gMid r => .hd r
        | .gOut r => .out 0 r.1 }
  w := fun a => match a with
    | .outCopy _ e => G.w e.1
    | .inCopy _ e => G.w e.1
    | .outStep _ e => G.w e.1
    | .inStep _ e => G.w e.1
    | _ => 0
  neg := fun a => match a with
    | .gMid _ => true
    | _ => false
  aux := fun _ => false

/-- The potential on `H`, p.20: `ϕ(v^out_i) = −d̃^{h+1−i}(v, V)`, `ϕ(v^in_i) = d̃^{h−i}(V, v)`,
`ϕ(v_tail) = ϕ(v^in_0)` and `ϕ(v_head) = ϕ(v^out_0)`.

**Formalization Note.** Both distances are at most `0` by the empty walk and, under `Frozen`, not `⊥`, so
`EReal.toReal` loses nothing. -/
noncomputable def layeredPot [Fintype V] (G : WGraph V E) (h : ℕ) : HVertex G h → ℝ
  | .out i v => -(G.dHtFrom (h + 1 - i) v).toReal
  | .inn i v => (G.dHtTo (h - i) v).toReal
  | .tl r => (G.dHtTo h r.1).toReal
  | .hd r => -(G.dHtFrom (h + 1) r.1).toReal

/-- The layered graph `H` of Lemma 4.8, reweighted with the potential `layeredPot` (p.20: "We use H to denote
the graph reweighted with potential ϕ"). -/
noncomputable def layeredH [Fintype V] (G : WGraph V E) (h : ℕ) : WGraph (HVertex G h) (HArc G h) :=
  (layeredBase G h).reweight (layeredPot G h)

end BFAlmostLinear


