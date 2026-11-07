-- Prove2me | Definitions.Def_GyoriLovasz_SplitNetwork
-- name    : GyoriLovasz_SplitNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:16.18309+00:00
-- url     : https://prove2.me/theorems/eae67425-1672-4fd1-90c9-fb204f986f15
-- title:
--   The vertex-splitting network $H$ of Proposition 3.2
-- statement:
--   For a vertex $v\in V\setminus T$ let $K=k+1$. The network $H$ has nodes $x_{\mathrm{in}},x_{\mathrm{out}}$ for every $x\in V$, a source $s_{\mathrm{in}}$ and a sink $s_{\mathrm{out}}$, and arcs
--
--   1. the split arc $(x_{\mathrm{in}},x_{\mathrm{out}})$ of capacity $1$ if $x\neq v$ and $K$ if $x=v$;
--   2. $(s_{\mathrm{in}},v_{\mathrm{in}})$ of capacity $K$;
--   3. $(x_{\mathrm{out}},y_{\mathrm{in}})$ of capacity $K$ for every edge $(x,y)\in E$;
--   4. $(t_{\mathrm{out}},s_{\mathrm{out}})$ of capacity $K$ for every $t\in T$.
--
--   An integral flow obeys the capacities and conservation at every node other than $s_{\mathrm{in}},s_{\mathrm{out}}$; its value is the flow into $s_{\mathrm{out}}$. The residual graph of $f$ has the forward arc $(x,y)$ if $f(x,y)<c_{(x,y)}$ and the reverse arc $(y,x)$ if $f(x,y)>0$. With $\mathfrak R$ the set of nodes from which $s_{\mathrm{out}}$ is reachable in the residual graph,
--   $$L_C=\{x: x_{\mathrm{in}},x_{\mathrm{out}}\in\mathfrak R\},\quad S_C=\{x: x_{\mathrm{in}}\notin\mathfrak R,\ x_{\mathrm{out}}\in\mathfrak R\},\quad R_C=\{x: x_{\mathrm{in}},x_{\mathrm{out}}\notin\mathfrak R\}.$$
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), proof of Proposition 3.2, pp.18–19

import Mathlib
import Definitions.Def_GyoriLovasz_DG

namespace GyoriLovasz

/-- **Nodes of the vertex-splitting network `H`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), proof of Proposition 3.2, p.18: two copies
`x_in`, `x_out` of each vertex, a source `s_in` and a sink `s_out`. -/
inductive HNode (V : Type*) where
  | vin (x : V) : HNode V
  | vout (x : V) : HNode V
  | sin : HNode V
  | sout : HNode V
  deriving DecidableEq

namespace SplitNetwork

variable {V : Type*} [DecidableEq V]

/-- The node set of `H`. -/
def nodes (G : DG V) : Finset (HNode V) :=
  G.verts.image HNode.vin ∪ G.verts.image HNode.vout ∪ {HNode.sin, HNode.sout}

/-- The arc set of `H` (proof of Proposition 3.2, p.18): the split arcs `(x_in, x_out)`, the arc
`(s_in, v_in)`, an arc `(x_out, y_in)` for each edge `(x, y) ∈ E`, and `(t_out, s_out)` for each `t ∈ T`. -/
def arcs (G : DG V) (T : Finset V) (v : V) : Finset (HNode V × HNode V) :=
  G.verts.image (fun x => (HNode.vin x, HNode.vout x)) ∪ {(HNode.sin, HNode.vin v)} ∪
    G.arcs.image (fun a => (HNode.vout a.1, HNode.vin a.2)) ∪
    T.image (fun t => (HNode.vout t, HNode.sout))

/-- The capacities of `H` (p.18), with `K = k + 1`: "Add the split arc (x_in, x_out) with capacity 1 when x ≠ v and
with capacity K when x = v"; every other arc has capacity `K`. -/
def cap (T : Finset V) (v : V) : HNode V × HNode V → ℕ
  | (HNode.vin x, HNode.vout _) => if x = v then T.card + 1 else 1
  | _ => T.card + 1

/-- An integral flow from `s_in` to `s_out` in `H`: capacities on the arcs and conservation at the other nodes.
Values of `f` off the arcs are never read. -/
def IsFlow (G : DG V) (T : Finset V) (v : V) (f : HNode V × HNode V → ℕ) : Prop :=
  (∀ a ∈ arcs G T v, f a ≤ cap T v a) ∧
    ∀ x ∈ nodes G, x ≠ HNode.sin → x ≠ HNode.sout →
      ∑ a ∈ (arcs G T v).filter (fun a => a.2 = x), f a =
        ∑ a ∈ (arcs G T v).filter (fun a => a.1 = x), f a

/-- The value of a flow: the total flow into `s_out`, which has no outgoing arc. -/
def value (G : DG V) (T : Finset V) (v : V) (f : HNode V × HNode V → ℕ) : ℕ :=
  ∑ a ∈ (arcs G T v).filter (fun a => a.2 = HNode.sout), f a

/-- An integral maximum flow of `H`. -/
def IsMaxFlow (G : DG V) (T : Finset V) (v : V) (f : HNode V × HNode V → ℕ) : Prop :=
  IsFlow G T v f ∧ ∀ g, IsFlow G T v g → value G T v g ≤ value G T v f

/-- A residual arc (p.18): "The residual graph of f contains the forward arc (x, y) if f(a) < c_a and the reverse arc
(y, x) if f(a) > 0." -/
def ResArc (G : DG V) (T : Finset V) (v : V) (f : HNode V × HNode V → ℕ) (x y : HNode V) : Prop :=
  ((x, y) ∈ arcs G T v ∧ f (x, y) < cap T v (x, y)) ∨ ((y, x) ∈ arcs G T v ∧ 0 < f (y, x))

/-- The set `ℜ` (p.18): "the set of network vertices from which s_out can be reached in this residual graph." -/
def Reaches (G : DG V) (T : Finset V) (v : V) (f : HNode V × HNode V → ℕ) (x : HNode V) : Prop :=
  Relation.ReflTransGen (ResArc G T v f) x HNode.sout

open Classical in
/-- `L_C = {x ∈ V | x_in, x_out ∈ ℜ}` (p.18). -/
noncomputable def cutL (G : DG V) (T : Finset V) (v : V) (f : HNode V × HNode V → ℕ) : Finset V :=
  G.verts.filter fun x => Reaches G T v f (HNode.vin x) ∧ Reaches G T v f (HNode.vout x)

open Classical in
/-- `S_C = {x ∈ V | x_in ∉ ℜ, x_out ∈ ℜ}` (p.18). -/
noncomputable def cutS (G : DG V) (T : Finset V) (v : V) (f : HNode V × HNode V → ℕ) : Finset V :=
  G.verts.filter fun x => ¬ Reaches G T v f (HNode.vin x) ∧ Reaches G T v f (HNode.vout x)

open Classical in
/-- `R_C = {x ∈ V | x_in, x_out ∉ ℜ}` (p.18). -/
noncomputable def cutR (G : DG V) (T : Finset V) (v : V) (f : HNode V × HNode V → ℕ) : Finset V :=
  G.verts.filter fun x => ¬ Reaches G T v f (HNode.vin x) ∧ ¬ Reaches G T v f (HNode.vout x)

end SplitNetwork

end GyoriLovasz


