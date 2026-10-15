-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Diagrams
-- name    : OAI_Combinatorics_Automata_Diagrams
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:59:31.012721+00:00
-- url     : https://prove2.me/theorems/66c8ce34-449c-4b99-bd6c-4b7bd6e8ef43
-- title:
--   Cell diagrams of a two-way automaton, coloring data and the separation condition
-- statement:
--   These definitions assemble the cell diagrams of a deterministic two-way automaton into one diagram for a whole input word. They also introduce the Boolean colorings that are used to test acceptance.
--
--   Throughout, $M$ is a deterministic two-way automaton with finite state set $Q$ and initial state $q_0$, and $f\in Q$ is a distinguished *finish* state. An input $w=w_1\cdots w_n$ is read between endmarkers, so the tape has cells $0,1,\dots,n+1$ carrying the symbols $b_0=\triangleright$, $b_i=w_i$ $(1\le i\le n)$ and $b_{n+1}=\triangleleft$. As in the earlier cell-network definitions, a *slot* is a triple $\sigma=(d,p,q)$ consisting of a direction bit and two states (a candidate move from $p$ to $q$). A *port* is a pair $(\sigma,\ell)$ of a slot and a lane bit $\ell\in\{0,1\}$. Every cell has *incidences*: boundary incidences $(s,\sigma)$ on its left side ($s=0$) or right side ($s=1$), and stay incidences $((p,q),\theta)$ with a role bit $\theta$. Each incidence $j$ has two *tips* $(j,0)$ and $(j,1)$. For a symbol $b$, the local vertex map of the cell groups the incidences into local vertices, and $r_b$ is a fixed rotation of the cell: a permutation of the incidences whose cycles are exactly the fibres of the local vertex map. A *diagram* is a perfect matching of (left ports) $\sqcup$ (right ports). Diagrams form a monoid under gluing (closed loops are discarded), and a pair $(l,r)$ of port colorings is *compatible* with a diagram if matched ports receive equal colors. Below, $\oplus$ denotes exclusive or of bits.
--
--   1. **Body and full diagrams.** The body diagram $D_b$ of a symbol $b$ is the cell diagram built from the rotation $r_b$. In this wiring, lanes join each port to a tip and join the stay tips in pairs, and joins connect each tip $(j,0)$ to $(r_b(j),1)$. Paths through the wiring are then contracted, and closed loops are discarded. The full diagram of $w$ is the ordered product of the body diagrams of the scanned cells:
--   $$
--   D(w)=D_{b_0}\,D_{b_1}\cdots D_{b_{n+1}}=D_{\triangleright}\,D_{w_1}\cdots D_{w_n}\,D_{\triangleleft}.
--   $$
--   2. **Coloring data.** A coloring datum for $(M,f,w)$ consists of port colorings $\beta_k$, one for each interface $k\in\mathbb{N}$, and tip colorings $\tau_i$, one for each cell $i\in\{0,\dots,n+1\}$. Interface $k$ is the left side of cell $k$ and the right side of cell $k-1$. The colorings must satisfy, for every cell $i$, side $s$, slot $\sigma$, lane $\ell$, stay pair $(p,q)$, role $\theta$, bit $t$ and incidence $j$,
--   $$
--   \beta_{i+s}(\sigma,\ell)=\tau_i\big((s,\sigma),\,s\oplus\ell\big),\qquad \tau_i\big(((p,q),\theta),t\big)=\tau_i\big(((p,q),\neg\theta),\neg t\big),\qquad \tau_i(j,0)=\tau_i\big(r_{b_i}(j),1\big).
--   $$
--   3. **Flat and separated colorings.** A port coloring $c$ is *flat* if $c(\sigma,0)=c(\sigma,1)$ for every slot $\sigma$. Let $\sigma^\ast=(\mathrm{right},q_0,f)$ be the test slot. A pair $(l,r)$ of port colorings is *separated* if $l$ and $r$ are flat, $l(\sigma^\ast,0)=0$ and $r(\sigma^\ast,0)=1$.
--   4. **Whole-network tips.** A coloring datum colors the tips of every incidence of the whole network. A cell incidence $j$ of cell $i$ with bit $t$ gets $\tau_i(j,t)$. An outer leaf $(s,\sigma)$ with bit $t$ gets the outermost interface color at the port $(\sigma,\,s\oplus\neg t)$, taken from $\beta_0$ if $s$ is the left side and from $\beta_{n+2}$ if $s$ is the right side.
--   5. **Coloring data from the network.** Let $c$ be a Boolean coloring of the vertices of the cell network graph of $(M,f,w)$ that is constant along every edge. Then the two endpoints of every edge have equal color. In particular, for each slot, the right boundary incidence of cell $i$ and the left boundary incidence of cell $i+1$ have equal color. The boundary coloring of $c$ ignores the lane $\ell$ and is defined as follows. $\beta^c_0(\sigma,\ell)$ is the color of the vertex of the left incidence $(0,\sigma)$ of cell $0$. For $1\le k\le n+2$, $\beta^c_k(\sigma,\ell)$ is the color of the vertex of the right incidence $(1,\sigma)$ of cell $k-1$. For $k>n+2$ it is $0$. Together with the tip colors $\tau_i(j,t)=c(\text{local vertex of } j \text{ in cell } i)$, this is a coloring datum.
--
--   The full diagram is the image of the endmarked word under the monoid homomorphism $b\mapsto D_b$, so it is determined by the letter diagrams alone. Later results show two things. First, $D(w)$ is compatible with $(l,r)$ exactly when some coloring datum has $\beta_0=l$ and $\beta_{n+2}=r$. Second, provided $f$ has no transition on $\triangleleft$, a separated compatible pair exists exactly when $M$ cannot get from $(0,q_0)$ to $(n+1,f)$. When the run fails, item 5 produces such a pair: color each network vertex by whether it reaches the final configuration. This is how acceptance of $M$ becomes a property of a product of matchings.
--
--   **Formalization Note** The objects are `bodyDiagram`, `fullDiagram`, `ColorData` (fields `boundary`, `tip`, `port_eq`, `stay_eq`, `join_eq`), `Flat`, `Separated`, `ColorData.wholeTip`, `boundaryColor` and `vertexColorData`. The lemmas `vertex_color_flip`, `vertex_color_adjacent`, `boundaryColor_left` and `boundaryColor_right` are the facts in item 5 used to build `vertexColorData`. The rotation $r_b$ is `(orders M finish b).perm`, a cyclic order chosen once for each symbol. Bits are `Bool`s, with `false` read as $0$, and boundary colorings are indexed by all of $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Diagrams.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Diagrams.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

namespace OneWayLiveness
namespace Pairing
variable {A : Type} [Fintype A]

end Pairing

namespace CellNetwork
variable {Q Alpha : Type} [Fintype Q] (M : Machine Alpha Q)

structure ColorData (finish : Q) (w : List Alpha) where
  boundary : ℕ → Port Q → Bool
  tip : Fin (w.length + 2) → Tip Q → Bool
  port_eq : ∀ i s slot l, (if s then boundary (i.val+1) else boundary i.val) (slot,l) =
    tip i (.inl (s,slot),tipRole s l)
  stay_eq : ∀ i pq role t, tip i (.inr (pq,role),t) = tip i (.inr (pq,!role),!t)
  join_eq : ∀ i j, tip i (j,false) = tip i ((orders M finish (scanned w i)).perm j,true)

noncomputable def bodyDiagram (finish : Q) (b : Symbol Alpha) : Pairing (Port Q ⊕ Port Q) :=
  diagram Q (orders M finish b).perm

noncomputable def fullDiagram (finish : Q) (w : List Alpha) : Pairing (Port Q ⊕ Port Q) :=
  (List.ofFn fun i : Fin (w.length + 2) => bodyDiagram M finish (scanned w i)).prod

def Flat (c : Port Q → Bool) : Prop := ∀ slot, c (slot,false) = c (slot,true)

def Separated (finish : Q) (l r : Port Q → Bool) : Prop :=
  Flat l ∧ Flat r ∧ l (testSlot M finish,false) = false ∧ r (testSlot M finish,false) = true

namespace ColorData
variable {M} {finish : Q} {w : List Alpha} (C : ColorData M finish w)

/-- Restoring a reflection at every outer leaf extends the tip assignment. -/
def wholeTip : WholeInc Q w.length → Bool → Bool
  | .inl (i,j),t => C.tip i (j,t)
  | .inr (s,slot),t => C.boundary (if s then w.length+2 else 0) (slot,tipRole s (!t))

end ColorData
omit [Fintype Q] in
/-- A vertex coloring which is constant along all edges also respects
all local joins, regardless of cycles in other components. -/
lemma vertex_color_flip (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e))
    (d : Edge Q w.length × Bool) :
    c (wholeVertex M finish w (edgeInc Q w.length d)) =
      c (wholeVertex M finish w (edgeInc Q w.length ((graph M finish w).flip d))) := by
  rw [← graph_vertex, ← graph_vertex]
  rcases d with ⟨e,b⟩
  cases b with
  | false => exact hc e
  | true => exact (hc e).symm

omit [Fintype Q] in
lemma vertex_color_adjacent (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e))
    (i : Fin (w.length+1)) (slot : Slot Q) :
    c (wholeVertex M finish w (.inl (i.castSucc,.inl (true,slot)))) =
      c (wholeVertex M finish w (.inl (i.succ,.inl (false,slot)))) := by
  have h := vertex_color_flip M finish w c hc (.inl (i,slot),false)
  rcases slot with ⟨d,p,q⟩
  cases d with
  | false => exact h.symm
  | true => exact h

noncomputable def boundaryColor (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (k : ℕ) (p : Port Q) : Bool :=
  if hk : k = 0 then c (wholeVertex M finish w (.inl (⟨0,by omega⟩,.inl (false,p.1))))
  else if hk' : k-1 < w.length+2 then
    c (wholeVertex M finish w (.inl (⟨k-1,hk'⟩,.inl (true,p.1)))) else false

omit [Fintype Q] in
lemma boundaryColor_right (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (i : Fin (w.length+2)) (slot : Slot Q) (lane : Bool) :
    boundaryColor M finish w c (i.val+1) (slot,lane) =
      c (wholeVertex M finish w (.inl (i,.inl (true,slot)))) := by
  simp [boundaryColor, i.isLt]

omit [Fintype Q] in
lemma boundaryColor_left (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e))
    (i : Fin (w.length+2)) (slot : Slot Q) (lane : Bool) :
    boundaryColor M finish w c i.val (slot,lane) =
      c (wholeVertex M finish w (.inl (i,.inl (false,slot)))) := by
  by_cases hi : i.val = 0
  · have he : i = ⟨0,by omega⟩ := Fin.ext hi
    rw [he]
    simp [boundaryColor]
  · have hb : i.val-1 < w.length+2 := by omega
    rw [boundaryColor, dite_eq_right hi, dite_eq_left hb]
    let j : Fin (w.length+1) := ⟨i.val-1,by omega⟩
    have hj : j.succ = i := Fin.ext (by dsimp [j]; omega)
    exact (vertex_color_adjacent M finish w c hc j slot).trans (congrArg
      (fun k => c (wholeVertex M finish w (.inl (k,.inl (false,slot))))) hj)

noncomputable def vertexColorData (finish : Q) (w : List Alpha) (c : Vertex Q w.length → Bool)
    (hc : ∀ e, c ((graph M finish w).src e) = c ((graph M finish w).dst e)) : ColorData M finish w where
  boundary := boundaryColor M finish w c
  tip i j := c (wholeVertex M finish w (.inl (i,j.1)))
  port_eq i s slot lane := by
    cases s with
    | false => exact boundaryColor_left M finish w c hc i slot lane
    | true => exact boundaryColor_right M finish w c i slot lane
  stay_eq i pq role t := vertex_color_flip M finish w c hc (.inr (.inl (i,pq)),role)
  join_eq i j := congrArg (fun v => c (.inl (i,v))) ((orders M finish (scanned w i)).vertex_eq j).symm

end CellNetwork
end OneWayLiveness

end OAI


