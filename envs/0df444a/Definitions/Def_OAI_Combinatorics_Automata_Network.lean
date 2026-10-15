-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Network
-- name    : OAI_Combinatorics_Automata_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:55:41.658537+00:00
-- url     : https://prove2.me/theorems/54dc6051-a938-4165-bfc3-04960295193b
-- title:
--   The candidate-slot computation graph of a two-way machine and its symbol-local rotation system
-- statement:
--   Fix a deterministic two-way machine $M$ with state set $Q$, initial state $q_0$ and transition function $\delta$, a distinguished state $\mathrm{fin}\in Q$, and an input word $w$ of length $n$. The input has cells $i=0,\dots,n+1$ carrying the symbols $b_0=\vdash$, $b_i=a_i$ for $1\le i\le n$ and $b_{n+1}=\dashv$, and internal boundaries $j=0,\dots,n$, boundary $j$ lying between cells $j$ and $j+1$. Slots $(d,p,q)$ (with $d=1$ pointing to the right), incidences and local vertices are those of the cell diagrams. This file builds a functional edge graph of the computation in which every vertex and every edge end is located in one cell and is determined by the symbol of that cell.
--
--   1. **Edges.** There are three kinds: a crossing candidate $(j,\sigma)$ for every internal boundary $j$ and slot $\sigma$; a stay candidate $(i,(p,q))$ for every cell $i$ and all $p,q\in Q$; and an outward edge $(s,\sigma)$ for each outer side $s$ (the left side of cell $0$ or the right side of cell $n+1$) and every slot $\sigma$, attached to its own external leaf.
--
--   2. **Edge ends as incidences.** The edge ends correspond bijectively to the local incidences of all cells together with the external leaves. For a crossing candidate $(j,(d,p,q))$, the source end is the incidence $(1,(d,p,q))$ on the right side of cell $j$ and the target end is the incidence $(0,(d,p,q))$ on the left side of cell $j+1$ when $d=1$, and the other way round when $d=0$. The source and target ends of a stay candidate $(i,(p,q))$ are the stay incidences $((p,q),0)$ and $((p,q),1)$ of cell $i$. An outward edge $(s,\sigma)$ has its target end at the incidence $(s,\sigma)$ of the outer cell on side $s$ and its source end at its external leaf.
--
--   3. **Source attachment.** A key is a triple $(m,p,q)$ of a move and two states. In a cell with symbol $b$, the source end of the candidate with key $(m,p,q)$ is attached to the state vertex $p$ if $\delta(p,b)=(q,m)$, and otherwise to a private leaf named by its source incidence: the left-side incidence with slot $(0,p,q)$ for $m=L$, the stay incidence $((p,q),0)$ for $m=S$, and the right-side incidence with slot $(1,p,q)$ for $m=R$. By determinism, different keys never share a source vertex.
--
--   4. **Local vertex map.** A side of a cell with symbol $b$ is outward if $b=\vdash$ and it is the left side, or $b=\dashv$ and it is the right side; the test slot is $\sigma_{\mathrm{test}}=(1,q_0,\mathrm{fin})$. The incidences of a cell with symbol $b$ are attached as follows. (a) A boundary incidence $(s,\sigma)$ on an outward side goes to the state vertex $q_0$ (left side) or $\mathrm{fin}$ (right side) if $\sigma=\sigma_{\mathrm{test}}$, and to its own private vertex otherwise. (b) A boundary incidence $(s,(d,p,q))$ on a side that is not outward goes, when $s=d$ (the cell is the source of the slot), to the source attachment of the key $(R,p,q)$ if $s=1$ or $(L,p,q)$ if $s=0$, and otherwise to the state vertex $q$. (c) A stay incidence $((p,q),1)$ goes to the state vertex $q$, and $((p,q),0)$ to the source attachment of $(S,p,q)$.
--
--   5. **The graph.** The vertices are the pairs (cell $i$, local vertex) together with the external leaves. In the functional edge graph $G_{M,\mathrm{fin}}(w)$, the crossing candidate $(j,(1,p,q))$ runs from the source attachment of $(R,p,q)$ in cell $j$ to the state vertex $q$ of cell $j+1$; the crossing candidate $(j,(0,p,q))$ runs from the source attachment of $(L,p,q)$ in cell $j+1$ to the state vertex $q$ of cell $j$; the stay candidate $(i,(p,q))$ runs from the source attachment of $(S,p,q)$ in cell $i$ to the state vertex $q$ of cell $i$; and the outward edge $(s,\sigma)$ runs from its external leaf to the local vertex of the incidence $(s,\sigma)$ in the outer cell. The source map is injective, and the vertex at every edge end is the local vertex of the corresponding incidence (or the external leaf). A configuration $(i,q)$ of $M$ is represented by the state vertex $q$ of cell $i$.
--
--   6. **Rotation system.** For finite $Q$, a cyclic order $r_b$ of the local vertex map of a cell with symbol $b$ is chosen once for every symbol $b$. Acting by $r_{b_i}$ inside every cell $i$ and fixing the external leaves gives a cyclic order of the vertex map on all incidences, and transported along the bijection of item 2 it is a rotation of $G_{M,\mathrm{fin}}(w)$. The same local cyclic order is used at every occurrence of a symbol.
--
--   Only actual transitions of $M$ leave state vertices, while a candidate that matches no transition starts at a private leaf; in this way the edges and cyclic orders inside a cell depend only on its own symbol, although together they encode the whole computation. The cell diagram of the cyclic order $r_b$ is then the matching diagram of the symbol $b$. For the sink-normalized machine with $\mathrm{fin}$ the sink state, the two outward test edges attach the initial configuration $(0,q_0)$ and the terminal configuration $(n+1,\mathrm{fin})$ to the outer test ports.
--
--   **Formalization Note** The edge type is `Edge Q n := (Fin (n + 1) × Slot Q) ⊕ ((Fin (n + 2) × (Q × Q)) ⊕ (Bool × Slot Q))`, the incidences of the whole input are `WholeInc Q n`, and `incidenceEquiv` (built from `edgeInc` and `incEdge`) is the bijection of item 2; `outCell n s` is the outer cell on side `s`. Keys are `Key Q := Move × Q × Q` with `sourceInc` and `sourceAttach`; `outward`, `testSlot` and `localVertex` give item 4; `edgeKey` and `decorate` locate the sources, and `graph M finish w` has target map `destination M finish w`. `wholeVertex`, `graph_vertex`, `wholePerm`, `orders`, `wholeOrder`, `graphOrder` and `stateVertex` complete items 5 and 6, with `orders` chosen by `CyclicOrder.choose` under `[Fintype Q]`. Sides, slot directions and edge ends use `false` for left, left and source, and `true` for right, right and target.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Network.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Network.lean by skeleton subtraction
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

namespace OAI

namespace OneWayLiveness
namespace CellNetwork
variable (Q : Type)

/-- Edges of all crossing and stay candidates, together with all outward
slots. Every outward slot is an edge to its own external leaf. -/
abbrev Edge (n : ℕ) := (Fin (n + 1) × Slot Q) ⊕
  ((Fin (n + 2) × (Q × Q)) ⊕ (Bool × Slot Q))
abbrev WholeInc (n : ℕ) := (Fin (n + 2) × Incidence Q) ⊕ (Bool × Slot Q)

def outCell (n : ℕ) (s : Bool) : Fin (n + 2) :=
  if s then ⟨n + 1, by omega⟩ else ⟨0, by omega⟩

/-- Locate an oriented incidence in its cell, or at its external leaf. -/
def edgeInc (n : ℕ) : Edge Q n × Bool → WholeInc Q n
  | (.inl (j,slot),b) =>
      if slot.1 ^^ b then .inl (j.castSucc, .inl (true,slot))
      else .inl (j.succ, .inl (false,slot))
  | (.inr (.inl (i,pq)),b) => .inl (i,.inr (pq,b))
  | (.inr (.inr (s,slot)),b) =>
      if b then .inl (outCell n s,.inl (s,slot)) else .inr (s,slot)

def incEdge (n : ℕ) : WholeInc Q n → Edge Q n × Bool
  | .inl (i,.inl (false,slot)) =>
      if h : i.val = 0 then (.inr (.inr (false,slot)),true)
      else (.inl (⟨i.val - 1, by omega⟩,slot),slot.1)
  | .inl (i,.inl (true,slot)) =>
      if h : i.val = n + 1 then (.inr (.inr (true,slot)),true)
      else (.inl (⟨i.val, by omega⟩,slot),!slot.1)
  | .inl (i,.inr (pq,b)) => (.inr (.inl (i,pq)),b)
  | .inr (s,slot) => (.inr (.inr (s,slot)),false)

lemma incEdge_edgeInc (n : ℕ) (d : Edge Q n × Bool) : incEdge Q n (edgeInc Q n d) = d := by
  rcases d with ⟨(⟨j,⟨dir,p,q⟩⟩ | (⟨i,pq⟩ | ⟨s,slot⟩)),b⟩
  · have hj : j.val ≠ n + 1 := Nat.ne_of_lt j.isLt
    cases dir <;> cases b <;> simp [edgeInc, incEdge, hj]
  · rfl
  · cases s <;> cases b <;> simp [edgeInc, incEdge, outCell]

lemma edgeInc_incEdge (n : ℕ) (d : WholeInc Q n) : edgeInc Q n (incEdge Q n d) = d := by
  rcases d with ⟨i,(⟨s,⟨dir,p,q⟩⟩ | ⟨pq,b⟩)⟩ | ⟨s,slot⟩
  · cases s with
    | false =>
      simp only [incEdge]
      split_ifs with hi
      · have he : i = ⟨0,by omega⟩ := Fin.ext hi
        rw [he]
        rfl
      · cases dir <;> simp only [edgeInc, Bool.false_xor, Bool.true_xor, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
        all_goals congr 2; apply Fin.ext; dsimp; omega
    | true =>
      simp only [incEdge]
      split_ifs with hi
      · have he : i = ⟨n+1,by omega⟩ := Fin.ext hi
        rw [he]
        rfl
      · cases dir <;> simp [edgeInc]
  · rfl
  · rfl

def incidenceEquiv (n : ℕ) : (Edge Q n × Bool) ≃ WholeInc Q n where
  toFun := edgeInc Q n
  invFun := incEdge Q n
  left_inv := incEdge_edgeInc Q n
  right_inv := edgeInc_incEdge Q n

/-- A complete proposed successor, including its source and target state. -/
abbrev Key := Move × Q × Q

def sourceInc : Key Q → Incidence Q
  | (.left,p,q) => .inl (false,(false,p,q))
  | (.stay,p,q) => .inr ((p,q),false)
  | (.right,p,q) => .inl (true,(true,p,q))

lemma sourceInc_injective : Function.Injective (sourceInc Q) := by
  rintro ⟨d,p,q⟩ ⟨d',p',q'⟩ h
  cases d <;> cases d' <;> simp_all [sourceInc]

variable {Q} {Alpha : Type} (M : Machine Alpha Q)

noncomputable def sourceAttach (b : Symbol Alpha) (k : Key Q) : LocalVertex Q := by
  classical
  exact if M.transition k.2.1 b = some (k.2.2,k.1) then .inl k.2.1 else .inr (sourceInc Q k)

lemma sourceAttach_injective (b : Symbol Alpha) : Function.Injective (sourceAttach M b) := by
  classical
  rintro ⟨d,p,q⟩ ⟨d',p',q'⟩ h
  dsimp only [sourceAttach] at h
  split_ifs at h with hk hk'
  · have he : p = p' := Sum.inl.inj h
    subst p'
    have he := Option.some.inj (hk.symm.trans hk')
    have hq : q = q' := congrArg Prod.fst he
    cases hq
    have hd : d = d' := congrArg Prod.snd he
    cases hd
    rfl
  · exact sourceInc_injective Q (Sum.inr.inj h)

/-- Only the side facing away from the input is outward. -/
def outward : Symbol Alpha → Bool → Bool
  | .left, s => !s
  | .right, s => s
  | .letter _, _ => false

def testSlot (finish : Q) : Slot Q := (true, M.initial, finish)

noncomputable def localVertex (finish : Q) (b : Symbol Alpha) : Incidence Q → LocalVertex Q := by
  classical
  exact fun i => match i with
    | .inl (s,slot) =>
      if outward b s then
        if slot = testSlot M finish then .inl (if s then finish else M.initial) else .inr i
      else if s = slot.1 then
        sourceAttach M b (if s then .right else .left,slot.2.1,slot.2.2)
      else .inl slot.2.2
    | .inr (pq,r) => if r then .inl pq.2 else sourceAttach M b (.stay,pq.1,pq.2)

variable (Q)
/-- An edge is uniquely determined by the cell, move and states of its
source proposal, or by its outward slot. -/
def edgeKey (n : ℕ) : Edge Q n → (Fin (n + 2) × Key Q) ⊕ (Bool × Slot Q)
  | .inl (j,(true,p,q)) => .inl (j.castSucc,(.right,p,q))
  | .inl (j,(false,p,q)) => .inl (j.succ,(.left,p,q))
  | .inr (.inl (i,(p,q))) => .inl (i,(.stay,p,q))
  | .inr (.inr z) => .inr z

lemma edgeKey_injective (n : ℕ) : Function.Injective (edgeKey Q n) := by
  rintro (⟨i,⟨d,p,q⟩⟩ | (⟨i,⟨p,q⟩⟩ | z)) (⟨j,⟨d',p',q'⟩⟩ | (⟨j,⟨p',q'⟩⟩ | z')) h
  all_goals first
    | (cases d <;> cases d' <;> simp_all [edgeKey])
    | (cases d <;> simp_all [edgeKey])
    | (cases d' <;> simp_all [edgeKey])
    | simp_all [edgeKey]

abbrev Vertex (n : ℕ) := (Fin (n + 2) × LocalVertex Q) ⊕ (Bool × Slot Q)
variable {Q}

noncomputable def decorate (w : List Alpha) :
    (Fin (w.length + 2) × Key Q) ⊕ (Bool × Slot Q) → Vertex Q w.length
  | .inl (i,k) => .inl (i,sourceAttach M (scanned w i) k)
  | .inr z => .inr z

lemma decorate_injective (w : List Alpha) : Function.Injective (decorate M w) := by
  rintro (⟨i,k⟩ | z) (⟨j,k'⟩ | z') h
  · have he := Sum.inl.inj h
    have hij : i = j := congrArg Prod.fst he
    subst j
    have hk := sourceAttach_injective M (scanned w i) (congrArg Prod.snd he)
    cases hk
    rfl
  · cases h
  · cases h
  · exact congrArg Sum.inr (Sum.inr.inj h)

noncomputable def destination (finish : Q) (w : List Alpha) : Edge Q w.length → Vertex Q w.length
  | .inl (j,(true,_p,q)) => .inl (j.succ,.inl q)
  | .inl (j,(false,_p,q)) => .inl (j.castSucc,.inl q)
  | .inr (.inl (i,(_p,q))) => .inl (i,.inl q)
  | .inr (.inr (s,slot)) => .inl (outCell w.length s,
      localVertex M finish (scanned w (outCell w.length s)) (.inl (s,slot)))

noncomputable def graph (finish : Q) (w : List Alpha) : FunctionalEdges (Vertex Q w.length) (Edge Q w.length) where
  src e := decorate M w (edgeKey Q w.length e)
  dst := destination M finish w
  src_injective := (decorate_injective M w).comp (edgeKey_injective Q w.length)

noncomputable def wholeVertex (finish : Q) (w : List Alpha) : WholeInc Q w.length → Vertex Q w.length
  | .inl (i,j) => .inl (i,localVertex M finish (scanned w i) j)
  | .inr z => .inr z

lemma outward_internal (w : List Alpha) (j : Fin (w.length + 1)) :
    outward (scanned w j.castSucc) true = false ∧ outward (scanned w j.succ) false = false := by
  constructor
  · have hr : scanned w j.castSucc ≠ .right := by
      rw [ne_eq, scanned_eq_right_iff]; exact Nat.ne_of_lt j.isLt
    cases h : scanned w j.castSucc <;> simp_all [outward]
  · have hl : scanned w j.succ ≠ .left := by
      rw [ne_eq, scanned_eq_left_iff]; simp
    cases h : scanned w j.succ <;> simp_all [outward]

lemma graph_vertex (finish : Q) (w : List Alpha) (d : Edge Q w.length × Bool) :
    (graph M finish w).vertex d = wholeVertex M finish w (edgeInc Q w.length d) := by
  classical
  rcases d with ⟨(⟨j,⟨dir,p,q⟩⟩ | (⟨i,pq⟩ | ⟨s,slot⟩)),b⟩
  · obtain ⟨hl,hr⟩ := outward_internal w j
    cases dir <;> cases b <;>
      simp [FunctionalEdges.vertex, graph, decorate, edgeKey, destination, wholeVertex, edgeInc,
        localVertex, hl, hr]
  · cases b <;> rfl
  · cases b <;> rfl

/-- The same local cyclic orders are used at every occurrence of a symbol. -/
def wholePerm (w : List Alpha) (r : Symbol Alpha → Equiv.Perm (Incidence Q)) :
    Equiv.Perm (WholeInc Q w.length) where
  toFun x := match x with
    | .inl (i,j) => .inl (i,r (scanned w i) j)
    | .inr z => .inr z
  invFun x := match x with
    | .inl (i,j) => .inl (i,(r (scanned w i)).symm j)
    | .inr z => .inr z
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

lemma wholePerm_pow (w : List Alpha) (r : Symbol Alpha → Equiv.Perm (Incidence Q))
    (n : ℕ) (i : Fin (w.length + 2)) (j : Incidence Q) :
    (wholePerm w r ^ n) (.inl (i,j)) = .inl (i,(r (scanned w i) ^ n) j) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Equiv.Perm.mul_apply, ih]; rfl

noncomputable def orders [Fintype Q] (finish : Q) (b : Symbol Alpha) :
    CyclicOrder (localVertex M finish b) := CyclicOrder.choose _

noncomputable def wholeOrder [Fintype Q] (finish : Q) (w : List Alpha) :
    CyclicOrder (wholeVertex M finish w) where
  perm := wholePerm w (fun b => (orders M finish b).perm)
  vertex_eq x := by
    rcases x with ⟨i,j⟩ | z
    · change Sum.inl (i,localVertex M finish _ ((orders M finish (scanned w i)).perm j)) = _
      rw [(orders M finish (scanned w i)).vertex_eq]
      rfl
    · rfl
  cyclic := by
    rintro (⟨i,j⟩ | z) (⟨i',j'⟩ | z') h
    · have he := Sum.inl.inj h
      have hi : i = i' := congrArg Prod.fst he
      subst i'
      have hj := congrArg Prod.snd he
      obtain ⟨n, hn⟩ := ((orders M finish (scanned w i)).cyclic j j' hj).exists_nat_pow_eq
      refine ⟨n, ?_⟩
      simp only [zpow_natCast, wholePerm_pow, hn]
    · cases h
    · cases h
    · have hz := Sum.inr.inj h
      exact (congrArg Sum.inr hz).sameCycle _

noncomputable def graphOrder [Fintype Q] (finish : Q) (w : List Alpha) :
    (graph M finish w).Rotation where
  perm := (incidenceEquiv Q w.length).symm.permCongrHom (wholeOrder M finish w).perm
  vertex_eq d := by
    rw [graph_vertex, graph_vertex]
    change wholeVertex M finish w (incidenceEquiv Q w.length
      ((incidenceEquiv Q w.length).symm ((wholeOrder M finish w).perm (incidenceEquiv Q w.length d)))) = _
    rw [Equiv.apply_symm_apply]
    exact (wholeOrder M finish w).vertex_eq _
  cyclic d d' h := by
    rw [graph_vertex, graph_vertex] at h
    have hh := (wholeOrder M finish w).cyclic _ _ h
    change (wholeOrder M finish w).perm.SameCycle (incidenceEquiv Q w.length d)
      (incidenceEquiv Q w.length d') at hh
    simpa only [Equiv.symm_apply_apply] using
      sameCycle_permCongr (incidenceEquiv Q w.length).symm (wholeOrder M finish w).perm hh

/-- State configurations embed without identifying any added leaves. -/
def stateVertex (w : List Alpha) (c : Machine.Config (Q := Q) w) : Vertex Q w.length :=
  .inl (c.1,.inl c.2)

end CellNetwork
end OneWayLiveness

end OAI


