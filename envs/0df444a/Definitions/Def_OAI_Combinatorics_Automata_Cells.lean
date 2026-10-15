-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Cells
-- name    : OAI_Combinatorics_Automata_Cells
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:52:41.580284+00:00
-- url     : https://prove2.me/theorems/14a33038-5dfb-4f8d-8598-f98a2953f1bb
-- title:
--   Cell diagrams: matchings of a cell's boundary ports built from travel lanes and local joins
-- statement:
--   This file builds, from a permutation of local incidences, the matching diagram that represents a single input cell. Throughout, $Q$ is a set (later the state set of a machine), and Boolean labels take values in $\{0,1\}$.
--
--   1. **Closing internal tips.** Let $P$ and $I$ be finite, let $\lambda$ be a pairing of $P\sqcup I$ and let $\jmath$ be a pairing of $I$. The closure $\mathrm{cl}(\lambda,\jmath)$ is the pairing of $P$ obtained by composing $\lambda$, viewed as a diagram from $P$ to $I$, with $\jmath$, viewed as a diagram from $I$ to the empty set. Thus every point of $I$ is joined to its $\jmath$-partner, the resulting wiring is contracted, its paths pair up the points of $P$, and closed loops are discarded.
--
--   2. **Labels.** A *slot* is a triple $\sigma=(d,p,q)\in\{0,1\}\times Q\times Q$, a candidate transition from state $p$ to state $q$ across a cell boundary, where $d=1$ means that the prospective successor lies to the right. A *port* is a pair $(\sigma,\ell)$ of a slot and a lane label $\ell\in\{0,1\}$; each side of a cell carries one copy of the port set, so for finite $Q$ each side has $4|Q|^2$ ports. A *boundary incidence* is a pair $(s,\sigma)$ of a side $s\in\{0,1\}$ ($0$ left, $1$ right) and a slot. An *incidence* is either a boundary incidence or a stay incidence $((p,q),\rho)$ with $p,q\in Q$ and $\rho\in\{0,1\}$, one of the two ends of a candidate stay edge. A *tip* is a pair $(i,t)$ of an incidence $i$ and $t\in\{0,1\}$, one of the two lane tips at $i$. A *local vertex* is an element of $Q\sqcup\mathrm{Inc}$: a state vertex, or a private vertex named by an incidence. Finally, the *tip role* of the lane label $\ell$ at side $s$ is $s\oplus\ell$ (exclusive or), so the same absolute lane label has opposite roles on the two sides of a cell.
--
--   3. **Lanes.** The pairing $\Lambda$ of the disjoint union of the boundary ports $((s,\sigma),\ell)$ and the tips, given by the fixed-point-free involution
--   $$\bigl((s,\sigma),\ell\bigr)\ \longleftrightarrow\ \bigl((s,\sigma),\,s\oplus\ell\bigr),\qquad \bigl(((p,q),\rho),\,t\bigr)\ \longleftrightarrow\ \bigl(((p,q),1-\rho),\,1-t\bigr).$$
--   Every boundary port is wired to a tip of its own incidence, and the tips at the two ends of each stay edge are wired crosswise.
--
--   4. **Joins.** For a permutation $r$ of the set of incidences, the pairing $J_r$ of the tips with
--   $$(i,0)\ \longleftrightarrow\ (r(i),1)\qquad\text{for every incidence } i .$$
--   Reading $t=0$ as the incoming and $t=1$ as the outgoing tip, a join connects the incoming tip at $i$ to the outgoing tip at the next incidence $r(i)$.
--
--   5. **Cell diagram.** The boundary port $((s,\sigma),\ell)$ is identified with the port $(\sigma,\ell)$ of the left side if $s=0$ and of the right side if $s=1$. For finite $Q$ and a permutation $r$ of the incidences, the cell diagram is
--   $$D_r=\mathrm{cl}(\Lambda,J_r),$$
--   read through this identification as a pairing of the left ports together with the right ports, i.e. a matching diagram with $4|Q|^2$ ports on each side.
--
--   When $r$ cyclically orders the incidences around each local vertex of a cell, $D_r$ records how the two travel lanes of every edge and the joins at every vertex connect the boundary ports of the cell. The diagram depends on nothing but $r$; this is what allows every occurrence of an input symbol to be represented by the same diagram, so that a whole input is represented by the product of the diagrams of its cells.
--
--   **Formalization Note** The label types are `Slot Q := Bool × Q × Q`, `Port Q := Slot Q × Bool`, `Boundary Q := Bool × Slot Q`, `Incidence Q := Boundary Q ⊕ ((Q × Q) × Bool)`, `Tip Q := Incidence Q × Bool` and `LocalVertex Q := Q ⊕ Incidence Q`, with `Q : Type`. The tip role is `tipRole s l = s ^^ l` (simp lemmas `tipRole_twice`, `tipRole_ne`); the lanes and joins are `lanes Q` and `joins Q r`, built with `Pairing.ofInvolution` from the involutions `laneMate` and `joinMate`; the side identification is `portsEquiv`, and `diagram Q r` assumes `[Fintype Q]`. `Pairing.close` composes with the joins as a pairing of `I ⊕ Empty` and transports back along `Equiv.sumEmpty`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Cells.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Cells.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring

namespace OAI

namespace OneWayLiveness
namespace Pairing
variable {P I : Type} [Fintype P] [Fintype I]

/-- Close all internal tips with a matching of local joins. -/
noncomputable def close (lanes : Pairing (P ⊕ I)) (joins : Pairing I) : Pairing P :=
  (compose lanes (joins.transport (Equiv.sumEmpty I Empty).symm)).transport (Equiv.sumEmpty P Empty)

end Pairing

namespace CellNetwork
variable (Q : Type)
/-- `true` directs the prospective successor to the right. -/
abbrev Slot := Bool × Q × Q
abbrev Port := Slot Q × Bool
abbrev Boundary := Bool × Slot Q
abbrev Incidence := Boundary Q ⊕ ((Q × Q) × Bool)
abbrev Tip := Incidence Q × Bool
abbrev LocalVertex := Q ⊕ Incidence Q

/-- A lane's absolute label changes its incoming/outgoing role between
opposite sides of a cell. -/
def tipRole (side lane : Bool) : Bool := side ^^ lane
@[simp] lemma tipRole_twice (s l : Bool) : tipRole s (tipRole s l) = l := by cases s <;> cases l <;> rfl
@[simp] lemma tipRole_ne (s l : Bool) : tipRole (!s) l = !(tipRole s l) := by cases s <;> cases l <;> rfl

/-- All stay candidates are allowed locally; a nontransition candidate will
be attached to a fresh leaf. This leaves the external degree unchanged. -/
def laneMate : ((Boundary Q × Bool) ⊕ Tip Q) → ((Boundary Q × Bool) ⊕ Tip Q)
  | .inl (b,l) => .inr (.inl b, tipRole b.1 l)
  | .inr (.inl b,t) => .inl (b, tipRole b.1 t)
  | .inr (.inr (pq,r),t) => .inr (.inr (pq,!r),!t)

lemma laneMate_involutive : Function.Involutive (laneMate Q) := by
  rintro (⟨⟨s,slot⟩,l⟩ | ⟨(⟨s,slot⟩ | ⟨pq,r⟩),t⟩) <;> simp [laneMate]
lemma laneMate_ne (p) : laneMate Q p ≠ p := by
  rcases p with ⟨⟨s,slot⟩,l⟩ | ⟨(⟨s,slot⟩ | ⟨pq,r⟩),t⟩ <;> simp [laneMate]

def lanes : Pairing ((Boundary Q × Bool) ⊕ Tip Q) :=
  Pairing.ofInvolution (laneMate Q) (laneMate_involutive Q) (laneMate_ne Q)

def joinMate (r : Equiv.Perm (Incidence Q)) : Tip Q → Tip Q
  | (i,false) => (r i, true)
  | (i,true) => (r.symm i, false)

lemma joinMate_involutive (r : Equiv.Perm (Incidence Q)) : Function.Involutive (joinMate Q r) := by
  rintro ⟨i, b⟩; cases b <;> simp [joinMate]
lemma joinMate_ne (r : Equiv.Perm (Incidence Q)) (p) : joinMate Q r p ≠ p := by
  rcases p with ⟨i,b⟩; cases b <;> simp [joinMate]

def joins (r : Equiv.Perm (Incidence Q)) : Pairing (Tip Q) :=
  Pairing.ofInvolution (joinMate Q r) (joinMate_involutive Q r) (joinMate_ne Q r)

/-- The two sides use exactly the same slot/lane labels. -/
def portsEquiv : (Boundary Q × Bool) ≃ (Port Q ⊕ Port Q) where
  toFun p := if p.1.1 then .inr (p.1.2,p.2) else .inl (p.1.2,p.2)
  invFun p := p.elim (fun p => ((false,p.1),p.2)) (fun p => ((true,p.1),p.2))
  left_inv p := by rcases p with ⟨⟨s,slot⟩,l⟩; cases s <;> rfl
  right_inv p := by cases p <;> rfl

noncomputable def diagram [Fintype Q] (r : Equiv.Perm (Incidence Q)) : Pairing (Port Q ⊕ Port Q) :=
  (Pairing.close (lanes Q) (joins Q r)).transport (portsEquiv Q)

end CellNetwork
end OneWayLiveness

end OAI


