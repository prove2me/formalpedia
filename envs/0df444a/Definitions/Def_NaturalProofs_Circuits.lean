-- Prove2me | Definitions.Def_NaturalProofs_Circuits
-- name    : NaturalProofs_Circuits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:22:37.1182+00:00
-- url     : https://prove2.me/theorems/c3419b4d-c94f-4330-9c03-9cd0ae71a541
-- title:
--   Circuits
-- statement:
--   Definitions and structural lemmas for Circuits, from zzyzek / NaturalProof-Lean contributors's pinned NaturalProof-Lean development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean

module
public import Definitions.Def_NaturalProofs_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace NaturalProofs
variable {α β γ δ : Type}
def evalFrom (x : α → Bool) (acc : List Bool) (gs : List (Gate α)) : List Bool :=
  gs.foldl (fun vals g => vals ++ [g.eval x vals]) acc
def Wire.rw (off : ℕ) (σ : α → Wire β) : Wire α → Wire β
  | .input a => σ a
  | .const b => .const b
  | .gate i => .gate (i + off)
def Gate.rw (off : ℕ) (σ : α → Wire β) : Gate α → Gate β
  | .not w => .not (w.rw off σ)
  | .and w₁ w₂ => .and (w₁.rw off σ) (w₂.rw off σ)
  | .or w₁ w₂ => .or (w₁.rw off σ) (w₂.rw off σ)
def Wire.Local (n : ℕ) : Wire β → Prop
  | .gate j => j < n
  | _ => True
def Wire.san (n : ℕ) : Wire β → Wire β
  | .gate j => if j < n then .gate j else .const false
  | w => w
structure MCircuit (α γ : Type) where
  gates : List (Gate α)
  out : γ → Wire α
namespace MCircuit
def size (C : MCircuit α γ) : ℕ := C.gates.length
def eval (C : MCircuit α γ) (x : α → Bool) (c : γ) : Bool :=
  (C.out c).eval x (evalGates x C.gates)
def toCircuit (C : MCircuit α γ) (c : γ) : Circuit α := ⟨C.gates, C.out c⟩
def ofCircuit (C : Circuit α) : MCircuit α Unit := ⟨C.gates, fun _ => C.output⟩
def wires (w : γ → Wire α) : MCircuit α γ := ⟨[], w⟩
def gate1 (g : Gate α) : MCircuit α Unit := ⟨[g], fun _ => .gate 0⟩
def mapOut (g : δ → γ) (C : MCircuit α γ) : MCircuit α δ := ⟨C.gates, C.out ∘ g⟩
def mapIn (f : α → β) (C : MCircuit α γ) : MCircuit β γ :=
  ⟨C.gates.map (Gate.rw 0 (fun a => .input (f a))), fun c => (C.out c).rw 0 (fun a => .input (f a))⟩
def extendσ (E : MCircuit β α) : β ⊕ α → Wire β :=
  Sum.elim Wire.input (fun a => (E.out a).san E.gates.length)
def extend (E : MCircuit β α) (C : MCircuit (β ⊕ α) γ) : MCircuit β (α ⊕ γ) where
  gates := E.gates ++ C.gates.map (Gate.rw E.gates.length (extendσ E))
  out := Sum.elim (fun a => (E.out a).san E.gates.length)
    (fun c => (C.out c).rw E.gates.length (extendσ E))
def comp (C : MCircuit α γ) (E : MCircuit β α) : MCircuit β γ :=
  (extend E (C.mapIn Sum.inr)).mapOut Sum.inr
def par [DecidableEq α] (E : α → MCircuit β Unit) : List α → MCircuit β α
  | [] => wires (fun _ => .const false)
  | a :: l =>
    (extend (E a) ((par E l).mapIn Sum.inl)).mapOut
      (fun b => if b = a then Sum.inl () else Sum.inr b)
noncomputable def parAll [Fintype α] [DecidableEq α] (E : α → MCircuit β Unit) : MCircuit β α :=
  par E (Finset.univ : Finset α).toList
end MCircuit
end NaturalProofs


