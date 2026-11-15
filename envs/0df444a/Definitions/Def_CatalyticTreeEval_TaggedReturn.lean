-- Prove2me | Definitions.Def_CatalyticTreeEval_TaggedReturn
-- name    : CatalyticTreeEval_TaggedReturn
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T07:58:08.461805+00:00
-- url     : https://prove2.me/theorems/4389cd78-ece0-4cc3-b6e6-1a428411ad62
-- title:
--   Native finite-context subroutine returns
-- statement:
--   Fix a native child machine with s control states and a finite context set of size t+1. A product controller retains one context tag during every child step. When the child first halts, the host reaches a live return port containing that tag. The table has exactly $$(t+1)(s+1)$$ states. All physical data actions are the original child actions; retaining the finite context adds no work cells. The live return port takes a further quiet native transition to halt, so a caller must charge its return dispatch explicitly. Both t and the child table are fixed before input, tape contents and runtime widths.
-- source:
--   Native composition infrastructure for Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, uniform subroutine and replay hosts.

import Definitions.Def_CatalyticTreeEval_MachineContracts

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.TaggedReturn

open CatalyticMatching.General

abbrev Control (A : Machine) (tags : ℕ) := Fin (tags + 1) × Option (Fin A.states)

noncomputable def encode (A : Machine) (tags : ℕ) :
    Control A tags ≃ Fin (Fintype.card (Control A tags)) := Fintype.equivFin _

noncomputable def liftInstruction (A : Machine) (tags : ℕ) (tag : Fin (tags + 1))
    (a : Instruction A.states) : Instruction (Fintype.card (Control A tags)) where
  next := some (encode A tags (tag, a.next))
  workWrite := a.workWrite
  catalystWrite := a.catalystWrite
  inputMove := a.inputMove
  workMove := a.workMove
  catalystMove := a.catalystMove
  emit := a.emit

/-- Retain one fixed finite context through a native subroutine. Source halt
reaches a live tagged return port; a further quiet transition would halt. -/
noncomputable def machine (A : Machine) (tags : ℕ) : Main.Machine where
  states := Fintype.card (Control A tags)
  start := encode A tags (⟨0, by omega⟩, some A.start)
  table q input work catalyst io wo co :=
    let control := (encode A tags).symm q
    match control.2 with
    | some source => liftInstruction A tags control.1 (A.table source input work catalyst io wo co)
    | none =>
      { next := none, workWrite := work, catalystWrite := none,
        inputMove := .stay, workMove := .stay, catalystMove := .stay, emit := none }

noncomputable def entry (A : Machine) (tags : ℕ) (tag : Fin (tags + 1)) :
    Fin (machine A tags).states := encode A tags (tag, some A.start)

noncomputable def returned (A : Machine) (tags : ℕ) (tag : Fin (tags + 1)) :
    Fin (machine A tags).states := encode A tags (tag, none)

noncomputable def embed (A : Machine) (tags : ℕ) (tag : Fin (tags + 1))
    (c : Configuration A) : Configuration (machine A tags) :=
  { c with state := some (encode A tags (tag, c.state)) }

end CatalyticTreeEval.Contracts.TaggedReturn


