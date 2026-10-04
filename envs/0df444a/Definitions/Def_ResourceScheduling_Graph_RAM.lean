-- Prove2me | Definitions.Def_ResourceScheduling_Graph_RAM
-- name    : ResourceScheduling_Graph_RAM
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T13:36:01.844989+00:00
-- url     : https://prove2.me/theorems/2adbc59f-b5c4-4c66-80ef-27e9b23ce013
-- title:
--   ResourceScheduling Graph RAM
-- statement:
--   Natural registers represented by stack lengths, with separate input, reversed output, and six cleared scratch stacks.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackSpecification
import Definitions.Def_ResourceScheduling_Graph_WordProgram

set_option autoImplicit false
namespace ResourceScheduling.Graph
open CookPvsNP

/-- Natural registers are represented by stack lengths; their letters need not be canonical. -/
structure RAMState (V : Type) where
  val : V → ℕ
  word : List Letter
  out : List Letter

abbrev RAMWire (V : Type) := (V ⊕ Fin 6) ⊕ Bool
def ramReg {V : Type} (v : V) : RAMWire V := .inl (.inl v)
def ramTmp {V : Type} (i : Fin 6) : RAMWire V := .inl (.inr i)
def ramInput {V : Type} : RAMWire V := .inr false
def ramOutput {V : Type} : RAMWire V := .inr true

def RAMRep {V : Type} (s : RAMState V) (l : RAMWire V → List Letter) : Prop :=
  (∀ v, (l (ramReg v)).length = s.val v) ∧ l ramInput = s.word ∧
    l ramOutput = s.out ∧ ∀ i, l (ramTmp i) = []

def RAMState.set {V : Type} [DecidableEq V] (s : RAMState V) (v : V) (n : ℕ) : RAMState V :=
  { s with val := Function.update s.val v n }

end ResourceScheduling.Graph


