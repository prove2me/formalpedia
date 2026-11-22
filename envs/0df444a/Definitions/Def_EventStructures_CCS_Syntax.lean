-- Prove2me | Definitions.Def_EventStructures_CCS_Syntax
-- name    : EventStructures_CCS_Syntax
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:35:46.248048+00:00
-- url     : https://prove2.me/theorems/d5e036b6-0781-4bce-ade7-5529a2d889b3
-- title:
--   Syntax
-- statement:
--   Definitions and structural lemmas for Syntax, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Syntax.lean

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
set_option autoImplicit true
namespace CCS
inductive Label (Name : Type*) where
  | inp : Name → Label Name
  | out : Name → Label Name
namespace Label
variable {Name Name' : Type*}
def co : Label Name → Label Name
  | inp n => out n
  | out n => inp n
def map (f : Name → Name') : Label Name → Label Name'
  | inp n => inp (f n)
  | out n => out (f n)
def strip : Label (Option Name) → Option (Label Name)
  | inp none => none
  | inp (some n) => some (inp n)
  | out none => none
  | out (some n) => some (out n)
end Label
inductive Action (Name : Type*) where
  | vis : Label Name → Action Name
  | tau : Action Name
namespace Action
variable {Name Name' : Type*}
def map (f : Name → Name') : Action Name → Action Name'
  | vis a => vis (a.map f)
  | tau => tau
def strip : Action (Option Name) → Option (Action Name)
  | vis a => a.strip.map vis
  | tau => some tau
end Action
universe u
inductive Process : Type u → Type (u + 1) where
  | nil {Name : Type u} : Process Name
  | pre {Name : Type u} : Action Name → Process Name → Process Name
  | sum {Name : Type u} : Process Name → Process Name → Process Name
  | par {Name : Type u} : Process Name → Process Name → Process Name
  | res {Name : Type u} : Process (Option Name) → Process Name
inductive Step : ∀ {Name : Type*}, Process Name → Action Name → Process Name → Prop where
  | pre {Name} {α : Action Name} {P : Process Name} : Step (.pre α P) α P
  | sumL {Name} {P : Process Name} {α : Action Name} {P' Q : Process Name} :
      Step P α P' → Step (.sum P Q) α P'
  | sumR {Name} {P Q : Process Name} {α : Action Name} {Q' : Process Name} :
      Step Q α Q' → Step (.sum P Q) α Q'
  | parL {Name} {P : Process Name} {α : Action Name} {P' Q : Process Name} :
      Step P α P' → Step (.par P Q) α (.par P' Q)
  | parR {Name} {P Q : Process Name} {α : Action Name} {Q' : Process Name} :
      Step Q α Q' → Step (.par P Q) α (.par P Q')
  | parSync {Name} {P : Process Name} {a : Label Name} {P' Q Q' : Process Name} :
      Step P (.vis a) P' → Step Q (.vis a.co) Q' → Step (.par P Q) .tau (.par P' Q')
  | res {Name} {P : Process (Option Name)} {α : Action Name} {P' : Process (Option Name)} :
      Step P (Action.map some α) P' → Step (.res P) α (.res P')
end CCS


