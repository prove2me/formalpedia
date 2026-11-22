-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Necessity
-- name    : LeanPool_MatchingLogic_Necessity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:48.413706+00:00
-- url     : https://prove2.me/theorems/dcca5ce6-c2f8-420b-9c94-72594a274346
-- title:
--   Necessity
-- statement:
--   Definitions and structural lemmas for Necessity, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
namespace Necessity
abbrev S : Signature := ⟨Unit, fun _ => 1⟩
abbrev M : Model S :=
  { carrier := Fin 3
    nonempty := ⟨0⟩
    interp := fun _ a => if a 0 = 1 then ({0} : Set (Fin 3)) else ∅ }
abbrev C : Set (Fin 3) := {0}
section Generic
variable {Var : Type} [DecidableEq Var]
def psi (x : Var) : Pattern S Var := .app () (fun _ => .var x)
def rho : Var → Fin 3 := fun _ => 1
def rho' : Var → Fin 3 := fun _ => 2
end Generic
end Necessity
end MatchingLogic


