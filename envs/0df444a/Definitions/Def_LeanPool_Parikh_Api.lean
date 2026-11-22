-- Prove2me | Definitions.Def_LeanPool_Parikh_Api
-- name    : LeanPool_Parikh_Api
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:56:20.302996+00:00
-- url     : https://prove2.me/theorems/e7de3e0c-a1aa-4cfe-9c25-d4daded7d97d
-- title:
--   Api
-- statement:
--   Definitions and structural lemmas for Api, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
abbrev CountVector (T : Type*) := Vector T
abbrev LinearComponent (T : Type*) := Component T
abbrev SemilinearRepresentation (T : Type*) := Witness T
abbrev parikhVector {T : Type*} [DecidableEq T] (w : List T) : CountVector T := counts w
abbrev parikhImage {T : Type*} [DecidableEq T] (L : Language T) : Set (CountVector T) := image L
abbrev LinearComponent.denotation {T : Type*} (c : LinearComponent T) : Set (CountVector T) :=
  Component.denotation c
abbrev SemilinearRepresentation.denotation {T : Type*}
    (W : SemilinearRepresentation T) : Set (CountVector T) := Witness.denotation W
abbrev compileGrammar (g : EncodedGrammar) : SemilinearRepresentation (Fin g.terminalCount) :=
  compiler.compile g
end Parikh


