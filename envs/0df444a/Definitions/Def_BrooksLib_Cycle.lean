-- Prove2me | Definitions.Def_BrooksLib_Cycle
-- name    : BrooksLib_Cycle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:27:03.161866+00:00
-- url     : https://prove2.me/theorems/13fd53c4-2dd8-4b10-abe2-ff2d062432f8
-- title:
--   Cycle
-- statement:
--   Definitions and structural lemmas for Cycle, from Juan Pablo Traverso Gianini (jtraverso/brooks; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos-Rubin-Taylor degree-choosability, block-cut trees, and Brooks' theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean

module
public import Definitions.Def_BrooksLib_Greedy
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace BrooksTheorem
namespace Aux
variable {V : Type*} [Fintype V]
open Classical in
/-- A neighbour of `a` different from `b` (if any). -/
noncomputable def other (G : SimpleGraph V) (a b : V) : V :=
  if h : ((nb G a).erase b).Nonempty then h.choose else a
noncomputable def pseq (G : SimpleGraph V) (v0 v1 : V) : ℕ → V × V
  | 0 => (v0, v1)
  | n + 1 => ((pseq G v0 v1 n).2, other G (pseq G v0 v1 n).2 (pseq G v0 v1 n).1)
noncomputable def sq (G : SimpleGraph V) (v0 v1 : V) (n : ℕ) : V := (pseq G v0 v1 n).1
section
variable (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (v0 v1 : V) (h01 : G.Adj v0 v1)
end
end Aux
end BrooksTheorem


