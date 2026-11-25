-- Prove2me | Definitions.Def_ExpanderSpectral_Solution
-- name    : ExpanderSpectral_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:19:23.272092+00:00
-- url     : https://prove2.me/theorems/eb25a02a-cdc3-43df-9fed-b870b18b8d97
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/expander-spectral; see pinned Apache-2.0 LICENSE and source headers)'s pinned The expander mixing lemma and the Alon-Boppana bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/Solution.lean

module
public import Mathlib
public import Definitions.Def_ExpanderLib_Expanders
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Matrix
namespace ExpanderTheorem
variable {V : Type*} [Fintype V]
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℕ :=
  ((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card
end ExpanderTheorem


