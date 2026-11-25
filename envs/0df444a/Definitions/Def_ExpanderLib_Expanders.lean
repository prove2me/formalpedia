-- Prove2me | Definitions.Def_ExpanderLib_Expanders
-- name    : ExpanderLib_Expanders
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:09:07.76738+00:00
-- url     : https://prove2.me/theorems/a7495050-f0ea-447c-982f-2e8ac9453786
-- title:
--   Expanders
-- statement:
--   Definitions and structural lemmas for Expanders, from Juan Pablo Traverso Gianini (jtraverso/expander-spectral; see pinned Apache-2.0 LICENSE and source headers)'s pinned The expander mixing lemma and the Alon-Boppana bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/Expanders.lean

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Matrix
namespace Expanders
variable {V : Type*} [Fintype V]
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℕ :=
  ((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card
end Expanders


