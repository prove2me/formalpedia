-- Prove2me | Definitions.Def_ExpanderLib_MixingAux
-- name    : ExpanderLib_MixingAux
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:58:59.588118+00:00
-- url     : https://prove2.me/theorems/6d0277ee-cdc0-41e6-979a-934eb861d025
-- title:
--   Mixing Aux
-- statement:
--   Definitions and structural lemmas for Mixing Aux, from Juan Pablo Traverso Gianini (jtraverso/expander-spectral; see pinned Apache-2.0 LICENSE and source headers)'s pinned The expander mixing lemma and the Alon-Boppana bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/MixingAux.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Matrix
namespace Expanders
variable {V : Type*} [Fintype V]
end Expanders


