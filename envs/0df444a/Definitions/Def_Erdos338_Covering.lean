-- Prove2me | Definitions.Def_Erdos338_Covering
-- name    : Erdos338_Covering
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:57:06.53933+00:00
-- url     : https://prove2.me/theorems/3aca83f0-8131-5ae7-8739-331f18925820
-- title:
--   Covering
-- statement:
--   Definitions and structural lemmas for Covering, from Veljko Janoski (veljjanoski/erdos338-palomar; includes Kneser's theorem adapted under Apache-2.0 from Mantas Baksys and Yael Dillies in YaelDillies/misc-yd and definitions under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 338: restricted order of robust sets of positive lower density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Covering.lean

module
public import Mathlib
public import Definitions.Def_Erdos338_Kneser_Kneser
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
open scoped Pointwise
namespace Erdos338Proof
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
end Erdos338Proof


