-- Prove2me | Definitions.Def_Erdos338_Structure
-- name    : Erdos338_Structure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:57:43.000514+00:00
-- url     : https://prove2.me/theorems/d504dda6-2aea-47de-bcfb-c60973bb059f
-- title:
--   Structure
-- statement:
--   Definitions and structural lemmas for Structure, from Veljko Janoski (veljjanoski/erdos338-palomar; includes Kneser's theorem adapted under Apache-2.0 from Mantas Baksys and Yael Dillies in YaelDillies/misc-yd and definitions under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 338: restricted order of robust sets of positive lower density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Structure.lean

module
public import Definitions.Def_Erdos338_Covering
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
open scoped Pointwise
namespace Erdos338Proof
open Classical in
/-- `cnt S b` is the number of elements of `S` below `b`. -/
noncomputable def cnt (S : Set ℕ) (b : ℕ) : ℕ := #((range b).filter (· ∈ S))
end Erdos338Proof


