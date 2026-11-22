-- Prove2me | Definitions.Def_GJKKL_History_FirstFailure
-- name    : GJKKL_History_FirstFailure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:32:23.291814+00:00
-- url     : https://prove2.me/theorems/626fc34d-72a4-4484-a263-e7cc60f9f750
-- title:
--   First Failure
-- statement:
--   Definitions and structural lemmas for First Failure, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/FirstFailure.lean

module
public import Definitions.Def_GJKKL_History_Freedman
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] (κ : Kernel α) (G : List α → Prop)
end GJKKL.History


