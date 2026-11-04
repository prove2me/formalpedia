-- Prove2me | Definitions.Def_Submission_ThreeSum_SubsetTransport
-- name    : Submission_ThreeSum_SubsetTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:08.71762+00:00
-- url     : https://prove2.me/theorems/8b1c9d57-b7c0-4759-b8d2-7aa8c6c5bb87
-- title:
--   Subset Transport
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean

import Definitions.Def_Submission_ThreeSum_Subset
set_option autoImplicit false
namespace ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
def reindex (e : α ≃ β) (f : Finset α → ℤ) (S : Finset β) : ℤ :=
  f (S.map e.symm.toEmbedding)
end ThreeSum.SubsetTransport


