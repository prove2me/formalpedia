-- Prove2me | Definitions.Def_APFPaper1_RankExtend
-- name    : APFPaper1_RankExtend
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-08T04:14:00.071915+00:00
-- url     : https://prove2.me/theorems/52053a24-5455-48a2-b8c3-53a6f62178af
-- title:
--   Finite set accumulated by list insertion
-- statement:
--   For any type D with decidable equality, extend inserts every list member into an initial finite set. Repetitions are allowed. extend represents only the finite set accumulated from an ordered list by insertion; it neither represents nor certifies the paper's additional tested, distinct, admissible and support-novel chain conditions.
-- source:
--   Paper1 Supplement v9.27:2836–2847,2853–2856. Existing seed extension_union, ordinary finite-set bookkeeping. Inputs revision2026-10-04.1 is the policy baseline; no physical input consumed. Exact extend recursion and theorem proof body preserved; unrelated historical Ranks/cost definitions and project imports removed. extend represents only the finite set accumulated from an ordered list by insertion; it neither represents nor certifies the paper's additional tested, distinct, admissible and support-novel chain conditions.

import Mathlib.Data.Finset.Card

namespace APFPaper1.Ranks

def extend {D : Type*} [DecidableEq D] : Finset D → List D → Finset D
  | S, [] => S
  | S, d :: ds => extend (insert d S) ds

end APFPaper1.Ranks


