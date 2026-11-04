-- Prove2me | Definitions.Def_Submission_ThreeSum_Bands
-- name    : Submission_ThreeSum_Bands
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:12.610405+00:00
-- url     : https://prove2.me/theorems/1e29cf9f-9b1f-48c3-ac03-f55ea6adfa7d
-- title:
--   Bands
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace ThreeSum.Bands
variable {I J K : Type*}
def Separated (lo hi : I → ℤ) : Prop :=
  ∀ i j, i ≠ j → hi i < lo j ∨ hi j < lo i
def Overlap (alo ahi : I → ℤ) (blo bhi : J → ℤ) (p : I × J) : Prop :=
  alo p.1 ≤ bhi p.2 ∧ blo p.2 ≤ ahi p.1
instance (alo ahi : I → ℤ) (blo bhi : J → ℤ) (p : I × J) :
    Decidable (Overlap alo ahi blo bhi p) :=
  inferInstanceAs (Decidable (alo p.1 ≤ bhi p.2 ∧ blo p.2 ≤ ahi p.1))
def overlapOwner (alo : I → ℤ) (blo : J → ℤ) (p : I × J) : I ⊕ J :=
  if alo p.1 ≤ blo p.2 then Sum.inr p.2 else Sum.inl p.1
def Relevant (alo ahi : I → ℤ) (blo bhi : J → ℤ) (clo chi : K → ℤ)
    (p : I × (J × K)) : Prop :=
  alo p.1 ≤ chi p.2.2 - blo p.2.1 ∧ clo p.2.2 - bhi p.2.1 ≤ ahi p.1
instance (alo ahi : I → ℤ) (blo bhi : J → ℤ) (clo chi : K → ℤ)
    (p : I × (J × K)) : Decidable (Relevant alo ahi blo bhi clo chi p) :=
  inferInstanceAs (Decidable
    (alo p.1 ≤ chi p.2.2 - blo p.2.1 ∧ clo p.2.2 - bhi p.2.1 ≤ ahi p.1))
def tripleOwner (alo : I → ℤ) (blo bhi : J → ℤ) (clo : K → ℤ)
    (p : I × (J × K)) : (J × K) ⊕ (I × (J ⊕ K)) :=
  if alo p.1 < clo p.2.2 - bhi p.2.1 then Sum.inl p.2
  else Sum.inr (p.1, overlapOwner (fun j => alo p.1 + blo j) clo p.2)
end ThreeSum.Bands


