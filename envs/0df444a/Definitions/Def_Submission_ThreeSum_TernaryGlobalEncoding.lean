-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
-- name    : Submission_ThreeSum_TernaryGlobalEncoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:19.132427+00:00
-- url     : https://prove2.me/theorems/b547969b-ad03-43b3-a13b-680eb191f2e4
-- title:
--   Ternary Global Encoding
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data

set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryGlobalEncoding
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]
variable (maps : I → Coordinate (Fin L) → ZMod p) (occ : Ω → I)
  (edge : Ω → LocalEdge L α π)
def rawSource (w : Coordinate (Fin L) → ZMod p) (tag : Bool) (a : TritWord L) : ℤ :=
  (w (Sum.inr tag)).val + ∑ i, ((w (Sum.inl i)).val : ℤ)*(a i).val
def rawLeft (c : Ω) : ℤ := -rawSource (maps (occ c)) false (left (edge c))
def rawRight (c : Ω) : ℤ := rawSource (maps (occ c)) true (right (edge c))
def rawOutput (w : Coordinate (Fin L) → ZMod p) (q : TritWord L) : ℤ :=
  (w (Sum.inr false)).val+(w (Sum.inr true)).val+
    ∑ i, ((w (Sum.inl i)).val : ℤ)*(q i).val
abbrev OutputBlock (L : ℕ) (π : DigitType) (I : Type*) := I × {q // q ∈ vertices L π}
def blockOfChoice (c : Ω) : OutputBlock L π I := by
  classical
  exact (occ c,⟨output (edge c),mem_filter.mpr ⟨mem_univ _,(edge_data (edge c)).2.2.1⟩⟩)
def blockKey (b : OutputBlock L π I) : ℤ := rawOutput (maps b.1) b.2.val
def representations (J : ℕ) (a b : ℤ) : Finset (List Ω) :=
  Radix.representations (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) J a b
def wantedRepresentations (J : ℕ) (a b c : ℤ) : Finset (List Ω) :=
  (representations maps occ edge J (-a) b).filter fun xs =>
    (p : ℤ)^J ∣ c-Radix.positionalHash (p : ℤ) (blockKey maps) (xs.map (blockOfChoice occ edge))
end ThreeSum.TernaryGlobalEncoding


