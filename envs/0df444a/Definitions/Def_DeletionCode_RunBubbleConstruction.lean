-- Prove2me | Definitions.Def_DeletionCode_RunBubbleConstruction
-- name    : DeletionCode_RunBubbleConstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:23:37.813577+00:00
-- url     : https://prove2.me/theorems/925740cf-500a-4477-81d4-0c325f814b17
-- title:
--   Run Bubble Construction
-- statement:
--   Definitions and structural lemmas for Run Bubble Construction, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean

import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
namespace DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
structure TrimmedRun (k : ℕ) (pre suffix : List Bool) (rho : ℕ)
    (bit : Bool) (orientation : Orientation) where
  bubble : BubbleWord k
  before : List Bool
  after : List Bool
  rho_eq : bubble.rho = rho
  bit_eq : bubble.bit = bit
  orientation_eq : bubble.orientation = orientation
  pre_eq : pre = before ++ bubble.left
  suffix_eq : suffix = bubble.right ++ after
  left_boundary : bubble.left.getLast? = some (!bubble.bit)
  right_boundary : bubble.right.head? = some (!bubble.bit)
def trimRun (k : ℕ) (pre suffix : List Bool) (rho : ℕ)
    (bit : Bool) (orientation : Orientation)
    (hrho : 1 ≤ rho) (hrho' : rho ≤ k + 1)
    (hpre : windowLength k - rho ≤ pre.length)
    (hsuffix : windowLength k - rho ≤ suffix.length)
    (hleft : pre.getLast? = some (!bit))
    (hright : suffix.head? = some (!bit)) :
    TrimmedRun k pre suffix rho bit orientation := by
  have hflank : 0 < windowLength k - rho := by
    unfold windowLength
    omega
  refine {
    bubble := {
      left := pre.drop (pre.length - (windowLength k - rho))
      right := suffix.take (windowLength k - rho)
      rho := rho
      bit := bit
      orientation := orientation
      rho_lower := hrho
      rho_upper := hrho'
      left_length := by simp only [List.length_drop]; omega
      right_length := by
        simp only [List.length_take, Nat.min_eq_left hsuffix]
    }
    before := pre.take (pre.length - (windowLength k - rho))
    after := suffix.drop (windowLength k - rho)
    rho_eq := rfl
    bit_eq := rfl
    orientation_eq := rfl
    pre_eq := (List.take_append_drop _ pre).symm
    suffix_eq := (List.take_append_drop _ suffix).symm
    left_boundary := ?_
    right_boundary := ?_
  }
  · change (pre.drop (pre.length - (windowLength k - rho))).getLast? = some (!bit)
    rw [List.getLast?_drop, if_neg (by omega)]
    exact hleft
  · change (suffix.take (windowLength k - rho)).head? = some (!bit)
    rw [List.head?_take, if_neg (by omega)]
    exact hright
namespace TrimmedRun
variable {k rho : ℕ} {pre suffix : List Bool} {bit : Bool} {orientation : Orientation}
end TrimmedRun
structure LocalBubble (k : ℕ) (source target : List Bool) (pos : ℕ)
    (orientation : Orientation) where
  bubble : BubbleWord k
  before : List Bool
  after : List Bool
  orientation_eq : bubble.orientation = orientation
  source_eq : source = before ++ bubble.negativeWord ++ after
  target_eq : target = before ++ bubble.positiveWord ++ after
  left_boundary : bubble.left.getLast? = some (!bubble.bit)
  right_boundary : bubble.right.head? = some (!bubble.bit)
  edit_start : before.length + bubble.left.length ≤ pos
  edit_stop : pos < before.length + windowLength k
namespace LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
end LocalBubble
end DeletionCode.RunBubbleConstruction


