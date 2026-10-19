-- Prove2me | Definitions.Def_AngelDevil_NiceReduction
-- name    : AngelDevil_NiceReduction
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:15:55.582059+00:00
-- url     : https://prove2.me/theorems/c56b8f68-ce47-4000-86d9-66bc21fc0bcf
-- title:
--   Nice Devil transformation and allowed finite journeys
-- statement:
--   For a finite history, a square is eligible for a Nice Devil precisely when it is not the origin and is outside the power-p neighbourhood of every position except the last. The transformed Devil applies the original Devil to the reduced history, and retains its selected square exactly when eligible; otherwise it passes. An allowed journey starts at the origin, has legal jumps, and never lands on any square selected by the Devil at an earlier prefix, including the selection immediately before landing.
-- source:
--   Andras Mathe, The Angel of power 2 wins, CPC 16 (2007), 363-374; https://doi.org/10.1017/S0963548306008303; author manuscript internal pagination. Definition 2.5 and following discussion, p. 2; equation (2), p. 3.

import Definitions.Def_AngelDevil_ReducedJourney

namespace AngelDevil

/- Equation (2): protect the origin and the neighbourhood of every position
strictly before the current one. The Devil may still eat the current position
when it is not protected by an earlier position. -/
def NiceEligible (p : Nat) (h : List Point) (z : Point) : Prop :=
  z ≠ origin ∧ ∀ v ∈ h.dropLast, ¬ Jump p v z

instance niceEligibleDecidable (p : Nat) (h : List Point) (z : Point) :
    Decidable (NiceEligible p h z) := by
  unfold NiceEligible
  infer_instance

def niceReduction (p : Nat) (D : DevilStrategy) : DevilStrategy := fun h =>
  match D (reducedJourney p h) with
  | none => none
  | some z => if NiceEligible p h z then some z else none

/- An allowed finite journey: the Devil acts on prefix i before landing j,
so all pairs i < j must be checked, not only consecutive moves. -/
def Allowed (p : Nat) (D : DevilStrategy) (h : List Point) : Prop :=
  Journey p h ∧ ∀ (i j : Nat) (z : Point), i < j → h[j]? = some z →
    D (h.take (i+1)) ≠ some z

end AngelDevil


