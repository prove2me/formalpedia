-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_HeadGainLocalFees
-- name    : Sensitivity214439_Phase0_Solutions_HeadGainLocalFees
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:19:43.277849+00:00
-- url     : https://prove2.me/theorems/0daceec0-96bd-4232-ae44-c15931371840
-- title:
--   Own-target prices for paired head repairs
-- statement:
--   The paired head pricing functions use the child prescribed-gain, promotion, color-switch, and directional profiles. Given an old height $h$ and needed rank $n<12$, the basic entry fee uses $C(h,n)$ and, for a strict old child, the smaller applicable promotion or switching fee. The sentinel $n\ge12$ has zero fee.
--
--   The needed rank is determined by the unchanged mate's height: it is unattainable if the mate does not exceed the lower target, equals the upper target if the mate does not exceed that target, and otherwise equals the lower target. An own socket is eligible only when the old guards are legal. When both children are strict and their color-match flag is false, a directional rise or fall price may further reduce its fee according to the socket side and orientation. The whole own-target fee is the sum of the two socket fees.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/HeadGainLocalFees.lean lines 7–57; SHA256 45b111576787892fa78d4977000db63e467dcc886e45eabe33aabc849a1269ee; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HeadGainNumericCore
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Range

namespace SensitivityHeadGainNumeric
end SensitivityHeadGainNumeric
namespace SensitivityPairedHeadFees
end SensitivityPairedHeadFees



/-! Computable target-entry and directional fees shared by finite certificate
checks and their actual Boolean-event interpretation. -/
namespace SensitivityPairedHeadFees

def headSwitchFee (values : SensitivityLocalNumeric.Bounds) (height needed : ℕ) : ℕ :=
  values.profile[312 + (height-1)*12 + needed]?.getD 0

def headEntryFee (values : SensitivityLocalNumeric.Bounds) (same : Bool) (height needed : ℕ) : ℕ :=
  if 12 ≤ needed then 0 else
  if height ≤ needed then
    let c := SensitivityLocalNumeric.entry values.profile 3 height needed
    if 5 < height then min c
      (if same then values.promotion (height-1) needed else headSwitchFee values height needed)
    else c
  else if same then 0 else headSwitchFee values height needed

def headNeed (limit lo hi mateHeight : ℕ) : ℕ :=
  if mateHeight ≤ lo then limit else if mateHeight ≤ hi then hi else lo

end SensitivityPairedHeadFees

namespace SensitivityHeadGainNumeric

open SensitivityPairedHeadFees

def sideHeight (s : State) (side : Bool) : ℕ := if side then s.right else s.left

def ownLegal (r : Recipe) (strong : Fin 12) (s : State) : Prop :=
  count s (r.soft strong) ≤ r.allowance strong ∧ count s (r.hard strong) = 0

instance (r : Recipe) (strong : Fin 12) (s : State) : Decidable (ownLegal r strong s) := by
  unfold ownLegal
  infer_instance

def ownNeed (r : Recipe) (strong : Fin 12) (s : State) (side : Bool) : ℕ :=
  headNeed 12 (r.lo strong (count s (r.soft strong))).val
    (r.hi strong (count s (r.soft strong))).val (sideHeight s (!side))

def directionFee (price : ℕ → ℕ → ℕ) (height needed : ℕ) : ℕ :=
  if 12 ≤ needed then 0 else price (height-1) needed

def ownSocketFee (r : Recipe) (values : SensitivityLocalNumeric.Bounds)
    (rise fall : ℕ → ℕ → ℕ) (strong : Fin 12) (s : State) (orientation side : Bool) : ℕ :=
  if ownLegal r strong s then
    let base := headEntryFee values s.same (sideHeight s side) (ownNeed r strong s side)
    if s.same = false ∧ 5 < s.left ∧ 5 < s.right then
      min base (directionFee (if side = orientation then rise else fall)
        (sideHeight s side) (ownNeed r strong s side))
    else base
  else 0

def ownFee (r : Recipe) (values : SensitivityLocalNumeric.Bounds)
    (rise fall : ℕ → ℕ → ℕ) (strong : Fin 12) (s : State) (orientation : Bool) : ℕ :=
  ownSocketFee r values rise fall strong s orientation false +
    ownSocketFee r values rise fall strong s orientation true

end SensitivityHeadGainNumeric


