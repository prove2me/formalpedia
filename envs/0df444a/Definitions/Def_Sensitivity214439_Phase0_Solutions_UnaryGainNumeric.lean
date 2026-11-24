-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
-- name    : Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:48:36.3669+00:00
-- url     : https://prove2.me/theorems/e05394b7-47fb-4cab-9391-702d8a8d1e73
-- title:
--   Numerical ordinary and warm gain model for unary gates
-- statement:
--   A unary recipe specifies soft and hard cutoffs, an allowance, and a target rank. A state consists of the own child height and a list of occupied guard heights. It accepts when the soft count is affordable, the hard count is zero, and the own height exceeds the target.
--
--   For a chosen old guard height, the candidate set contains all replacement heights $0,\ldots,12$ accepted at both weak and strong ranks. Its maximum determines the guard's exact-source $M$-fee. The own fee is the relevant child $A$-entry when the guards are legal; the total fee adds all listed guard fees. Local validity requires own repair to be upward, every possible occupied-guard repair to be downward, no possible cold repair, and the total fee below the bound.
--
--   The warm-state list enumerates own heights $0,\ldots,12$ and at most two guards above the destination soft cutoff. For ordinary target $7$ and allowance $q$, the fee is
--   $$
--   \mathbf1_{f\le q,\ h\le7}A(h,7)
--   +\mathbf1_{f>0,\ f-1\le q,\ h>7}\,fB(5,5).
--   $$
--   The ordinary checker tests this fee over finite heights and failure counts consistent with weak rejection and one-bit destination repair. The literal phase-zero recipe is included.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainNumeric.lean lines 12–157; SHA256 5c1ca2c0fb6d5a3bb3dd3161215b590b131a506c60b0fcab09ef484cb3d7582b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range

namespace SensitivityUnaryGainNumeric
end SensitivityUnaryGainNumeric



/-!
Finite prescribed-gain checks for the literal unary recipe.  The weak source
may be ordinary, so soft and hard counts are kept separately.  At a warm
destination only zero, one, or two originally positive soft guards can occur.
All own heights, including the completely false height zero, are covered.
-/
namespace SensitivityUnaryGainNumeric

structure Recipe where
  soft : Fin 12 → ℕ
  hard : Fin 12 → ℕ
  allowance : Fin 12 → ℕ
  target : Fin 12 → ℕ → Fin 12

def phase0 : Recipe where
  soft := SensitivityLocalNumeric.phase0.soft
  hard := SensitivityLocalNumeric.phase0.hard
  allowance := fun j => (#[5,4,3,2,1,1,1,1,1,1,1,1] : Array ℕ)[j.val]?.getD 0
  target := SensitivityLocalNumeric.phase0.lo

def occupied (cutoff height : ℕ) : ℕ := if cutoff < height then 1 else 0

def count (cutoff : ℕ) (heights : List ℕ) : ℕ := (heights.map (occupied cutoff)).sum

def legal (r : Recipe) (j : Fin 12) (softCount hardCount : ℕ) : Prop :=
  softCount ≤ r.allowance j ∧ hardCount = 0

instance (r : Recipe) (j : Fin 12) (f g : ℕ) : Decidable (legal r j f g) := by
  unfold legal
  infer_instance

def accepts (r : Recipe) (j : Fin 12) (softCount hardCount height : ℕ) : Prop :=
  legal r j softCount hardCount ∧ (r.target j softCount).val < height

instance (r : Recipe) (j : Fin 12) (f g height : ℕ) : Decidable (accepts r j f g height) := by
  unfold accepts
  infer_instance

structure State where
  height : ℕ
  guards : List ℕ
deriving DecidableEq, Repr

def acceptsState (r : Recipe) (j : Fin 12) (s : State) : Prop :=
  accepts r j (count (r.soft j) s.guards) (count (r.hard j) s.guards) s.height

instance (r : Recipe) (j : Fin 12) (s : State) : Decidable (acceptsState r j s) := by
  unfold acceptsState
  infer_instance

def afterGuard (r : Recipe) (j : Fin 12) (s : State) (old fresh : ℕ) : Prop :=
  accepts r j
    (count (r.soft j) s.guards - occupied (r.soft j) old + occupied (r.soft j) fresh)
    (count (r.hard j) s.guards - occupied (r.hard j) old + occupied (r.hard j) fresh) s.height

instance (r : Recipe) (j : Fin 12) (s : State) (old fresh : ℕ) :
    Decidable (afterGuard r j s old fresh) := by
  unfold afterGuard
  infer_instance

def guardCandidates (r : Recipe) (i j : Fin 12) (s : State) (old : ℕ) : Finset ℕ :=
  (Finset.range 13).filter fun fresh => afterGuard r i s old fresh ∧ afterGuard r j s old fresh

def guardTop (r : Recipe) (i j : Fin 12) (s : State) (old : ℕ) : ℕ :=
  (guardCandidates r i j s old).sup id



def ownFee (r : Recipe) (input : Array ℕ) (j : Fin 12) (s : State) : ℕ :=
  let f := count (r.soft j) s.guards
  if legal r j f (count (r.hard j) s.guards) then
    SensitivityLocalNumeric.entry input 0 s.height (r.target j f).val else 0

def guardFee (r : Recipe) (input : Array ℕ) (i j : Fin 12) (s : State) (old : ℕ) : ℕ :=
  if (guardCandidates r i j s old).Nonempty then
    SensitivityLocalNumeric.entry input 2 (guardTop r i j s old) (old-1) else 0

def totalFee (r : Recipe) (input : Array ℕ) (i j : Fin 12) (s : State) : ℕ :=
  ownFee r input j s + (s.guards.map (guardFee r input i j s)).sum

def localValid (r : Recipe) (input : Array ℕ) (i j : Fin 12) (bound : ℕ) (s : State) : Prop :=
  (legal r j (count (r.soft j) s.guards) (count (r.hard j) s.guards) →
    s.height ≤ (r.target j (count (r.soft j) s.guards)).val) ∧
  (s.guards.all fun old => decide ((guardCandidates r i j s old).Nonempty →
    guardTop r i j s old < old)) = true ∧
  ¬ (guardCandidates r i j s 0).Nonempty ∧ totalFee r input i j s ≤ bound

instance (r : Recipe) (input : Array ℕ) (i j : Fin 12) (bound : ℕ) (s : State) :
    Decidable (localValid r input i j bound s) := by
  unfold localValid
  infer_instance



def guardHeights (r : Recipe) (j : Fin 12) : List ℕ :=
  (List.range 13).filter (fun h => r.soft j < h)

def warmStates (r : Recipe) (j : Fin 12) : List State :=
  (List.range 13).flatMap fun h =>
    (SensitivityLocalNumeric.guardLists (guardHeights r j)).map fun g => ⟨h,g⟩







def ordinaryFee (input : Array ℕ) (q height failures : ℕ) : ℕ :=
  (if failures ≤ q ∧ height ≤ 7 then SensitivityLocalNumeric.entry input 0 height 7 else 0) +
  (if 0 < failures ∧ failures-1 ≤ q ∧ 7 < height then
    failures * SensitivityLocalNumeric.entry input 1 5 5 else 0)

def ordinaryCheck (input : Array ℕ) (i j : Fin 12) (bound : ℕ) : Prop :=
  ∀ (height : Fin 13) (failures : Fin 7),
    failures.val ≤ phase0.allowance j + 1 →
    ¬ (failures.val ≤ phase0.allowance i ∧ 7 < height.val) →
    ordinaryFee input (phase0.allowance j) height.val failures.val ≤ bound

instance (input : Array ℕ) (i j : Fin 12) (bound : ℕ) : Decidable (ordinaryCheck input i j bound) := by
  unfold ordinaryCheck
  infer_instance




end SensitivityUnaryGainNumeric


