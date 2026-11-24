-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
-- name    : Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:18.403118+00:00
-- url     : https://prove2.me/theorems/aee6f71f-9b73-4c53-875f-5d562e7c8177
-- title:
--   Finite strict-state recurrences for promotion and joint bounds
-- statement:
--   A strict numerical recipe records unary or paired arity, total guard degree, soft and hard cutoffs, and matching targets. A guard height contributes one unit above the soft cutoff and one above the effective hard cutoff. Scalar acceptance means total weight at most one and both target-height inequalities.
--
--   The local state list enumerates child heights $6,\ldots,12$ and lists of at most two guard heights above the destination soft cutoff; unary states duplicate the one target height. The source predicate accepts the source rank and rejects its successor. Numerical bounds comprise a flattened profile plus promotion and joint functions.
--
--   For each state, finite searches determine the highest permitted downward replacement and first harmful upward crossing of a guard. Own and guard promotion fees use the relevant child $A,C,M,P$ entries. Joint fees combine weak loss and strong gain, taking available child $J$ minima and accounting for occupied versus cold guard sockets. Their sum is the full branch fee.
--
--   The promotion checker bounds every covered source branch. The joint checker accepts either the known parent loss-plus-promotion estimate or a sharper bound for every source branch where promotion is possible. Separate interval, cold-no-gain, and cold-endpoint checks certify that every actual height transition is covered by the numerical endpoints. All checks range over explicit finite state and height lists.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalNumericRecurrence.lean lines 15–374; SHA256 a5770df37a51e23b906cd6cee034e85040644f7b9889626f6cdd7427ad34764c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityLocalNumeric
end SensitivityLocalNumeric



/-!
Finite local recurrence evaluator at the exact literal profiles. Heights are
one greater than the source's exact ranks, with zero denoting no accepted rank.
All ordered target pairs and all guard lists of length at most two are covered.
These definitions describe numeric certificates; semantic cost soundness is
provided separately by the event-set lemmas.
-/
namespace SensitivityLocalNumeric


structure Recipe where
  unary : Bool
  degree : ℕ
  soft : Fin 12 → ℕ
  hard : Fin 12 → ℕ
  lo : Fin 12 → ℕ → Fin 12
  hi : Fin 12 → ℕ → Fin 12

 def arrayEntry (values : Array ℕ) (j : Fin 12) : ℕ := values[j.val]?.getD 0
 def targetEntry (cold warm : Array ℕ) (j : Fin 12) (f : ℕ) : Fin 12 :=
  Fin.ofNat 12 (arrayEntry (if f = 0 then cold else warm) j)

def phase0 : Recipe :=
  ⟨true,1329,arrayEntry #[5,5,5,5,5,5,4,4,3,3,2,2],arrayEntry #[12,12,12,12,12,5,5,4,4,3,3,2],
    targetEntry #[7,7,7,7,7,7,7,8,9,10,11,11] #[7,7,7,7,7,7,8,10,9,10,11,11],
    targetEntry #[7,7,7,7,7,7,7,8,9,10,11,11] #[7,7,7,7,7,7,8,10,9,10,11,11]⟩









def weight (r : Recipe) (j : Fin 12) (height : ℕ) : ℕ :=
  (if r.soft j < height then 1 else 0) +
    (if (if r.hard j < 12 then r.hard j else r.soft j) < height then 1 else 0)

def accepts (r : Recipe) (j : Fin 12) (failures left right : ℕ) : Prop :=
  failures ≤ 1 ∧ (r.lo j failures).val < min left right ∧
    (r.hi j failures).val < max left right

instance (r : Recipe) (j : Fin 12) (f a b : ℕ) : Decidable (accepts r j f a b) := by
  unfold accepts
  infer_instance

structure State where
  left : ℕ
  right : ℕ
  guards : List ℕ
deriving DecidableEq, Repr

def failures (r : Recipe) (j : Fin 12) (s : State) : ℕ :=
  (s.guards.map (weight r j)).sum

def targetHeights : List ℕ := (List.range 7).map (· + 6)

def guardHeights (r : Recipe) (n : Fin 12) : List ℕ :=
  (List.range 13).filter (fun h => r.soft n < h)

def guardLists (heights : List ℕ) : List (List ℕ) :=
  [[]] ++ heights.map (fun h => [h]) ++
    heights.flatMap (fun a => heights.map (fun b => [a,b]))

def localStates (r : Recipe) (n : Fin 12) : List State :=
  targetHeights.flatMap fun a =>
    (if r.unary then [a] else targetHeights).flatMap fun b =>
      (guardLists (guardHeights r n)).map fun g => ⟨a,b,g⟩







def AdmissibleState (r : Recipe) (n : Fin 12) (s : State) : Prop :=
  5 < s.left ∧ s.left ≤ 12 ∧ 5 < s.right ∧ s.right ≤ 12 ∧
    s.guards.length ≤ 2 ∧ (∀ h ∈ s.guards, r.soft n < h ∧ h ≤ 12) ∧
      (r.unary = true → s.left = s.right)



def sourceCondition (r : Recipe) (x : Fin 12) (s : State) : Prop :=
  accepts r x (failures r x s) s.left s.right ∧
    ¬ accepts r (Fin.ofNat 12 (x.val + 1))
      (failures r (Fin.ofNat 12 (x.val + 1)) s) s.left s.right

instance (r : Recipe) (x : Fin 12) (s : State) : Decidable (sourceCondition r x s) := by
  unfold sourceCondition
  infer_instance

def pairOffset (i j : ℕ) : ℕ := i * 12 - i * (i - 1) / 2 + (j - i)

def entry (v : Array ℕ) (kind i j : ℕ) : ℕ :=
  v[kind * 78 + pairOffset i j]?.getD 0

structure Bounds where
  profile : Array ℕ
  promotion : ℕ → ℕ → ℕ
  joint : ℕ → ℕ → ℕ → ℕ

def need (r : Recipe) (j : Fin 12) (f mate : ℕ) : ℕ :=
  if 1 < f then 12 else
    if mate ≤ (r.lo j f).val then 12 else
      if mate ≤ (r.hi j f).val then (r.hi j f).val else (r.lo j f).val

def dropBot (r : Recipe) (n : Fin 12) (rest : ℕ) (s : State) (old : ℕ) : ℕ :=
  ((List.range old).reverse.find? fun fresh =>
    decide (accepts r n (rest + weight r n fresh) s.left s.right)).getD 12

def riseTop (r : Recipe) (c : Fin 12) (rest : ℕ) (s : State) (old : ℕ) : ℕ :=
  (((List.range 12).drop old).find? fun rank =>
    decide (¬ accepts r c (rest + weight r c (rank + 1)) s.left s.right)).getD 12





def promotionOwn (r : Recipe) (v : Bounds) (n : Fin 12) (s : State) : ℕ :=
  let f := failures r n s
  if 1 < f then 0 else
    if r.unary then
      if s.left ≤ (r.lo n f).val then entry v.profile 0 s.left (r.lo n f).val else 0
    else
      let fee := fun old mate =>
        let needed := need r n f mate
        if old ≤ needed ∧ needed < 12 then
          min (entry v.profile 3 old needed) (v.promotion (old - 1) needed) else 0
      fee s.left s.right + fee s.right s.left

def promotionGuard (r : Recipe) (v : Bounds) (n : Fin 12) (s : State) (old : ℕ) : ℕ :=
  let bot := dropBot r n (failures r n s - weight r n old) s old
  if bot < 12 then entry v.profile 2 bot (old - 1) else 0

def promotionFee (r : Recipe) (v : Bounds) (n : Fin 12) (s : State) : ℕ :=
  promotionOwn r v n s + (s.guards.map (promotionGuard r v n s)).sum

def ownInterval (r : Recipe) (c n : Fin 12) (s : State) (mate : ℕ) : ℕ × ℕ :=
  let fc := failures r c s
  let fn := failures r n s
  (if r.unary then (r.lo c fc).val else need r c fc mate,
    if 1 < fn then 12 else if r.unary then (r.lo n fn).val else need r n fn mate)

def jointOwnOne (r : Recipe) (v : Bounds) (c n : Fin 12) (s : State)
    (old mate : ℕ) : ℕ :=
  let (lower,upper) := ownInterval r c n s mate
  let loss := entry v.profile 2 lower (old - 1)
  if old ≤ upper ∧ upper < 12 then
    let gain := if r.unary then entry v.profile 0 old upper else
      min (entry v.profile 3 old upper) (v.promotion (old - 1) upper)
    min (loss + gain) (v.joint lower (old - 1) upper)
  else loss

def jointOwn (r : Recipe) (v : Bounds) (c n : Fin 12) (s : State) : ℕ :=
  jointOwnOne r v c n s s.left s.right +
    if r.unary then 0 else jointOwnOne r v c n s s.right s.left

def guardInterval (r : Recipe) (c n : Fin 12) (s : State) (old : ℕ) : ℕ × ℕ :=
  (riseTop r c (failures r c s - weight r c old) s old,
    dropBot r n (failures r n s - weight r n old) s old)

def emptyFee (r : Recipe) (v : Bounds) (c n : Fin 12) (s : State) : ℕ :=
  let top := riseTop r c (failures r c s) s 0
  if top < 12 then entry v.profile 0 (r.soft n) top else 0

def guardHigh (v : Bounds) (old top : ℕ) : ℕ :=
  if top < 12 then entry v.profile 0 old top else 0

def guardCombined (v : Bounds) (old top bot : ℕ) : ℕ :=
  let separate := guardHigh v old top +
    if bot < 12 then entry v.profile 2 bot (old - 1) else 0
  if 5 < old ∧ top < 12 ∧ bot < 12 then
    min separate (v.joint (max 5 bot) (old - 1) top) else separate

def guardSlots (r : Recipe) (v : Bounds) (z old top : ℕ) : ℕ :=
  if r.unary then 1 else if z < guardHigh v old top then 2 else 1

def jointGuards (r : Recipe) (v : Bounds) (c n : Fin 12) (s : State) : ℕ :=
  let z := emptyFee r v c n s
  let slotCount := (s.guards.map fun old =>
    guardSlots r v z old (guardInterval r c n s old).1).sum
  (r.degree - slotCount) * z + (s.guards.map fun old =>
    let (top,bot) := guardInterval r c n s old
    guardCombined v old top bot +
      (guardSlots r v z old top - 1) * guardHigh v old top).sum

def promotionPossible (r : Recipe) (c n : Fin 12) (s : State) : Prop :=
  (s.left ≤ (ownInterval r c n s s.right).2 ∧ (ownInterval r c n s s.right).2 < 12) ∨
    (r.unary = false ∧ s.right ≤ (ownInterval r c n s s.left).2 ∧
      (ownInterval r c n s s.left).2 < 12) ∨
    ∃ old ∈ s.guards, (guardInterval r c n s old).2 < 12

instance (r : Recipe) (c n : Fin 12) (s : State) : Decidable (promotionPossible r c n s) := by
  unfold promotionPossible
  infer_instance

def jointFee (r : Recipe) (v : Bounds) (c n : Fin 12) (s : State) : ℕ :=
  jointOwn r v c n s + jointGuards r v c n s

def promotionCheck (r : Recipe) (v : Bounds) (x n : Fin 12) (bound : ℕ) : Bool :=
  (localStates r n).all fun s =>
    decide (sourceCondition r x s → promotionFee r v n s ≤ bound)

def jointCheck (r : Recipe) (v : Bounds) (updated : Array ℕ)
    (c x n : Fin 12) (promotion bound : ℕ) : Bool :=
  decide (entry updated 2 c.val x.val + promotion ≤ bound) ||
    (decide (entry updated 2 c.val x.val ≤ bound) &&
      (localStates r n).all fun s => decide
        (sourceCondition r x s → accepts r c (failures r c s) s.left s.right →
          promotionPossible r c n s → jointFee r v c n s ≤ bound))





def intervalHit (L top bot height : ℕ) : Prop :=
  (top < L ∧ top < height) ∨ (bot < L ∧ height ≤ bot)

instance (L top bot height : ℕ) : Decidable (intervalHit L top bot height) := by
  unfold intervalHit
  infer_instance

def promotionIntervalsCheck (r : Recipe) (x n : Fin 12) : Bool :=
  (localStates r n).all fun s => decide (sourceCondition r x s →
    ∀ old ∈ s.guards, ∀ fresh : Fin 13,
      accepts r n (failures r n s - weight r n old + weight r n fresh.val) s.left s.right →
        let bot := dropBot r n (failures r n s - weight r n old) s old
        bot < 12 ∧ fresh.val ≤ bot)

def coldNoGainCheck (r : Recipe) (x n : Fin 12) : Bool :=
  (localStates r n).all fun s => decide (sourceCondition r x s →
    ∀ fresh : Fin 13,
      ¬ accepts r n (failures r n s + weight r n fresh.val) s.left s.right)



def coldEndpointCheck (r : Recipe) (c x n : Fin 12) : Bool :=
  (localStates r n).all fun s => decide (sourceCondition r x s →
    accepts r c (failures r c s) s.left s.right →
      let top := riseTop r c (failures r c s) s 0
      top < 12 → r.soft n ≤ top)



def jointIntervalsCheck (r : Recipe) (c x n : Fin 12) : Bool :=
  (localStates r n).all fun s => decide (sourceCondition r x s →
    accepts r c (failures r c s) s.left s.right →
      ((∀ fresh : Fin 13,
        ¬ accepts r c (failures r c s + weight r c fresh.val) s.left s.right →
          let top := riseTop r c (failures r c s) s 0
          top < 12 ∧ top < fresh.val) ∧
      ∀ old ∈ s.guards, ∀ fresh : Fin 13,
        (¬ accepts r c (failures r c s - weight r c old + weight r c fresh.val) s.left s.right ∨
          accepts r n (failures r n s - weight r n old + weight r n fresh.val) s.left s.right) →
        intervalHit 12 (guardInterval r c n s old).1 (guardInterval r c n s old).2 fresh.val))










end SensitivityLocalNumeric


