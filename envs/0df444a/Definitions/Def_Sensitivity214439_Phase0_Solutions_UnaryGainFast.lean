-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainFast
-- name    : Sensitivity214439_Phase0_Solutions_UnaryGainFast
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:33.090866+00:00
-- url     : https://prove2.me/theorems/759f9576-00c6-4f55-a1a8-725f811f64e8
-- title:
--   Closed-form unary guard cutoffs and warm checks
-- statement:
--   Guard monotonicity requires the soft cutoff to be at most the hard cutoff and the target to be nondecreasing between adjacent legal failure counts. Removing a selected guard gives a base acceptance predicate; adding one soft failure to that base gives the next predicate. The accepted-height cutoff is
--   $$
--   d_j=\min\!\left(12,h_j,
--   \begin{cases}12,&\text{the next predicate holds},\\s_j,&\text{otherwise}.\end{cases}\right).
--   $$
--   A guard replacement is possible at both ranks when both base predicates hold. Its fast fee is the exact-source entry $M(\min(d_i,d_j),h_{\rm old}-1)$, or zero when impossible.
--
--   Fast local validity requires a needed own-target rise whenever guards are legal, strictly downward feasible occupied-guard repairs, no feasible cold repair, and the total fee at most the supplied bound. The warm checker imposes these conditions on every enumerated state rejecting the weak rank.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainFast.lean lines 10–169; SHA256 428f440faee9336a86c07994867c663c320f717a9edfebdff23cf74cc11d15e6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range

namespace SensitivityUnaryGainNumeric
end SensitivityUnaryGainNumeric



/-!
The accepted new guard heights form an initial interval.  Computing its two
threshold endpoints avoids enumerating all thirteen heights inside every
numeric C certificate.  The equality with the exhaustive definition is proved.
-/
namespace SensitivityUnaryGainNumeric

def GuardMonotone (r : Recipe) (j : Fin 12) : Prop :=
  r.soft j ≤ r.hard j ∧ ∀ f, f+1 ≤ r.allowance j → r.target j f ≤ r.target j (f+1)

def guardBase (r : Recipe) (j : Fin 12) (s : State) (old : ℕ) : Prop :=
  accepts r j (count (r.soft j) s.guards - occupied (r.soft j) old)
    (count (r.hard j) s.guards - occupied (r.hard j) old) s.height

instance (r : Recipe) (j : Fin 12) (s : State) (old : ℕ) : Decidable (guardBase r j s old) := by
  unfold guardBase
  infer_instance

def guardNext (r : Recipe) (j : Fin 12) (s : State) (old : ℕ) : Prop :=
  accepts r j (count (r.soft j) s.guards - occupied (r.soft j) old + 1)
    (count (r.hard j) s.guards - occupied (r.hard j) old) s.height

instance (r : Recipe) (j : Fin 12) (s : State) (old : ℕ) : Decidable (guardNext r j s old) := by
  unfold guardNext
  infer_instance

def guardCut (r : Recipe) (j : Fin 12) (s : State) (old : ℕ) : ℕ :=
  min 12 (min (r.hard j) (if guardNext r j s old then 12 else r.soft j))





def guardPossible (r : Recipe) (i j : Fin 12) (s : State) (old : ℕ) : Prop :=
  guardBase r i s old ∧ guardBase r j s old

instance (r : Recipe) (i j : Fin 12) (s : State) (old : ℕ) :
    Decidable (guardPossible r i j s old) := by
  unfold guardPossible
  infer_instance

def guardTopFast (r : Recipe) (i j : Fin 12) (s : State) (old : ℕ) : ℕ :=
  min (guardCut r i s old) (guardCut r j s old)







def guardFeeFast (r : Recipe) (input : Array ℕ) (i j : Fin 12) (s : State) (old : ℕ) : ℕ :=
  if guardPossible r i j s old then
    SensitivityLocalNumeric.entry input 2 (guardTopFast r i j s old) (old-1) else 0



def localValidFast (r : Recipe) (input : Array ℕ) (i j : Fin 12) (bound : ℕ) (s : State) : Prop :=
  (legal r j (count (r.soft j) s.guards) (count (r.hard j) s.guards) →
    s.height ≤ (r.target j (count (r.soft j) s.guards)).val) ∧
  (s.guards.all fun old => decide (guardPossible r i j s old →
    guardTopFast r i j s old < old)) = true ∧
  ¬ guardPossible r i j s 0 ∧
    ownFee r input j s + (s.guards.map (guardFeeFast r input i j s)).sum ≤ bound

instance (r : Recipe) (input : Array ℕ) (i j : Fin 12) (bound : ℕ) (s : State) :
    Decidable (localValidFast r input i j bound s) := by
  unfold localValidFast
  infer_instance



def warmCheckFast (r : Recipe) (input : Array ℕ) (i j : Fin 12) (bound : ℕ) : Bool :=
  (warmStates r j).all fun s => decide (¬ acceptsState r i s → localValidFast r input i j bound s)






end SensitivityUnaryGainNumeric


