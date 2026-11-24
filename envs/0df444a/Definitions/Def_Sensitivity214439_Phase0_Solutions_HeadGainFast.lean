-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_HeadGainFast
-- name    : Sensitivity214439_Phase0_Solutions_HeadGainFast
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:19:38.760799+00:00
-- url     : https://prove2.me/theorems/f8350bd6-a87d-41fc-a1f6-f8e16c91de77
-- title:
--   Closed-form accepted guard intervals for paired head states
-- statement:
--   For a numerical paired head state, remove one guard's old occupancy from both soft and hard counts. The base predicate tests acceptance with that check absent; the next predicate tests acceptance after adding one soft failure. Define
--   $$
--   d_j=\min\!\left(12,h_j,
--   \begin{cases}12,&\text{the next predicate holds},\\s_j,&\text{otherwise}.\end{cases}\right).
--   $$
--   A replacement is possible at both weak and strong ranks when both base predicates hold. The common accepted cutoff is $\min(d_i,d_j)$, and the fast guard fee is the child exact-source entry $M(\min(d_i,d_j),h_{\rm old}-1)$ when replacement is possible, or zero otherwise.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/HeadGainFast.lean lines 7–138; SHA256 98ce5c601549530fc49cb5e66ee6543f3f956e87a65493a4a3b4af8859762691; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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



/-! Closed cutoff arithmetic for paired guard repairs, with equality to the
exhaustive finite-height definition. -/
namespace SensitivityHeadGainNumeric

def guardBase (r : Recipe) (j : Fin 12) (s : State) (old : ℕ) : Prop :=
  acceptsCounts r j s
    (count s (r.soft j) - SensitivityBaselineLossNumeric.occupied (r.soft j) old)
    (count s (r.hard j) - SensitivityBaselineLossNumeric.occupied (r.hard j) old)

instance (r : Recipe) (j : Fin 12) (s : State) (old : ℕ) : Decidable (guardBase r j s old) := by
  unfold guardBase
  infer_instance

def guardNext (r : Recipe) (j : Fin 12) (s : State) (old : ℕ) : Prop :=
  acceptsCounts r j s
    (count s (r.soft j) - SensitivityBaselineLossNumeric.occupied (r.soft j) old + 1)
    (count s (r.hard j) - SensitivityBaselineLossNumeric.occupied (r.hard j) old)

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







end SensitivityHeadGainNumeric


