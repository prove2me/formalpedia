-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_HeadGainNumericCore
-- name    : Sensitivity214439_Phase0_Solutions_HeadGainNumericCore
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:27.634853+00:00
-- url     : https://prove2.me/theorems/22ff7088-3a1d-4800-a46a-c7981c08b0c2
-- title:
--   Finite paired head states and replacement acceptance
-- statement:
--   A paired numerical head state consists of two child heights, a Boolean color-match flag, and a list of occupied guard heights. Counts are sums of the indicators $\mathbf1_{\text{cutoff}<h}$. At rank $j$, acceptance requires the match flag to be true, the soft count within allowance, hard count zero, and
--   $$
--   \ell_j(f)<\min(h_0,h_1),\qquad
--   u_j(f)<\max(h_0,h_1).
--   $$
--   Replacing one guard updates each count by subtracting its old occupancy and adding its new occupancy. A good replacement accepts at both weak and strong ranks. Admissible destination states have both child heights at most $12$, at most two occupied guards, and every recorded guard height strictly above the destination soft cutoff and at most $12$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/HeadGainNumericCore.lean lines 6–150; SHA256 cc6d381ba4b7201e0b69456b3d99afc05052cfbe8de8f548b7b994a81ab52855; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Range

namespace SensitivityHeadGainNumeric
end SensitivityHeadGainNumeric



/-! Finite full-recipe states for ordinary and warm parent gain certificates. -/
namespace SensitivityHeadGainNumeric

abbrev Recipe := SensitivityBaselineLossNumeric.Recipe

structure State where
  left : ℕ
  right : ℕ
  same : Bool
  guards : List ℕ

def count (s : State) (cutoff : ℕ) : ℕ :=
  (s.guards.map (SensitivityBaselineLossNumeric.occupied cutoff)).sum

def acceptsCounts (r : Recipe) (j : Fin 12) (s : State) (soft hard : ℕ) : Prop :=
  s.same = true ∧ soft ≤ r.allowance j ∧ hard = 0 ∧
    (r.lo j soft).val < min s.left s.right ∧ (r.hi j soft).val < max s.left s.right

instance (r : Recipe) (j : Fin 12) (s : State) (soft hard : ℕ) :
    Decidable (acceptsCounts r j s soft hard) := by
  unfold acceptsCounts
  infer_instance

def accepts (r : Recipe) (j : Fin 12) (s : State) : Prop :=
  acceptsCounts r j s (count s (r.soft j)) (count s (r.hard j))

instance (r : Recipe) (j : Fin 12) (s : State) : Decidable (accepts r j s) := by
  unfold accepts
  infer_instance

def updatedCount (s : State) (cutoff old fresh : ℕ) : ℕ :=
  count s cutoff - SensitivityBaselineLossNumeric.occupied cutoff old +
    SensitivityBaselineLossNumeric.occupied cutoff fresh

def afterGuard (r : Recipe) (j : Fin 12) (s : State) (old fresh : ℕ) : Prop :=
  acceptsCounts r j s (updatedCount s (r.soft j) old fresh) (updatedCount s (r.hard j) old fresh)

instance (r : Recipe) (j : Fin 12) (s : State) (old fresh : ℕ) :
    Decidable (afterGuard r j s old fresh) := by
  unfold afterGuard
  infer_instance

def guardGood (r : Recipe) (weak strong : Fin 12) (s : State) (old fresh : ℕ) : Prop :=
  afterGuard r weak s old fresh ∧ afterGuard r strong s old fresh

instance (r : Recipe) (weak strong : Fin 12) (s : State) (old fresh : ℕ) :
    Decidable (guardGood r weak strong s old fresh) := by
  unfold guardGood
  infer_instance





















def Admissible (r : Recipe) (strong : Fin 12) (s : State) : Prop :=
  s.left ≤ 12 ∧ s.right ≤ 12 ∧ s.guards.length ≤ 2 ∧
    (∀ h ∈ s.guards, r.soft strong < h ∧ h ≤ 12)

instance (r : Recipe) (strong : Fin 12) (s : State) : Decidable (Admissible r strong s) := by
  unfold Admissible
  infer_instance















end SensitivityHeadGainNumeric


