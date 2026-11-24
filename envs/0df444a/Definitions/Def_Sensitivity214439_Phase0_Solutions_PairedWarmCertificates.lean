-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_PairedWarmCertificates
-- name    : Sensitivity214439_Phase0_Solutions_PairedWarmCertificates
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:33:07.267026+00:00
-- url     : https://prove2.me/theorems/618f66ee-c98d-4c77-adc1-e843f6e50e1b
-- title:
--   Finite certificates for paired warm head prices
-- statement:
--   The worst own-target fee is the maximum over the two possible orientations of the child colors. A warm head's kind is $0$ when it has no hard-active guard and $4$ otherwise.
--
--   Given a list of guard fees, warm validity requires their sum plus the worst own fee to be at most the prescribed-row bound. Each hard guard fee must also fit its height-indexed external loss price. If both children pass the hard cutoff and the total fee is positive, the certificate requires at most one hard failure, an enabled head-kind mask bit, and three high-head coefficient bounds: the own-plus-soft fee, that fee plus the larger of the two child loss prices, and that fee plus both child loss prices.
--
--   The fast predicate supplies each guard fee from the closed-form accepted-height cutoff. A certificate at a fixed left height checks both color-match flags, every right height in $0,\ldots,12$, and every occupied guard list of length at most two above the destination soft cutoff, whenever the old weak state is rejected.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/PairedWarmCertificates.lean lines 8–124; SHA256 4a230abb73ff01d28278738287a742f0ae9e2d3f05a48226184f083a9fd4457f; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HeadGainFast
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HeadGainLocalFees
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HeadGainNumericCore
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Range

namespace SensitivityHeadGainNumeric
end SensitivityHeadGainNumeric



/-! Finite certificates for paired warm C, external guard prices, and the
three incoming-mark prices of each operative high-head kind. -/
namespace SensitivityHeadGainNumeric

def ownWorst (r : Recipe) (values : SensitivityLocalNumeric.Bounds)
    (rise fall : ℕ → ℕ → ℕ) (strong : Fin 12) (s : State) : ℕ :=
  max (ownFee r values rise fall strong s false) (ownFee r values rise fall strong s true)



def warmKind (r : Recipe) (strong : Fin 12) (s : State) : ℕ :=
  if count s (r.hard strong) = 0 then 0 else 4

def WarmValidWith (r : Recipe) (values : SensitivityLocalNumeric.Bounds)
    (rise fall : ℕ → ℕ → ℕ) (strong : Fin 12) (single mask : ℕ) (ed cf : Array ℕ)
    (s : State) (fees : List ℕ) : Prop :=
  let own := ownWorst r values rise fall strong s
  let total := own + fees.sum
  let soft := ((s.guards.zip fees).map fun pair => if pair.1 ≤ r.hard strong then pair.2 else 0).sum
  total ≤ single ∧
    ((s.guards.zip fees).all fun pair =>
      decide (r.hard strong < pair.1 → pair.2 ≤ ed[pair.1-1]?.getD 0)) = true ∧
    (r.hard strong < min s.left s.right → 0 < total →
      count s (r.hard strong) ≤ 1 ∧ mask.testBit (warmKind r strong s) = true ∧
        own + soft ≤ cf[3*warmKind r strong s]?.getD 0 ∧
        own + soft + max (ed[s.left-1]?.getD 0) (ed[s.right-1]?.getD 0) ≤
          cf[3*warmKind r strong s+1]?.getD 0 ∧
        own + soft + ed[s.left-1]?.getD 0 + ed[s.right-1]?.getD 0 ≤
          cf[3*warmKind r strong s+2]?.getD 0)

instance (r : Recipe) (values : SensitivityLocalNumeric.Bounds)
    (rise fall : ℕ → ℕ → ℕ) (strong : Fin 12) (single mask : ℕ) (ed cf : Array ℕ)
    (s : State) (fees : List ℕ) :
    Decidable (WarmValidWith r values rise fall strong single mask ed cf s fees) := by
  unfold WarmValidWith
  infer_instance



def WarmValidFast (r : Recipe) (values : SensitivityLocalNumeric.Bounds)
    (rise fall : ℕ → ℕ → ℕ) (weak strong : Fin 12) (single mask : ℕ) (ed cf : Array ℕ)
    (s : State) : Prop :=
  WarmValidWith r values rise fall strong single mask ed cf s
    (s.guards.map (guardFeeFast r values.profile weak strong s))

instance (r : Recipe) (values : SensitivityLocalNumeric.Bounds)
    (rise fall : ℕ → ℕ → ℕ) (weak strong : Fin 12) (single mask : ℕ) (ed cf : Array ℕ)
    (s : State) : Decidable (WarmValidFast r values rise fall weak strong single mask ed cf s) := by
  unfold WarmValidFast
  infer_instance



def warmHeights (r : Recipe) (strong : Fin 12) : List ℕ :=
  (List.range 13).filter fun h => decide (r.soft strong < h)

def warmGuardLists (r : Recipe) (strong : Fin 12) : List (List ℕ) :=
  [] :: ((warmHeights r strong).map (fun h => [h]) ++
    (warmHeights r strong).flatMap (fun a => (warmHeights r strong).map (fun b => [a,b])))



def WarmCertifiedAt (r : Recipe) (values : SensitivityLocalNumeric.Bounds)
    (rise fall : ℕ → ℕ → ℕ) (weak strong : Fin 12) (single mask : ℕ) (ed cf : Array ℕ)
    (left : Fin 13) : Prop :=
  ∀ (right : Fin 13) (same : Bool),
    ((warmGuardLists r strong).all fun guards =>
      decide (¬ accepts r weak ⟨left.val,right.val,same,guards⟩ →
        WarmValidFast r values rise fall weak strong single mask ed cf
          ⟨left.val,right.val,same,guards⟩)) = true

instance (r : Recipe) (values : SensitivityLocalNumeric.Bounds)
    (rise fall : ℕ → ℕ → ℕ) (weak strong : Fin 12) (single mask : ℕ) (ed cf : Array ℕ)
    (left : Fin 13) :
    Decidable (WarmCertifiedAt r values rise fall weak strong single mask ed cf left) := by
  unfold WarmCertifiedAt
  infer_instance






end SensitivityHeadGainNumeric


