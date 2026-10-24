-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P13
-- name    : QAlgorithms_Papers_Independent_Support50_P13
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T19:20:10.27798+00:00
-- url     : https://prove2.me/theorems/7dee71d6-277e-4bdb-ba80-380547a48178
-- title:
--   Definitions for Additivity for a class of unital qubit channels
-- statement:
--   The objects the formalized statements of *Additivity for a class of unital qubit channels* (arXiv:quant-ph/0103156) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ultimateCapacityNats`: PDF p.4, Remark 2: operational unassisted classical capacity, converted from bits to nats. The accepted code model allows arbitrary block input states and collective POVMs, and provides no prior sender-receiver entanglement.
--   - `normalizedHolevoRate`: PDF p.4, (8): normalized Holevo quantity of the actual n-use tensor channel. The n=0 extension is zero and is irrelevant to the ordinary limit at infinity.
-- source:
--   Additivity for a class of unital qubit channels, arXiv:quant-ph/0103156v2, https://arxiv.org/abs/quant-ph/0103156v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P42

/-!
King, arXiv:quant-ph/0103156v2, Additivity for unital qubit channels.
Page numbers are PDF pages. Entropies and classical capacities are in nats.
Imports are pinned accepted libraries. All new definitions are paper-local.
Theorem 2 is an exact specialization of the accepted phaseDampingPNormBound;
its reuse record is in items.json, so it has no duplicate theorem here.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Support50.P13

open QAlgorithms.Papers.Independent.Gap48.P03
  (productChannel maximumOutputPNorm holevoQuantity depolarizingNormFactor
    phaseChannel qubitPauli)
open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)
open QAlgorithms.Papers.Independent.Information100.P63 (schatten)
open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Remark 2: operational unassisted classical capacity, converted from
bits to nats. The accepted code model allows arbitrary block input states and
collective POVMs, and provides no prior sender-receiver entanglement. -/
def ultimateCapacityNats {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (Phi : Superop A B) : ℝ :=
  Real.log 2 * ordinaryClassicalCapacity Phi

/-- PDF p.4, (8): normalized Holevo quantity of the actual n-use tensor channel.
The n=0 extension is zero and is irrelevant to the ordinary limit at infinity. -/
def normalizedHolevoRate {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (Phi : Superop A B) (n : ℕ) : ℝ :=
  holevoQuantity (piSuperop (fun _ : Fin n => Phi)) / (n : ℝ)

/-- Converting the operational capacity back from nats recovers the bit value. -/
example {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (Phi : Superop A B) :
    ultimateCapacityNats Phi / Real.log 2 = ordinaryClassicalCapacity Phi := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold ultimateCapacityNats
  field_simp [hlog]

/-- The zero-length extension has the declared harmless value. -/
example {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (Phi : Superop A B) :
    normalizedHolevoRate Phi 0 = 0 := by
  simp [normalizedHolevoRate]

end QAlgorithms.Papers.Independent.Support50.P13


