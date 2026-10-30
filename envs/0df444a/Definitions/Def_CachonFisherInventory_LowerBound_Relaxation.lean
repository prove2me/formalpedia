-- Prove2me | Definitions.Def_CachonFisherInventory_LowerBound_Relaxation
-- name    : CachonFisherInventory_LowerBound_Relaxation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T02:48:40.966817+00:00
-- url     : https://prove2.me/theorems/7d4f0aaa-cf9d-4eb2-b7d1-0be6a7f41efd
-- title:
--   Location-relaxed dynamics and optimal expected supplier charges
-- statement:
--   A relaxed state records echelon units y, each retailer's inventory position IP_i, and the complete supplier order pipeline in Q_s-lots. Its initial state is the physical state's echelon inventory, inventory positions, and supplier pipeline. In each period a policy orders a nonnegative integer number of Q_s-lots and chooses a signed integer batch allocation β_i for each retailer. Supplier arrivals occur after L_s periods, including immediate arrival when L_s=0. Before demand, y is increased by arriving Q_s Q_r units and IP_i becomes IP_i^b+β_i Q_r. Feasibility requires Σ_i IP_i≤y. After demand, total demand is subtracted from y and individual demand from IP_i. The supplier pipeline is shifted explicitly; there is no cancellation or negative supplier order.
--
--   A relaxed law is causal with the same product demand law as the physical system, starts from the prescribed state, and satisfies the allocation constraint almost surely at all times. Every finite customer-demand prefix must eventually be covered by initial inventory positions plus cumulative signed allocations; the fixed downstream delay does not change this eventuality requirement. This is the signed-allocation counterpart of eventual filling, not a stability or finite-cost assumption. Outstanding retailer orders need no separate constraint here because retailer requests are freely chosen and allocations can be negative.
--
--   The relaxed supplier value C̲_s is the infimum over these laws of the limsup expected Cesàro supplier charges G_s. Each expectation uses the finite offset b(R) and a nonnegative integral; hence infinite costs remain +∞. Infima are taken in EReal, whose empty-set infimum is +∞ and unbounded-below infimum is −∞, rather than a default real zero. No per-period optimizer, base-stock rule, stationary restriction, or optimal-policy existence is assumed.
-- source:
--   Cachon and Fisher (2000), Supply Chain Inventory Management and the Value of Shared Information, Management Science 46(8), DOI 10.1287/mnsc.46.8.1032.12029, §5.2, p. 1040 (PDF p. 9), displayed allocation constraints and definition of C̲_s

import Definitions.Def_CachonFisherInventory_LowerBound_Physical
import Definitions.Def_CachonFisherInventory_LowerBound_Charges

open MeasureTheory

namespace CachonFisherInventory.LowerBound

/-- Echelon units, retailer inventory positions in units, supplier pipeline in Qs-lots. -/
abbrev RelaxedStock (P : Parameters) := ℤ × (Fin P.N → ℤ) × (Fin P.Ls → ℕ)

/-- Supplier orders in Qs-lots and signed retailer allocations in Qr-batches. -/
abbrev RelaxedAction (P : Parameters) := ℕ × (Fin P.N → ℤ)

def relaxedInitial (P : Parameters) (s : Stock P) : RelaxedStock P :=
  (echelon P s, inventoryPosition P s, supplierPipe s)

def relaxedPre (P : Parameters) (s : RelaxedStock P) (a : RelaxedAction P) :
    RelaxedStock P :=
  (s.1 + (P.Qr * P.Qs * pipeArrival s.2.2 a.1 : ℕ),
   (fun i => s.2.1 i + a.2 i * P.Qr), pipeShift s.2.2 a.1)

def relaxedFeasible (P : Parameters) (s : RelaxedStock P) (a : RelaxedAction P) : Prop :=
  let v := relaxedPre P s a
  (∑ i, v.2.1 i) ≤ v.1

def relaxedNext (P : Parameters) (s : RelaxedStock P) (a : RelaxedAction P)
    (d : Demand P) : RelaxedStock P :=
  let v := relaxedPre P s a
  (v.1 - ∑ i, ((d i).val : ℤ), (fun i => v.2.1 i - (d i).val), v.2.2)

abbrev RelaxedTrace (P : Parameters) :=
  ControlTrace (RelaxedStock P) (RelaxedAction P) (Demand P)

def relaxedState (P : Parameters) (w : RelaxedTrace P) (t : ℕ) : RelaxedStock P :=
  controlledState (relaxedNext P) w t

/-- Eventual fulfillment in the signed-allocation model. Initial inventory positions
already include the finite downstream pipeline; a fixed Lr delay does not change
eventuality. Every finite demand prefix is eventually covered by cumulative allocations. -/
def relaxedEventuallyFilled (P : Parameters) (w : RelaxedTrace P) : Prop :=
  ∀ t i, ∃ T, t ≤ T ∧
    (∑ k ∈ Finset.range t, (((w.2 k).2 i).val : ℤ)) ≤
      w.1.2.1 i + ∑ k ∈ Finset.range T, (w.2 k).1.2 i * P.Qr

def RelaxedLaw (P : Parameters) (s : RelaxedStock P)
    (μ : Measure (RelaxedTrace P)) : Prop :=
  CausalLaw (demandLaw P) μ ∧ (∀ᵐ w ∂μ, w.1 = s) ∧
    ∀ᵐ w ∂μ, (∀ t, relaxedFeasible P (relaxedState P w t) (w.2 t).1) ∧
      relaxedEventuallyFilled P w

noncomputable def relaxedPeriodCharge (P : Parameters) (R : ℤ)
    (w : RelaxedTrace P) (t : ℕ) : ℝ :=
  let v := relaxedPre P (relaxedState P w t) (w.2 t).1
  supplierCharge P v.1 v.2.1 R

noncomputable def relaxedAverage (P : Parameters) (R : ℤ)
    (μ : Measure (RelaxedTrace P)) : EReal :=
  averageValue (fun t => lowerExpectation μ (chargeFloor P R)
    (fun w => relaxedPeriodCharge P R w t))

/-- The genuine infinite-horizon location-relaxed supplier optimization. -/
noncomputable def supplierLowerValue (P : Parameters) (s : RelaxedStock P) (R : ℤ) : EReal :=
  sInf {v | ∃ μ : Measure (RelaxedTrace P), RelaxedLaw P s μ ∧ v = relaxedAverage P R μ}

end CachonFisherInventory.LowerBound


