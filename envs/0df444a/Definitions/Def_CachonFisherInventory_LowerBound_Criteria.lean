-- Prove2me | Definitions.Def_CachonFisherInventory_LowerBound_Criteria
-- name    : CachonFisherInventory_LowerBound_Criteria
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T02:49:37.484423+00:00
-- url     : https://prove2.me/theorems/25643927-6d2c-46fb-98b7-52b4151c5a63
-- title:
--   Physical optimization and stationary charge accounting
-- statement:
--   For each physical initial state s, the physical value is the infimum over all feasible causal physical trajectory laws starting at s of limsup_{T→∞}(T+1)⁻¹ Σ_{t=0}^T E[C_t]. Actual costs C_t are evaluated on the end-of-period states and integrated nonnegatively. Costs may be infinite. The paper's min is read as an infimum; this definition does not assert that a minimizing policy exists.
--
--   For equation (5) only, a stationary physical law means a feasible causal law, potentially with random initial state, for which the joint law of beginning state, current action, and current demand is identical at every time. The map defining that joint law is required to be measurable. This is stationarity of the controlled process, not merely stationarity of consumer demands. The goal's policy class has no stationarity condition. Supplier and retailer charges are evaluated at the pre-demand physical echelon inventory and inventory positions, with the exact formulas of §5.1.
-- source:
--   Cachon and Fisher (2000), Supply Chain Inventory Management and the Value of Shared Information, Management Science 46(8), DOI 10.1287/mnsc.46.8.1032.12029, §5.1, equation (5), p. 1039 (PDF p. 8); §5.2 lower-bound display, p. 1040 (PDF p. 9)

import Definitions.Def_CachonFisherInventory_LowerBound_Relaxation

open MeasureTheory

namespace CachonFisherInventory.LowerBound

noncomputable def physicalAverage (P : Parameters) (μ : Measure (PhysicalTrace P)) : EReal :=
  averageValue (fun t => nonnegExpectation μ (fun w => actualCost P (physicalState P w (t + 1))))

noncomputable def physicalValue (P : Parameters) (s : Stock P) : EReal :=
  sInf {v | ∃ μ : Measure (PhysicalTrace P), PhysicalLaw P μ ∧
    (∀ᵐ w ∂μ, w.1 = s) ∧ v = physicalAverage P μ}

/-- Full stationary joint state/action/demand law, used only for equation (5). -/
def StationaryPhysicalLaw (P : Parameters) (μ : Measure (PhysicalTrace P)) : Prop :=
  PhysicalLaw P μ ∧ ∀ t : ℕ,
    Measurable (fun w : PhysicalTrace P => (physicalState P w t, w.2 t)) ∧
    μ.map (fun w => (physicalState P w t, w.2 t)) =
      μ.map (fun w => (physicalState P w 0, w.2 0))

noncomputable def physicalSupplierCharge (P : Parameters) (R : ℤ)
    (w : PhysicalTrace P) (t : ℕ) : ℝ :=
  supplierCharge P (echelon P (preState P w t))
    (inventoryPosition P (preState P w t)) R

noncomputable def physicalRetailerCharge (P : Parameters) (R : ℤ)
    (w : PhysicalTrace P) (t : ℕ) (i : Fin P.N) : ℝ :=
  retailerCharge P (inventoryPosition P (preState P w t) i) R

end CachonFisherInventory.LowerBound


