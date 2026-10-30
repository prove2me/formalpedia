-- Prove2me | Definitions.Def_CachonFisherInventory_LowerBound_Physical
-- name    : CachonFisherInventory_LowerBound_Physical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T02:47:59.636415+00:00
-- url     : https://prove2.me/theorems/06429292-e01e-4730-893d-9a6873f32555
-- title:
--   Physical inventory, shipment dynamics, and feasible information policies
-- statement:
--   A beginning-of-period state records supplier on-hand stock in Q_r-batches; each retailer's integer net on-hand inventory in units; each retailer's unshipped batch orders; a supplier pipeline in Q_s-lots; and one shipment pipeline in Q_r-batches per retailer. All stocks and orders except net inventory are nonnegative integers. Arbitrary finite state values are allowed, with no inventory truncation. On-hand stock and customer backlog are respectively the positive and negative parts of net inventory, so simultaneous positive stock and backlog cannot be chosen independently.
--
--   Actions specify retailer orders in batches, supplier orders in Q_s-lots, and nonnegative batch releases to each retailer. Releases cannot exceed that retailer's outstanding orders plus new orders, and total releases cannot exceed supplier stock plus current arrivals. Partial fulfillment is allowed. Retailer orders precede supplier orders; all orders, receipts, and releases precede current consumer demand. The transition first receives and releases stock, shifts both pipelines, and reduces outstanding orders. It then subtracts demand from retailer net inventories. Stock cannot be transferred laterally. Natural subtraction is used only for physical quantities whose subtrahend is bounded by the feasibility constraints; backlog subtraction is in the integers.
--
--   A retailer's inventory position IP_i is net inventory plus its downstream in-transit units, excluding unshipped orders. Echelon inventory IL_s is Q_r times supplier stock plus the sum of these positions. Actual end-of-period cost is equation (3): h_s Q_r I_s + Σ_i[h_s IT_i+(h_s+h_r)I_i+p_r B_i]. It is not defined by the charge decomposition. A feasible physical law is causal and almost surely obeys these transitions and constraints, with every finite prefix of customer demand, including initial backlog, eventually covered by arrivals. Decisions can depend on the entire pre-demand information history and can randomize. Policies with traditional information are included in this full-information comparison class. No iid assumption is made about retailer orders.
-- source:
--   Cachon and Fisher (2000), Supply Chain Inventory Management and the Value of Shared Information, Management Science 46(8), DOI 10.1287/mnsc.46.8.1032.12029, §3, pp. 1034–1035 (PDF pp. 3–4); §5.1, equations (3)–(4), p. 1039 (PDF p. 8)

import Definitions.Def_CachonFisherInventory_LowerBound_CausalLaw
import Definitions.Def_CachonFisherInventory_LowerBound_Parameters

open MeasureTheory

namespace CachonFisherInventory.LowerBound

/-- Stock, retailer net inventories, unshipped orders, and both pipelines, at period start.
Supplier stock, retailer pipeline and unshipped orders are in batches; supplier pipeline
entries are Qs-lots; net inventories are units. -/
abbrev Stock (P : Parameters) :=
  ℕ × (Fin P.N → ℤ) × (Fin P.N → ℕ) ×
    (Fin P.Ls → ℕ) × (Fin P.N → Fin P.Lr → ℕ)

def supplierStock {P : Parameters} (s : Stock P) := s.1
def retailerNet {P : Parameters} (s : Stock P) := s.2.1
def unshipped {P : Parameters} (s : Stock P) := s.2.2.1
def supplierPipe {P : Parameters} (s : Stock P) := s.2.2.2.1
def retailerPipe {P : Parameters} (s : Stock P) := s.2.2.2.2

/-- Retailer batch orders, supplier Qs-lot order, and retailer batch releases. -/
abbrev PhysicalAction (P : Parameters) := (Fin P.N → ℕ) × ℕ × (Fin P.N → ℕ)

def retailOrders {P : Parameters} (a : PhysicalAction P) := a.1
def supplyOrder {P : Parameters} (a : PhysicalAction P) := a.2.1
def releases {P : Parameters} (a : PhysicalAction P) := a.2.2

def physicalFeasible (P : Parameters) (s : Stock P) (a : PhysicalAction P) : Prop :=
  (∀ i, releases a i ≤ unshipped s i + retailOrders a i) ∧
  (∑ i, releases a i) ≤ supplierStock s +
    P.Qs * pipeArrival (supplierPipe s) (supplyOrder a)

/-- State after receipts and releases, before demand; zero lead times arrive now. -/
def physicalPre (P : Parameters) (s : Stock P) (a : PhysicalAction P) : Stock P :=
  (supplierStock s + P.Qs * pipeArrival (supplierPipe s) (supplyOrder a) -
      ∑ i, releases a i,
   (fun i => retailerNet s i + (P.Qr *
      pipeArrival (retailerPipe s i) (releases a i) : ℕ)),
   (fun i => unshipped s i + retailOrders a i - releases a i),
   pipeShift (supplierPipe s) (supplyOrder a),
   fun i => pipeShift (retailerPipe s i) (releases a i))

def physicalNext (P : Parameters) (s : Stock P) (a : PhysicalAction P)
    (d : Demand P) : Stock P :=
  let v := physicalPre P s a
  (supplierStock v, (fun i => retailerNet v i - (d i).val),
    unshipped v, supplierPipe v, retailerPipe v)

def transitUnits (P : Parameters) (s : Stock P) (i : Fin P.N) : ℕ :=
  P.Qr * ∑ k, retailerPipe s i k

def inventoryPosition (P : Parameters) (s : Stock P) (i : Fin P.N) : ℤ :=
  retailerNet s i + transitUnits P s i

def echelon (P : Parameters) (s : Stock P) : ℤ :=
  (P.Qr * supplierStock s : ℕ) + ∑ i, inventoryPosition P s i

noncomputable def onHand {P : Parameters} (s : Stock P) (i : Fin P.N) : ℝ :=
  max (retailerNet s i : ℝ) 0

noncomputable def backlog {P : Parameters} (s : Stock P) (i : Fin P.N) : ℝ :=
  max (-(retailerNet s i : ℝ)) 0

/-- Equation (3), evaluated on an end-of-period physical state. -/
noncomputable def actualCost (P : Parameters) (s : Stock P) : ℝ :=
  P.hs * P.Qr * supplierStock s +
    ∑ i, (P.hs * transitUnits P s i + (P.hs + P.hr) * onHand s i + P.pr * backlog s i)

abbrev PhysicalTrace (P : Parameters) := ControlTrace (Stock P) (PhysicalAction P) (Demand P)

def physicalState (P : Parameters) (w : PhysicalTrace P) (t : ℕ) : Stock P :=
  controlledState (physicalNext P) w t

def preState (P : Parameters) (w : PhysicalTrace P) (t : ℕ) : Stock P :=
  physicalPre P (physicalState P w t) (w.2 t).1

/-- Every finite prefix of customer demand, including any initial backlog, is eventually filled.
FIFO service of backlogs is implicit in the net-inventory representation. -/
def eventuallyFilled (P : Parameters) (w : PhysicalTrace P) : Prop :=
  ∀ t i, ∃ T, t ≤ T ∧
    (∑ k ∈ Finset.range t, ((w.2 k).2 i).val : ℕ) ≤
      retailerNet w.1 i + ∑ k ∈ Finset.range T,
        (P.Qr * pipeArrival (retailerPipe (physicalState P w k) i)
          (releases (w.2 k).1 i) : ℕ)

/-- Full-information feasible laws; all decisions precede the current demand.
Any policy using only traditional information belongs to this comparison class. -/
def PhysicalLaw (P : Parameters) (μ : Measure (PhysicalTrace P)) : Prop :=
  CausalLaw (demandLaw P) μ ∧
  (∀ᵐ w ∂μ, (∀ t, physicalFeasible P (physicalState P w t) (w.2 t).1) ∧
    eventuallyFilled P w)

end CachonFisherInventory.LowerBound


