-- Prove2me | Definitions.Def_PerishShip_Waste_Model
-- name    : PerishShip_Waste_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:14.789981+00:00
-- url     : https://prove2.me/theorems/62f022ea-6c5d-436e-a1ed-0f0586a7c019
-- title:
--   §4.1–§4.2.1, pp. 10–15 — two-echelon perishable shipment model and waste criteria
-- statement:
--   A product has a fixed shelf life of $N$ periods. Before each warehouse shipment, a plant replenishes age-zero stock so the warehouse holds $S^W$ units. The store has shelf capacity $L$. The vectors $x_i$ and $y_i$ record the units of age $i$ at the warehouse and store at the start of a period; $q_i$ records the units shipped from the warehouse, and $z_i=y_i+q_i$ is post-delivery store stock. A fraction $\gamma\in[0,1]$ of a shopper population of size $\lambda$ selects units oldest first, and the remaining shoppers select youngest first. The module defines the paper's demand reaching each age, balance equations, warehouse and store waste, feasible states and shipments, and shipping-oldest-first (SOF) shipments.
--
--   $$
--   x^{\mathrm{post}}_0=S^W-\sum_{i=1}^{N-1}x_i,\qquad
--   D_i=(\lceil\gamma\lambda\rceil-\sum_{j>i}z_j)^+ +(\lambda-\lceil\gamma\lambda\rceil-\sum_{j<i}z_j)^+,\qquad
--   W^W=x^{\mathrm{post}}_{N-1}-q_{N-1},\quad W^R=(z_{N-1}-D_{N-1})^+.
--   $$
--
--   A shipment is SOF when any younger unit is shipped only after every older available unit has been shipped. The SOF-in-full rule ships as many units as shelf space and warehouse stock allow. The state-law and long-run cost definitions specialize the accompanying general controlled-process layer.
--
--   **Formalization Note** Ages are indexed by $0,\ldots,N-1$; start-of-period age-zero stocks are zero. Natural-number subtraction implements $(\cdot)^+$. The post-replenishment stock formula is used on feasible states. Only the oldest cohort expires. The paper's printed demand sums use $z_i$ where the summation index requires $z_j$; this definition uses $z_j$.
-- source:
--   Akkaş & Honhon, Shipment policies for products with fixed shelf lives: impact on profits and waste, SSRN 3247290 (manuscript of 2021-03-20), pp. 10–15 (PDF 10–15), §4.1, §4.2, §4.2.1

import Mathlib
import Definitions.Def_PerishShip_Waste_AverageMDP

namespace PerishShip.Waste

/-- Parameters of the warehouse-to-store system of §4.1. -/
structure Params where
  N : ℕ
  SW : ℕ
  L : ℕ
  γ : ℝ
  demand : PMF ℕ

def Params.Standing (P : Params) : Prop := 1 ≤ P.N ∧ 0 ≤ P.γ ∧ P.γ ≤ 1

abbrev Vec (P : Params) := Fin P.N → ℕ

/-- Inventory before the plant replenishment and before the warehouse shipment. -/
structure State (P : Params) where
  x : Vec P
  y : Vec P
  deriving Countable

def State.Feasible {P : Params} (s : State P) : Prop :=
  (∀ i : Fin P.N, i.val = 0 → s.x i = 0 ∧ s.y i = 0) ∧
    (∑ i, s.x i) ≤ P.SW ∧ (∑ i, s.y i) ≤ P.L

/-- Warehouse stock after replenishing age zero to the order-up-to level. -/
def xbar {P : Params} (s : State P) : Vec P :=
  fun i => if i.val = 0 then P.SW - ∑ j, s.x j else s.x i

def ShipFeasible {P : Params} (s : State P) (q : Vec P) : Prop :=
  (∀ i, q i ≤ xbar s i) ∧ (∑ i, q i) + (∑ i, s.y i) ≤ P.L

/-- Post-delivery store stock. -/
def z {P : Params} (s : State P) (q : Vec P) : Vec P := fun i => s.y i + q i

/-- Number of FIFO shoppers; the remaining shoppers use LIFO. -/
noncomputable def fifo (P : Params) (lam : ℕ) : ℕ := Nat.ceil (P.γ * (lam : ℝ))
noncomputable def lifo (P : Params) (lam : ℕ) : ℕ := lam - fifo P lam

/-- The paper's age-specific demand formula, with its summation subscript corrected. -/
noncomputable def D {P : Params} (s : State P) (q : Vec P) (lam : ℕ)
    (i : Fin P.N) : ℕ :=
  (fifo P lam - ∑ j ∈ Finset.Ioi i, z s q j) +
    (lifo P lam - ∑ j ∈ Finset.Iio i, z s q j)

noncomputable def left {P : Params} (s : State P) (q : Vec P) (lam : ℕ) : Vec P :=
  fun i => z s q i - D s q lam i

/-- The oldest age, defined under the shelf-life assumption. -/
def old (P : Params) (hN : 1 ≤ P.N) : Fin P.N := ⟨P.N - 1, by omega⟩

/-- Warehouse waste, from the only age cohort that expires this period. -/
def ww {P : Params} (hN : 1 ≤ P.N) (s : State P) (q : Vec P) : ℕ :=
  xbar s (old P hN) - q (old P hN)

/-- Retail waste, from the same age cohort after demand. -/
noncomputable def wr {P : Params} (hN : 1 ≤ P.N) (s : State P)
    (q : Vec P) (lam : ℕ) : ℕ := left s q lam (old P hN)

noncomputable def wtot {P : Params} (hN : 1 ≤ P.N) (s : State P)
    (q : Vec P) (lam : ℕ) : ℕ := ww hN s q + wr hN s q lam

/-- Ages nonexpired stock by one period, discarding the final age cohort. -/
def ageShift {P : Params} (f : Vec P) : Vec P :=
  fun i => if h : i.val = 0 then 0 else f ⟨i.val - 1, by omega⟩

/-- The §4.1 balance equations. -/
noncomputable def next {P : Params} (s : State P) (q : Vec P) (lam : ℕ) : State P :=
  ⟨ageShift (fun i => xbar s i - q i), ageShift (left s q lam)⟩

abbrev Policy (P : Params) := MarkovPolicy (State P) (Vec P)

def Policy.Admissible {P : Params} (σ : Policy P) : Prop :=
  ∀ t s, s.Feasible → ShipFeasible s (σ t s)

/-- A shipment follows the paper's oldest-first issuing order. -/
def IsSOF {P : Params} (s : State P) (q : Vec P) : Prop :=
  ∀ i j : Fin P.N, i < j → 0 < q i → q j = xbar s j

/-- The maximum total quantity allowed at a feasible state. -/
def shipTotal {P : Params} (s : State P) : ℕ :=
  min (P.L - ∑ i, s.y i) P.SW

/-- Fill the store, or exhaust the warehouse, shipping oldest cohorts first. -/
def sofFull {P : Params} (s : State P) : Vec P :=
  fun i => min (xbar s i) (shipTotal s - ∑ j ∈ Finset.Ioi i, xbar s j)

def stationary {P : Params} (f : State P → Vec P) : Policy P := fun _ => f

/-- The state distribution induced by the paper's shopper-population law. -/
noncomputable def stateLaw {P : Params} (σ : Policy P) (s₀ : State P) : ℕ → PMF (State P) :=
  controlledStateLaw P.demand next σ s₀

noncomputable def expCost {P : Params} (c : State P → Vec P → ℕ → ℕ)
    (σ : Policy P) (s₀ : State P) (t : ℕ) : ENNReal :=
  controlledExpectedCost P.demand next (fun s q lam => (c s q lam : ENNReal)) σ s₀ t

noncomputable def cesaro {P : Params} (c : State P → Vec P → ℕ → ℕ)
    (σ : Policy P) (s₀ : State P) (T : ℕ) : ENNReal :=
  controlledCesaro P.demand next (fun s q lam => (c s q lam : ENNReal)) σ s₀ T

noncomputable def avgUpper {P : Params} (c : State P → Vec P → ℕ → ℕ)
    (σ : Policy P) (s₀ : State P) : ENNReal :=
  controlledAvgUpper P.demand next (fun s q lam => (c s q lam : ENNReal)) σ s₀

noncomputable def avgLower {P : Params} (c : State P → Vec P → ℕ → ℕ)
    (σ : Policy P) (s₀ : State P) : ENNReal :=
  controlledAvgLower P.demand next (fun s q lam => (c s q lam : ENNReal)) σ s₀

end PerishShip.Waste


