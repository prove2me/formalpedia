-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_Continuous
-- name    : NahmiasPerishable_Inventory_Continuous
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:28:13.096137+00:00
-- url     : https://prove2.me/theorems/e941333b-3773-4f8b-9acd-091ab1ba8472
-- title:
--   Perishable inventory: Continuous
-- statement:
--   Nonanticipating continuous-time integer replenishment with FIFO service, physical stock, purchases/setup/holding/disposal and sales, average net cost, and Poisson regenerative cycle quantities. The imported Poisson definition supplies only the counting process, not inventory assumptions.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 687–688, DOI:10.1287/opre.30.4.680.

import Definitions.Def_NahmiasPerishable_Inventory_Decay
import Definitions.Def_RankBasedSDI_LoadBalancing_PoissonProcess

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section

namespace NahmiasPerishable.Inventory
attribute [local instance] Classical.propDecidable

structure WeissParams where
  rate : ℝ
  life : ℝ
  K : ℝ
  c : ℝ
  h : ℝ
  revenue : ℝ
  disposal : ℝ

def ValidWeiss (P : WeissParams) : Prop :=
  0 < P.rate ∧ 0 < P.life ∧ 0 < P.K ∧ 0 ≤ P.c ∧ 0 < P.h ∧
    0 ≤ P.revenue ∧ 0 ≤ P.disposal

/-- Arrival number j+1 of the actual counting process; +∞ if it never occurs. -/
def arrival {Ω : Type*} (N : Ω → ℝ → ℝ) (j : ℕ) (ω : Ω) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' {t | 0 ≤ t ∧ (j+1 : ℕ) ≤ N ω t})

/-- Order epochs and quantities, together with the service record determined by FIFO.
No zero-stock restriction is imposed here. -/
structure ContinuousPolicy (Ω : Type*) where
  time : ℕ → Ω → EReal
  size : ℕ → Ω → ℕ
  served : ℕ → Ω → Option ℕ

def usedBefore {Ω : Type*} (π : ContinuousPolicy Ω) (i j : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range j).filter (fun l => π.served l ω = some i)).card

def available {Ω : Type*} (N : Ω → ℝ → ℝ) (life : ℝ)
    (π : ContinuousPolicy Ω) (ω : Ω) (j i : ℕ) : Prop :=
  π.time i ω < arrival N j ω ∧ arrival N j ω < π.time i ω + (life : EReal) ∧
    usedBefore π i j ω < π.size i ω

def usedBy {Ω : Type*} (N : Ω → ℝ → ℝ) (π : ContinuousPolicy Ω)
    (ω : Ω) (i : ℕ) (T : ℝ) : ℕ :=
  {j | arrival N j ω ≤ (T : EReal) ∧ π.served j ω = some i}.ncard

/-- Physical on-hand stock after all events at T (or just before orders at T). -/
def continuousStock {Ω : Type*} (N : Ω → ℝ → ℝ) (life : ℝ)
    (π : ContinuousPolicy Ω) (beforeOrders : Bool) (ω : Ω) (T : ℝ) : ℝ≥0∞ :=
  ∑' i : ℕ, if (if beforeOrders then π.time i ω < (T : EReal) else π.time i ω ≤ (T : EReal)) ∧
      (T : EReal) < π.time i ω + (life : EReal)
    then ((π.size i ω - usedBy N π ω i T : ℕ) : ℝ≥0∞) else 0

/-- Nonanticipation, locally finite positive orders, and work-conserving FIFO sales.
Demand at an order epoch is served before the new delivery. Unsatisfied demand is lost. -/
def AdmissibleContinuous {Ω : Type*} [MeasurableSpace Ω] (N : Ω → ℝ → ℝ)
    (life : ℝ) (π : ContinuousPolicy Ω) : Prop :=
  (∀ i, Measurable (π.time i) ∧ Measurable (π.size i) ∧
    ∀ j, MeasurableSet {ω | π.served i ω = some j}) ∧
  (∀ ω i, 0 ≤ π.time i ω ∧ (π.time i ω < ⊤ → 0 < π.size i ω)) ∧
  (∀ ω i j, i < j → π.time j ω < ⊤ → π.time i ω < π.time j ω) ∧
  (∀ (ω : Ω) (T : ℝ), {i | π.time i ω ≤ (T : EReal)}.Finite) ∧
  (∀ (T : ℝ) (ω ω' : Ω), 0 ≤ T →
    (∀ t ∈ Icc (0 : ℝ) T, N ω t = N ω' t) →
    ∀ i, (π.time i ω ≤ (T : EReal) ↔ π.time i ω' ≤ (T : EReal)) ∧
      (π.time i ω ≤ (T : EReal) → π.time i ω = π.time i ω' ∧ π.size i ω = π.size i ω')) ∧
  (∀ ω j, match π.served j ω with
    | none => ∀ i, ¬available N life π ω j i
    | some i => available N life π ω j i ∧
        ∀ l, available N life π ω j l → π.time i ω ≤ π.time l ω)

/-- Net operational cost up to time T: purchases, setups, holding, expirations, less actual sales. -/
def continuousCost {Ω : Type*} (N : Ω → ℝ → ℝ) (P : WeissParams)
    (π : ContinuousPolicy Ω) (ω : Ω) (T : ℝ) : EReal :=
  let purchases : ℝ≥0∞ := ∑' i : ℕ, if π.time i ω ≤ (T : EReal)
    then ENNReal.ofReal (P.K+P.c*π.size i ω) else 0
  let holding : ℝ≥0∞ := ENNReal.ofReal P.h *
    ∫⁻ t in Icc (0 : ℝ) T, continuousStock N P.life π false ω t
  let expired : ℝ≥0∞ := ∑' i : ℕ, if π.time i ω + (P.life : EReal) ≤ (T : EReal)
    then ((π.size i ω - usedBy N π ω i ((π.time i ω).toReal+P.life) : ℕ) : ℝ≥0∞) else 0
  let sales : ℕ := {j | arrival N j ω ≤ (T : EReal) ∧ (π.served j ω).isSome}.ncard
  (purchases+holding+ENNReal.ofReal P.disposal*expired).toEReal - (P.revenue*sales : ℝ)

def continuousAverage {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℝ → ℝ) (P : WeissParams) (π : ContinuousPolicy Ω) : EReal :=
  limsup (fun T : ℝ => (1/T : ℝ) * expectation μ (fun ω => continuousCost N P π ω T)) atTop

/-- Poisson point probabilities, used only at nonnegative time and positive intensity. -/
def poissonProb (rate t : ℝ) (j : ℕ) : ℝ := Real.exp (-rate*t)*(rate*t)^j/(j.factorial : ℝ)

def poissonLeft (rate t : ℝ) (S : ℕ) : ℝ :=
  ∑ j ∈ Finset.range S, ((S-j : ℕ) : ℝ)*poissonProb rate t j

def weissCycleTime (P : WeissParams) (S : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..P.life, ∑ j ∈ Finset.range S, poissonProb P.rate t j

/-- Regenerative cost E[cycle cost]/E[cycle length], with the actual Poisson finite sums. -/
def weissCost (P : WeissParams) (S : ℕ) : ℝ :=
  (P.K+P.c*S + P.h*(∫ t in (0 : ℝ)..P.life, poissonLeft P.rate t S) +
    P.disposal*poissonLeft P.rate P.life S - P.revenue*(S-poissonLeft P.rate P.life S)) /
      weissCycleTime P S

def weissOptima (P : WeissParams) : Set ℕ :=
  {S | 0 < S ∧ ∀ R, 0 < R → weissCost P S ≤ weissCost P R}

/-- The four combinations exactly as printed, including products with holding cost. -/
def weissParameters (P : WeissParams) : Fin 4 → ℝ :=
  ![P.rate*P.K/P.h, P.rate*(P.c-P.revenue)*P.h, P.rate*P.life,
    P.rate*(P.disposal+P.revenue)*P.h]

end NahmiasPerishable.Inventory


