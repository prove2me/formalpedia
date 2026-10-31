-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_Stationary
-- name    : NahmiasPerishable_Inventory_Stationary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:02.191261+00:00
-- url     : https://prove2.me/theorems/b93d0257-3e97-48a4-8801-96b5fadadea7
-- title:
--   Perishable inventory: Stationary
-- statement:
--   Actual base-stock FIFO paths from arbitrary canonical initial states, observed stock-decrease lags, invariant age laws and physical outdating, countable discrete demand, the printed bounds, packed fixed-order stock, and explicit general-state Markov/recurrence predicates.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 689–690, DOI:10.1287/opre.30.4.680.

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section

namespace NahmiasPerishable.Inventory

/-- Invariant law of a measurable state update driven by an independent shock. -/
def ShockInvariant {X : Type*} [MeasurableSpace X] (μ : Measure ℝ)
    (step : X → ℝ → X) (ν : Measure X) : Prop :=
  IsProbabilityMeasure ν ∧ (ν.prod μ).map (fun xd => step xd.1 xd.2) = ν

def shockPath {X : Type*} (step : X → ℝ → X) (x : X) (d : ℕ → ℝ) : ℕ → X
  | 0 => x
  | n+1 => step (shockPath step x d n) (d n)

/-- First positive return time, with infinity when no return occurs. -/
def firstReturn {X : Type*} (step : X → ℝ → X) (B : Set X)
    (x : X) (d : ℕ → ℝ) : ℝ≥0∞ :=
  sInf ((fun n : ℕ => (n : ℝ≥0∞)) '' {n | 0 < n ∧ shockPath step x d n ∈ B})

/-- Positive recurrence in the stationary return-time sense. The invariant probability
is concluded, not supplied; no irreducibility or common recurrent class is assumed.
For a positive-mass measurable set, the return time from its stationary conditional
law has finite mean (the unnormalized integral is finite exactly when that mean is). -/
def PositiveRecurrent {X : Type*} [MeasurableSpace X] (D : Demand)
    (step : X → ℝ → X) (space : Set X) : Prop :=
  ∃ ν : Measure X, ShockInvariant D.law step ν ∧ ν space = 1 ∧
    ∀ B : Set X, MeasurableSet B → 0 < ν B →
      (∫⁻ xd in {xd : X × (ℕ → ℝ) | xd.1 ∈ B}, firstReturn step B xd.1 xd.2
        ∂ν.prod (Measure.infinitePi (fun _ : ℕ => D.law))) < ⊤

/-- Fixed order-up-to level, FIFO, and full backlog retention. -/
def baseStep (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) : AgeState k :=
  fifo true x (pos (S-total x)) d

def basePath (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℕ → ℝ) : ℕ → AgeState k :=
  shockPath (baseStep k S) x d

def baseExpired (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℝ) : ℝ :=
  if k = 0 then pos (pos (S-total x)-x.2-d) else expires x d

def stockDecrease (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℕ → ℝ) (t : ℕ) : ℝ :=
  d t + baseExpired k S (basePath k S x d t) (d t)

/-- The observed lag vector, after k actual periods have elapsed. -/
def lagVector (k : ℕ) (S : ℝ) (x : AgeState k) (d : ℕ → ℝ) (t : ℕ) : Fin k → ℝ :=
  fun i => stockDecrease k S x d (t+i.val)

def lagStep (k : ℕ) (S : ℝ) (a : Fin k → ℝ) (d : ℝ) : Fin k → ℝ :=
  fun i => if hi : i.val+1 < k then a ⟨i.val+1,hi⟩ else max d (S-∑ j, a j)

def StationaryStock (μ : Measure ℝ) (k : ℕ) (S : ℝ) (ν : Measure (AgeState k)) : Prop :=
  ShockInvariant μ (baseStep k S) ν ∧
    ν {x | canonical true x ∧ total x ≤ S} = 1

/-- Stationary expected expiration is computed from physical expired units. -/
def stationaryOutdate (μ : Measure ℝ) (k : ℕ) (S : ℝ) (ν : Measure (AgeState k)) : ℝ :=
  ∫ xd, baseExpired k S xd.1 xd.2 ∂ν.prod μ

/-- A common rate for the invariant laws of the actual age process; existence is part of this predicate. -/
def IsStationaryRate (μ : Measure ℝ) (k : ℕ) (S r : ℝ) : Prop :=
  (∃ ν, StationaryStock μ k S ν) ∧
    ∀ ν, StationaryStock μ k S ν → stationaryOutdate μ k S ν = r

/-- Countably supported demand, without an integer grid or a finite-support restriction. -/
def DiscreteDemand (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ d ∂μ, 0 ≤ d) ∧ ∃ A : Set ℝ, A.Countable ∧ μ A = 1

/-- The two printed Chazan–Gal bounds. -/
def lowerPrinted (μ : Measure ℝ) (m : ℕ) (S : ℝ) : ℝ :=
  S/m - ∫ d, min d (S/m) ∂μ

def upperPrinted (μ : Measure ℝ) (m : ℕ) (S : ℝ) : ℝ :=
  S/m - ∫ d, min ((∑ i : Fin m, d i)/m) (S/m) ∂demandPaths μ m

/-- Packed oldest-first coordinates reconstructed from total end stock. -/
def packedStock (k : ℕ) (q Y : ℝ) : Fin k → ℝ :=
  fun i => min q (pos (Y - ((k-1-i.val : ℕ) : ℝ)*q))

def constantStep (k : ℕ) (q : ℝ) (Y d : ℝ) : ℝ :=
  total (fifo false (packedStock k q Y,0) q d)

/-- Markov property by the joint-law factorization against every measurable history event. -/
def MarkovFromShocks {X : Type*} [MeasurableSpace X] (μ : Measure ℝ)
    (Y : (ℕ → ℝ) → ℕ → X) (step : X → ℝ → X) : Prop :=
  ∀ n (H : Set (Fin (n+1) → X)) (B : Set X), MeasurableSet H → MeasurableSet B →
    (Measure.infinitePi (fun _ : ℕ => μ))
      {d | (fun i : Fin (n+1) => Y d i.val) ∈ H ∧ Y d (n+1) ∈ B} =
    ∫⁻ d in {d | (fun i : Fin (n+1) => Y d i.val) ∈ H},
      μ {z | step (Y d n) z ∈ B} ∂Measure.infinitePi (fun _ : ℕ => μ)

end NahmiasPerishable.Inventory


