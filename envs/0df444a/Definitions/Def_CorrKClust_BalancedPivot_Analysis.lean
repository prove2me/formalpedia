-- Prove2me | Definitions.Def_CorrKClust_BalancedPivot_Analysis
-- name    : CorrKClust_BalancedPivot_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:38.954818+00:00
-- url     : https://prove2.me/theorems/466abbb9-1066-4920-89f7-a9cb0b156343
-- title:
--   Stopping times, coverage, projected loads and the two merging events
-- statement:
--   For a fixed arrival order, $p_t(v)$ counts arrived members of the final pivot cluster founded by $v$, and $p_n(v)$ is its final size. The stopping time $T$ is just before pivot $k+1$ arrives, or $n$ if it never arrives; $T_0$ is the arrival time of pivot $k$, or $n$ if absent. A vertex is covered after $t$ if it has arrived or is adjacent to a pivot that arrived by $t$. Let $U$ be the set uncovered at $T$.
--
--   The projected load $P_b(t)$ of an output cluster sums final sizes only over pivots already assigned there by $t$. Current load counts only arrived vertices. For a nonempty comparison set $S$ of clusters present at $T$, put $\mu(S)=\max_{b\in S}P_b(T)$. The merging cost counts non-edges between distinct pivot clusters placed together; the base cost consists of negative pairs within pivot clusters and positive pairs separated by the output clustering.
--
--   Let $S_1$ be early pivot clusters with at most $2048\ln n$ vertices arrived at $T$, and set $L=2^{\lfloor\log_2 T\rfloor}$. The two events are
--   $$\mathcal L=\{T<n,\ |U|>512|S_1|n\ln n/L\},\quad\mathcal B=\{T<n,\ |U|\le512|S_1|n\ln n/L\}.$$
--   They cover exactly the orders with $T<n$. Finite maxima use the natural default zero on the empty set; the bound is applied only to nonempty comparison sets. All random times and sets remain functions of the order.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Definitions 7.2–7.3; §7.3.2; §7.3.4, pp. 28–42, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Algorithm
import Definitions.Def_CorrKClust_BalancedPivot_CliqueParameters

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- p_t(v): only arrived members of the final pivot cluster of v. -/
def pivotSize {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (σ : ArrivalOrder V) (t : ℕ) (v : V) : ℕ :=
  (Finset.univ.filter (fun u => arrivalTime σ u ≤ t ∧ pivotAssignment G σ u = v)).card

def finalSize {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (σ : ArrivalOrder V) (v : V) : ℕ := pivotSize G σ (Fintype.card V) v

/-- Definition 7.2: T is immediately before the (k+1)st pivot, or n. -/
def stopTime {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (σ : ArrivalOrder V) : ℕ :=
  match (pivotRun G σ (Fintype.card V)).pivots[k]? with
  | some v => arrivalTime σ v - 1
  | none => Fintype.card V

def kthPivotTime {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (σ : ArrivalOrder V) : ℕ :=
  match (pivotRun G σ (Fintype.card V)).pivots[k - 1]? with
  | some v => arrivalTime σ v
  | none => Fintype.card V

/-- Coverage includes already arrived vertices and neighbours of earlier pivots. -/
def Covered {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (σ : ArrivalOrder V) (t : ℕ) (v : V) : Prop :=
  arrivalTime σ v ≤ t ∨ ∃ p ∈ pivots G σ, arrivalTime σ p ≤ t ∧ G.Adj v p

def uncovered {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (σ : ArrivalOrder V) (t : ℕ) : Finset V :=
  Finset.univ.filter (fun v => ¬ Covered G σ t v)

def uncoveredAtStop {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (σ : ArrivalOrder V) : Finset V := uncovered G σ (stopTime G k σ)

/-- Multiset for J_σ; each pivot contributes its positive final size once. -/
def pivotSizes {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (σ : ArrivalOrder V) : Multiset ℕ :=
  (pivots G σ).val.map (finalSize G σ)

/-- Definition 7.3, p. 34: final masses of pivots assigned by t, not future pivots. -/
def projectedLoad {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 0 < k)
    (G : SimpleGraph V) (ρ : TieRule V k) (σ : ArrivalOrder V) (t : ℕ) (b : Fin k) : ℕ :=
  ∑ v ∈ (pivots G σ).filter (fun v => arrivalTime σ v ≤ t ∧
    (balancedRun hk G ρ σ t).assignment v = b), finalSize G σ v

def currentLoad {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 0 < k)
    (G : SimpleGraph V) (ρ : TieRule V k) (σ : ArrivalOrder V) (t : ℕ) (b : Fin k) : ℕ :=
  historyLoad (balancedRun hk G ρ σ t).seen (balancedRun hk G ρ σ t).assignment b

def LeastLoaded {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 0 < k)
    (G : SimpleGraph V) (ρ : TieRule V k) (σ : ArrivalOrder V) (t : ℕ) (b : Fin k) : Prop :=
  ∀ b', currentLoad hk G ρ σ t b ≤ currentLoad hk G ρ σ t b'

/-- Nonempty output clusters present at T. -/
def presentClusters {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 0 < k)
    (G : SimpleGraph V) (ρ : TieRule V k) (σ : ArrivalOrder V) : Finset (Fin k) :=
  Finset.univ.filter (fun b => 0 < currentLoad hk G ρ σ (stopTime G k σ) b)

def maxProjected {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 0 < k)
    (G : SimpleGraph V) (ρ : TieRule V k) (σ : ArrivalOrder V) (S : Finset (Fin k)) : ℕ :=
  S.sup (projectedLoad hk G ρ σ (stopTime G k σ))

/-- §7.3.4, type (iii), counting actual negative pairs. -/
def mergeCost {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 0 < k)
    (G : SimpleGraph V) (ρ : TieRule V k) (σ : ArrivalOrder V) : ℕ :=
  pairCount (fun u v => ¬ G.Adj u v ∧ pivotAssignment G σ u ≠ pivotAssignment G σ v ∧
    balancedAssignment hk G ρ σ u = balancedAssignment hk G ρ σ v)

/-- §7.3.4, types (i) and (ii). -/
def baseCost {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 0 < k)
    (G : SimpleGraph V) (ρ : TieRule V k) (σ : ArrivalOrder V) : ℕ :=
  pairCount (fun u v =>
    (¬ G.Adj u v ∧ pivotAssignment G σ u = pivotAssignment G σ v) ∨
    (G.Adj u v ∧ balancedAssignment hk G ρ σ u ≠ balancedAssignment hk G ρ σ v))

/-- S₁ with β = 2048, p. 38. -/
def smallEarlyPivots {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (σ : ArrivalOrder V) : Finset V :=
  (pivots G σ).filter (fun v => arrivalTime σ v ≤ stopTime G k σ ∧
    (pivotSize G σ (stopTime G k σ) v : ℝ) ≤ 2048 * Real.log (Fintype.card V))

/-- Left endpoint of the unique dyadic interval containing T ≥ 1. -/
def dyadicStart (t : ℕ) : ℕ := 2 ^ Nat.log 2 t

def LargeU {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (σ : ArrivalOrder V) : Prop :=
  stopTime G k σ < Fintype.card V ∧
    512 * ((smallEarlyPivots G k σ).card : ℝ) *
      ((Fintype.card V : ℝ) * Real.log (Fintype.card V) / dyadicStart (stopTime G k σ)) <
        ((uncoveredAtStop G k σ).card : ℝ)

def SmallU {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (σ : ArrivalOrder V) : Prop :=
  stopTime G k σ < Fintype.card V ∧
    ((uncoveredAtStop G k σ).card : ℝ) ≤
      512 * ((smallEarlyPivots G k σ).card : ℝ) *
        ((Fintype.card V : ℝ) * Real.log (Fintype.card V) / dyadicStart (stopTime G k σ))

end CorrKClust.BalancedPivot


