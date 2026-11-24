-- Prove2me | Definitions.Def_ShipConsol_OneWH_Supplement_Variable
-- name    : ShipConsol_OneWH_Supplement_Variable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:25:40.575065+00:00
-- url     : https://prove2.me/theorems/6253cf1b-5cb9-40de-bbcf-1b8bb71512fd
-- title:
--   §§3, 6 — unrestricted unit-order shipping, package partitions, H2/H3 and finite-horizon costs
-- statement:
--   Let F and v be nonnegative, convex, non-increasing functions on [1,∞), let d≥1 be the deadline, and let p_m, 0≤m≤M, be a stationary independent batch-count law. A state is a sorted finite list of positive slacks at most d. An action is any collection of nonempty disjoint packages of order indices; their union is the subset shipped. Every order of slack 1 must ship, and at the final decision every pending order must ship. For a package B,
--
--   $$c(B)=F(\min_{i\in B}z_i)+|B|v(\min_{i\in B}z_i).$$
--
--   The finite action set enumerates every subset and every partition. Retained slacks decrease by one; m new unit orders of slack d are appended. The unrestricted optimum is the finite-scenario Bellman value. H3 ships all pending orders together when the smallest slack crosses a constant integer threshold in {1,…,d}; H2 (p. 24) permits thresholds in {1,…,d} depending on the number of pending orders, still using one package. Terminal shipment is forced for both. Their actual expected T-period costs are evaluated recursively from an empty system. H3 is minimized over its finite threshold set; H2 is the infimum over all admissible volume-threshold functions. On source data its cost set is nonempty and bounded below by zero, and only finitely many table entries matter for a finite horizon.
--
--   The fixed-cost criterion is F(τ)/(1/α+d−τ) for α>0, extended by zero at α=0. The explicit bounds of Theorems 5–6 are also defined here; at γ=0 the first printed fraction of Theorem 5 is 0/0 and carries no value, so the Theorem 5 bound is then its second term alone. The Theorem 6 counterexample instance is also defined here. No stationary rational cost is substituted for a finite-horizon cost. The Theorem 6 counterexample uses T=5, d=3, α=3/4, F(x)=max{2,4−x}, v=0.
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), pinned PDF sha256 2cc7647135cddd3db3d07ad21c65ac52502947d2dde5f337f3ab9948547f0a03, §3, pp. 9–11; §§6.1–6.2, pp. 21–25

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_Control

namespace ShipConsol.OneWH.Supplement

/-- General bounded batch law; the hypotheses on the data are kept in SourceData. -/
structure ShippingData where
  F : ℝ → ℝ
  v : ℝ → ℝ
  d : ℕ
  maxBatch : ℕ
  p : Fin (maxBatch + 1) → ℝ

def CostAssumptions (F : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (Set.Ici 1) F ∧ AntitoneOn F (Set.Ici 1) ∧
    ∀ x ∈ Set.Ici (1 : ℝ), 0 ≤ F x

def ShippingData.SourceData (D : ShippingData) : Prop :=
  1 ≤ D.d ∧ CostAssumptions D.F ∧ CostAssumptions D.v ∧
    (∀ m, 0 ≤ D.p m) ∧ ∑ m, D.p m = 1

def validSlacks (d : ℕ) (s : List ℕ) : Prop :=
  s.Pairwise (· ≤ ·) ∧ ∀ z ∈ s, 1 ≤ z ∧ z ≤ d

abbrev Packages := Finset (Finset ℕ)

def shipped (a : Packages) : Finset ℕ := a.biUnion id

noncomputable def packageCost (F v : ℝ → ℝ) (s : List ℕ) (b : Finset ℕ) : ℝ :=
  if h : b.Nonempty then
    let z := b.inf' h (fun i => s[i]?.getD 0)
    F z + (b.card : ℝ) * v z
  else 0

noncomputable def shipmentCost (D : ShippingData) (s : List ℕ) (a : Packages) : ℝ :=
  ∑ b ∈ a, packageCost D.F D.v s b

/-- Every subset and every partition is available; no structural theorem is built in. -/
noncomputable def packageActions (t : ℕ) (s : List ℕ) : Finset Packages := by
  classical
  exact ((Finset.range s.length).powerset.powerset).filter fun a =>
    (∀ b ∈ a, b.Nonempty) ∧
    (∀ b ∈ a, ∀ c ∈ a, b ≠ c → Disjoint b c) ∧
    (∀ i ∈ Finset.range s.length, (t = 1 ∨ s[i]?.getD 0 = 1) → i ∈ shipped a)

/-- Retained slacks decrease; new unit orders arrive at the end of the period. -/
def nextSlacks (d : ℕ) (s : List ℕ) (a : Packages) (m : ℕ) : List ℕ :=
  ((s.zipIdx.filter fun zi => zi.2 ∉ shipped a).map fun zi => zi.1 - 1) ++
    List.replicate m d

noncomputable def shippingControl (D : ShippingData) :
    ScenarioControl (List ℕ) Packages (Fin (D.maxBatch + 1)) where
  actions := packageActions
  cost := shipmentCost D
  next := fun s a m => nextSlacks D.d s a m
  weight := D.p

noncomputable def onePackage (s : List ℕ) : Packages :=
  if s = [] then ∅ else {Finset.range s.length}

noncomputable def minSlack (s : List ℕ) : ℕ := s.foldr min (s.headD 0)

noncomputable def thresholdPolicy (θ : ℕ → ℕ → ℕ) (t : ℕ) (s : List ℕ) : Packages :=
  if t = 1 ∨ minSlack s ≤ θ t s.length then onePackage s else ∅

def validThresholds (d : ℕ) (θ : ℕ → ℕ → ℕ) : Prop :=
  ∀ t n, 1 ≤ θ t n ∧ θ t n ≤ d

noncomputable def h3Total (D : ShippingData) (T τ : ℕ) : ℝ :=
  (shippingControl D).evaluate (thresholdPolicy fun _ _ => τ) T []

noncomputable def h2Total (D : ShippingData) (T : ℕ) (θ : ℕ → ℕ → ℕ) : ℝ :=
  (shippingControl D).evaluate (thresholdPolicy θ) T []

/-- The cost sets are nonempty and bounded below by zero on SourceData, since all
feasible policies have nonnegative, finite costs. Only finitely many decisions are visited. -/
noncomputable def h3Average (D : ShippingData) (T : ℕ) : ℝ :=
  (finiteMin (Finset.Icc 1 D.d) (h3Total D T)) / T

/-- H2 (p. 24): one package, thresholds varying with the number of pending orders only,
optimized like H3's constant threshold. The set is nonempty (θ ≡ 1) and bounded below
by zero on SourceData. -/
noncomputable def h2Average (D : ShippingData) (T : ℕ) : ℝ :=
  sInf {c : ℝ | ∃ θ : ℕ → ℕ, (∀ n, 1 ≤ θ n ∧ θ n ≤ D.d) ∧
    c = h2Total D T (fun _ n => θ n) / T}

noncomputable def optimalAverage (D : ShippingData) (T : ℕ) : ℝ :=
  (shippingControl D).value T [] / T

noncomputable def bernoulliData (F v : ℝ → ℝ) (d : ℕ) (α : ℝ) : ShippingData where
  F := F
  v := v
  d := d
  maxBatch := 1
  p := fun m => if m.val = 0 then 1 - α else α

noncomputable def nonemptyProbability (D : ShippingData) : ℝ := 1 - D.p 0

noncomputable def fixedCriterion (F : ℝ → ℝ) (α : ℝ) (d τ : ℕ) : ℝ :=
  if α = 0 then 0 else F τ / (1 / α + (d : ℝ) - τ)

def fixedMinimizer (D : ShippingData) (τ : ℕ) : Prop :=
  1 ≤ τ ∧ τ ≤ D.d ∧ ∀ k, 1 ≤ k → k ≤ D.d →
    fixedCriterion D.F (nonemptyProbability D) D.d τ ≤
      fixedCriterion D.F (nonemptyProbability D) D.d k

/-- The printed minimum of Theorem 5 with `v(2) = γ F(2)`. At `γ = 0` the first printed
fraction is `0/0`, which has no value, so only the second term bounds the ratio there
(`if`, not Lean's junk `0/0 = 0`). -/
noncomputable def bound5 (F : ℝ → ℝ) (α γ : ℝ) : ℝ :=
  let Δ := F 1 - F 2
  let a₁ := 2 / α + 1
  let a₂ := 3 / (1 - α)
  let second := ((1 + (1 + 3 * α) * (3 - α)) / (1 + 2 * α) * F 2) /
      (F 2 / (α * (1 - α)) + Δ / α)
  if γ = 0 then second
  else min (γ * Δ / (a₁ * γ * Δ + (a₁ + a₂) * (γ * F 2))) second

noncomputable def bound6 (d τ : ℕ) (α γ : ℝ) : ℝ :=
  min (γ * ((d : ℝ) - τ) * α / (1 + γ))
    ((d : ℝ) * α / (γ * (1 + (d : ℝ) * α) + 1))

/-- Zero-variable-cost instance refuting the printed finite-T Theorem 6. -/
noncomputable def example6 : ShippingData :=
  bernoulliData (fun x => max 2 (4 - x)) (fun _ => 0) 3 (3 / 4)

/-- A time-dependent one-package threshold policy, admissible in the unrestricted model. -/
noncomputable def witnessThreshold6 (t _n : ℕ) : ℕ :=
  if t = 1 then 3 else if 3 ≤ t then 2 else 1

end ShipConsol.OneWH.Supplement


