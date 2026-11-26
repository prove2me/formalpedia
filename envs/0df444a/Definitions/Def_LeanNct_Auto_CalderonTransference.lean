-- Prove2me | Definitions.Def_LeanNct_Auto_CalderonTransference
-- name    : LeanNct_Auto_CalderonTransference
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:35:43.635351+00:00
-- url     : https://prove2.me/theorems/c19f076a-d3d3-4662-8ef6-b4adb3da7729
-- title:
--   Calderon Transference
-- statement:
--   Definitions and structural lemmas for Calderon Transference, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
abbrev ctRealVector (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def ctCoordinateAxis {n : ℕ} (i : Fin n) : ctRealVector n :=
  WithLp.toLp 2 (Pi.single i (1 : ℝ))
noncomputable def aux_ct_twistedAverage {n : ℕ} (χ : ℝ → ℝ)
    (f : Fin n → ctRealVector n → ℝ) : ctRealVector n → ℝ :=
  fun x ↦ ∫ s : ℝ, χ s * ∏ i, f i (x + s • ctCoordinateAxis i)
noncomputable def aux_ct_twistedAverageAtScale {n : ℕ} (t : ℝ) (χ : ℝ → ℝ)
    (f : Fin n → ctRealVector n → ℝ) : ctRealVector n → ℝ :=
  aux_ct_twistedAverage (fun s ↦ t⁻¹ * χ (t⁻¹ * s)) f
noncomputable abbrev ctTwistedAverage {n : ℕ} (χ : ℝ → ℝ)
    (f : Fin n → ctRealVector n → ℝ) : ctRealVector n → ℝ :=
  aux_ct_twistedAverage χ f
noncomputable abbrev ctTwistedAverageAtScale {n : ℕ} (t : ℝ) (χ : ℝ → ℝ)
    (f : Fin n → ctRealVector n → ℝ) : ctRealVector n → ℝ :=
  aux_ct_twistedAverageAtScale t χ f
noncomputable def ctUnitIntervalKernel : ℝ → ℝ :=
  (Ico (0 : ℝ) 1).indicator fun _ ↦ (1 : ℝ)
noncomputable def ctEndpointEnergy {n : ℕ} (J : ℕ) (t : Fin (J + 1) → ℝ)
    (χ : ℝ → ℝ) (f : Fin n → ctRealVector n → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin J, eLpNorm
    (fun x ↦ ctTwistedAverageAtScale (t j.succ) χ f x -
      ctTwistedAverageAtScale (t j.castSucc) χ f x) 2 volume ^ 2
structure ErgodicSystem (X : Type*) [MeasurableSpace X] (μ : Measure X)
    (n : ℕ) where
  transformation : Fin n → X → X
  measurePreserving : ∀ i, MeasurePreserving (transformation i) μ μ
  commutes : ∀ i j, Function.Commute (transformation i) (transformation j)
def aux_orbit {X : Type*} : {n : ℕ} →
    (Fin n → X → X) → (Fin n → ℕ) → X → X
  | 0, _, _ => id
  | _ + 1, S, k => (S 0)^[k 0] ∘ aux_orbit (fun i ↦ S i.succ) (fun i ↦ k i.succ)
def aux_coordinate {n : ℕ} (i : Fin n) (m : ℕ) : Fin n → ℕ :=
  fun j ↦ if j = i then m else 0
noncomputable def realErgodicAverage {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {n : ℕ} (S : ErgodicSystem X μ n) (N : ℕ)
    (f : Fin n → X → ℝ) : X → ℝ :=
  fun x ↦ (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
    ∏ i, f i ((S.transformation i)^[m] x)
noncomputable def aux_discreteAverage {n : ℕ} (N : ℕ)
    (F : Fin n → (Fin n → ℕ) → ℝ) : (Fin n → ℕ) → ℝ :=
  fun k ↦ (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
    ∏ i, F i (k + aux_coordinate i m)
noncomputable def aux_discreteJumpEnergy {n J : ℕ}
    (N : Fin (J + 1) → ℕ) (F : Fin n → (Fin n → ℕ) → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin J, eLpNorm
    (fun k ↦ aux_discreteAverage (N j.succ) F k -
      aux_discreteAverage (N j.castSucc) F k) 2 Measure.count ^ 2
def aux_discreteJumpBound {n : ℕ} (p : Fin n → ℝ≥0∞)
    (C : ℝ) (g : ℕ → ℝ) : Prop :=
  ∀ (J : ℕ), 0 < J → ∀ (N : Fin (J + 1) → ℕ),
    StrictMono N → (∀ j, 0 < N j) →
      ∀ F : Fin n → (Fin n → ℕ) → ℝ,
        (∀ i, MemLp (F i) (p i) Measure.count) →
          aux_discreteJumpEnergy N F ≤
            ENNReal.ofReal C * ENNReal.ofReal (g J) *
              ∏ i, eLpNorm (F i) (p i) Measure.count ^ 2
abbrev aux_RVector (n : ℕ) := Fin n → ℝ
abbrev aux_ZVector (n : ℕ) := Fin n → ℤ
def aux_translateAxis {n : ℕ} (x : aux_RVector n) (i : Fin n)
    (s : ℝ) : aux_RVector n :=
  fun j ↦ x j + if j = i then s else 0
def aux_translateAxisInt {n : ℕ} (x : aux_ZVector n) (i : Fin n)
    (s : ℤ) : aux_ZVector n :=
  fun j ↦ x j + if j = i then s else 0
noncomputable def aux_integerDiscreteAverage {n : ℕ} (N : ℕ)
    (F : Fin n → aux_ZVector n → ℝ) : aux_ZVector n → ℝ :=
  fun k ↦ (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
    ∏ i, F i (aux_translateAxisInt k i (m : ℤ))
noncomputable def aux_natToInt {n : ℕ}
    (F : (Fin n → ℕ) → ℝ) : aux_ZVector n → ℝ := by
  classical
  exact fun k ↦ if hk : ∀ i, 0 ≤ k i then F fun i ↦ (k i).toNat else 0
noncomputable def aux_cuboidEmbed {n : ℕ} (ε δ : ℝ) (i : Fin n)
    (a : aux_ZVector n → ℝ) (y : aux_RVector n) : ℝ :=
  if ∀ j,
      if j = i then
        ε ≤ y j - (⌊y j⌋ : ℝ) ∧ y j - (⌊y j⌋ : ℝ) < ε + δ
      else
        0 ≤ y j - (⌊y j⌋ : ℝ) ∧ y j - (⌊y j⌋ : ℝ) < ε
    then a (fun j ↦ ⌊y j⌋)
    else 0
noncomputable def aux_liftRaw {n : ℕ}
    (F : aux_RVector n → ℝ) : ctRealVector n → ℝ :=
  fun x ↦ F fun j ↦ x j
def aux_commonOverlap {n : ℕ} (ε δ : ℝ) (u : aux_RVector n)
    (m : ℕ) (s : ℝ) : Prop :=
  ∀ i, ε - u i ≤ s - (m : ℝ) ∧ s - (m : ℝ) < ε + δ - u i
def aux_commonOverlapSet {n : ℕ} (ε δ : ℝ) (u : aux_RVector n)
    (m : ℕ) : Set ℝ :=
  {s | aux_commonOverlap ε δ u m s}
noncomputable def aux_overlapLower {n : ℕ} (hn : 0 < n) (ε : ℝ)
    (u : aux_RVector n) (m : ℕ) : ℝ :=
  let i₀ : Fin n := ⟨0, hn⟩
  Finset.univ.sup' ⟨i₀, Finset.mem_univ i₀⟩
    (fun i ↦ (m : ℝ) + ε - u i)
noncomputable def aux_overlapUpper {n : ℕ} (hn : 0 < n) (ε δ : ℝ)
    (u : aux_RVector n) (m : ℕ) : ℝ :=
  let i₀ : Fin n := ⟨0, hn⟩
  Finset.univ.inf' ⟨i₀, Finset.mem_univ i₀⟩
    (fun i ↦ (m : ℝ) + ε + δ - u i)
noncomputable def aux_overlapWidth {n : ℕ} (hn : 0 < n) (ε δ : ℝ)
    (u : aux_RVector n) : ℝ :=
  aux_overlapUpper hn ε δ u 0 - aux_overlapLower hn ε u 0
noncomputable def aux_overlapContribution {n : ℕ} (ε δ : ℝ)
    (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (q : ℕ) (s : ℝ) : ℝ := by
  classical
  exact if aux_commonOverlap ε δ u q s then
    ∏ i, a i (aux_translateAxisInt k i (q : ℤ))
  else 0
def aux_orbitFunction {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {n : ℕ} (S : ErgodicSystem X μ n)
    (f : Fin n → X → ℝ) (x : X) :
    Fin n → (Fin n → ℕ) → ℝ :=
  fun i k ↦ f i (aux_orbit S.transformation k x)
noncomputable def realErgodicJumpEnergy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {n J : ℕ} (S : ErgodicSystem X μ n)
    (N : Fin (J + 1) → ℕ) (f : Fin n → X → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin J, eLpNorm
    (fun x ↦ realErgodicAverage S (N j.succ) f x -
      realErgodicAverage S (N j.castSucc) f x) 2 μ ^ 2
def realVariableJumpBound {n : ℕ} (p : Fin n → ℝ≥0∞)
    (C : ℝ) (g : ℕ → ℝ) : Prop :=
  ∀ (J : ℕ), 0 < J → ∀ (t : Fin (J + 1) → ℝ),
    StrictMono t → (∀ j, 0 < t j) →
      ∀ f : Fin n → ctRealVector n → ℝ,
        (∀ i, MemLp (f i) (p i) volume) →
          ctEndpointEnergy J t ctUnitIntervalKernel f ≤
            ENNReal.ofReal C * ENNReal.ofReal (g J) *
              ∏ i, eLpNorm (f i) (p i) volume ^ 2
def realErgodicJumpBound {n : ℕ} (p : Fin n → ℝ≥0∞)
    (C : ℝ) (g : ℕ → ℝ) : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X)
    (S : ErgodicSystem X μ n) (J : ℕ) (_hJ : 0 < J)
    (N : Fin (J + 1) → ℕ) (_hN : StrictMono N) (_hNpos : ∀ j, 0 < N j)
    (f : Fin n → X → ℝ), (∀ i, MemLp (f i) (p i) μ) →
      realErgodicJumpEnergy S N f ≤
        ENNReal.ofReal C * ENNReal.ofReal (g J) *
          ∏ i, eLpNorm (f i) (p i) μ ^ 2
abbrev aux_ct_realVariableJumpBound {n : ℕ} (p : Fin n → ℝ≥0∞)
    (C : ℝ) (g : ℕ → ℝ) : Prop :=
  realVariableJumpBound p C g
section
universe v
abbrev aux_ct_realErgodicJumpBound {n : ℕ} (p : Fin n → ℝ≥0∞)
    (C : ℝ) (g : ℕ → ℝ) : Prop :=
  realErgodicJumpBound.{v} p C g
end
namespace aux_CuboidNorm
abbrev RVector (n : ℕ) := aux_RVector n
abbrev ZVector (n : ℕ) := aux_ZVector n
def cuboid {n : ℕ} (l u : RVector n) : Set (RVector n) :=
  Set.pi Set.univ fun j ↦ Ico (l j) (u j)
def axisLower {n : ℕ} (ε : ℝ) (i : Fin n)
    (k : RVector n) : RVector n :=
  fun j ↦ k j + if j = i then ε else 0
def axisUpper {n : ℕ} (ε δ : ℝ) (i : Fin n)
    (k : RVector n) : RVector n :=
  fun j ↦ k j + if j = i then ε + δ else ε
def axisCuboid {n : ℕ} (ε δ : ℝ) (i : Fin n)
    (k : RVector n) : Set (RVector n) :=
  cuboid (axisLower ε i k) (axisUpper ε δ i k)
def latticeAxisCuboid {n : ℕ} (ε δ : ℝ) (i : Fin n)
    (k : ZVector n) : Set (RVector n) :=
  axisCuboid ε δ i fun j ↦ (k j : ℝ)
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
def finiteStep (A : Finset κ) (s : κ → Set α) (a : κ → ℝ) :
    α → ℝ :=
  fun x ↦ ∑ k ∈ A, (s k).indicator (fun _ ↦ a k) x
def finiteLatticeStep {n : ℕ} (ε δ : ℝ) (i : Fin n)
    (A : Finset (ZVector n)) (a : ZVector n → ℝ) : RVector n → ℝ :=
  finiteStep A (latticeAxisCuboid ε δ i) a
def latticeCuboid {n : ℕ} (ε : ℝ) (k : ZVector n) :
    Set (RVector n) :=
  cuboid (fun j ↦ (k j : ℝ)) (fun j ↦ (k j : ℝ) + ε)
def finiteLatticeCubeStep {n : ℕ} (ε : ℝ) (A : Finset (ZVector n))
    (a : ZVector n → ℝ) : RVector n → ℝ :=
  finiteStep A (latticeCuboid ε) a
def natToIntEmbedding {n : ℕ} : (Fin n → ℕ) ↪ ZVector n where
  toFun k := fun i ↦ (k i : ℤ)
  inj' := by
    intro k l h
    funext i
    exact Int.ofNat.inj (congrFun h i)
end aux_CuboidNorm
noncomputable def aux_truncate {n : ℕ} (A : Finset (Fin n → ℕ))
    (F : (Fin n → ℕ) → ℝ) : (Fin n → ℕ) → ℝ :=
  fun k ↦ if k ∈ A then F k else 0
noncomputable def aux_localInputSupport {n : ℕ}
    (B : Finset (Fin n → ℕ)) (L : ℕ) : Finset (Fin n → ℕ) :=
  B.biUnion fun k ↦
    (Finset.univ : Finset (Fin n)).biUnion fun i ↦
      (Finset.range L).image fun m ↦ k + aux_coordinate i m
namespace aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
def box (n L : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun _ : Fin n => Finset.range L
noncomputable def orbitPowerSum {X κ : Type*} [MeasurableSpace X]
    (B : Finset κ) (T : κ → X → X) (f : X → ℝ) (p : ℝ) : X → ℝ≥0∞ :=
  fun x ↦ ∑ k ∈ B, ‖f (T k x)‖ₑ ^ p
noncomputable def truncOrbit {X κ : Type*} [MeasurableSpace X]
    (B : Finset κ) (T : κ → X → X) (f : X → ℝ) (x : X) : κ → ℝ :=
  (B : Set κ).indicator fun k ↦ f (T k x)
end aux_ErgodicBox
def calderonTransferenceConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (4 * n + 6)
end
end Auto


