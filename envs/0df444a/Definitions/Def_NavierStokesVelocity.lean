-- Prove2me | Definitions.Def_NavierStokesVelocity
-- name    : NavierStokesVelocity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.760594+00:00
-- url     : https://prove2.me/theorems/94e77ed5-a6f8-4fbd-9042-33e7eaf9ffde
-- statement:
--   This block sets up the formal vocabulary for a velocity-detection construction built around the three-dimensional incompressible Navier-Stokes equations. Fields on Coord n = ℝⁿ are time-dependent scalar or vector fields; spatialD takes partial derivatives, timeD a one-sided time derivative on [0,∞), and laplacian, advection and divergence are defined from them. NavierStokes(ν,u,p,f) is a defined proposition: for all t≥0, x and components i, ∂ₜuᵢ + (u·∇)uᵢ = −∂ᵢp + νΔuᵢ + fᵢ, the divergence of u vanishes for t≥0, and u(0,x)=0 for all x, so the velocity starts at rest and is driven by the forcing f. Observation events ask whether, for some t≥0, the third velocity component exceeds 1/2 at a point with 1/32<x₁<1/8 (torusEvent), or whether the integral of u₃ over the upper half plane {X₁>0} times the unit-height period interval (0,1] exceeds 1/2 (planeEvent via planeMass). Auxiliary machinery includes a Turing-style two-stack machine with base-b stack updates for moves right, stay and left, configurations, rule application, a lookup table, a history-augmented configuration with packed-state addresses of active boxes, and a base-b digit encoding of words; expanding radii 4D-based geometric scales with initial radius 1024·3000(1+ν)·4D(KD+2); smooth cutoff profiles (window, ramp, theta) and center paths interpolating between lattice-like positions; a uniform-derivatives boundedness predicate on iterated Fréchet derivatives; a closed subspace of pairs (C₀ function, L¹ function) that agree almost everywhere with a continuous evaluation functional; and a cylinder ℝ²×(0,1] with z-periodic fields, Sobolev-type structures SliceH2 and PressureH1, continuity in L² and C¹-in-time notions, and a ComparisonClass bundling H², L², continuity and bounded-derivative regularity of (u,p) on every finite time interval.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NavierStokesVelocity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/NavierStokesVelocity.lean; bytes 16..15447
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
namespace VelocityDetection
open scoped BigOperators Topology ContDiff
open Set Function Filter

abbrev Coord (n : ℕ) := Fin n → ℝ

abbrev ScalarField (n : ℕ) := ℝ → Coord n → ℝ

abbrev VectorField (n : ℕ) := ℝ → Coord n → Coord n

theorem neZeroTwo : NeZero 2 := ⟨Nat.succ_ne_zero 1⟩

theorem neZeroThree : NeZero 3 := ⟨Nat.succ_ne_zero 2⟩

theorem neZeroFive : NeZero 5 := ⟨Nat.succ_ne_zero 4⟩

def spatialD {n : ℕ} (i : Fin n) (q : ScalarField n) : ScalarField n :=
  fun t x => deriv (fun s => q t (Function.update x i s)) (x i)

def timeD {n : ℕ} (q : ScalarField n) : ScalarField n :=
  fun t x => derivWithin (fun s => q s x) (Ici 0) t

def laplacian {n : ℕ} (q : ScalarField n) : ScalarField n :=
  fun t x => ∑ i : Fin n, spatialD i (spatialD i q) t x

def advection {n : ℕ} (a : VectorField n) (q : ScalarField n) : ScalarField n :=
  fun t x => ∑ i : Fin n, a t x i * spatialD i q t x

def divergence {n : ℕ} (a : VectorField n) : ScalarField n :=
  fun t x => ∑ i : Fin n, spatialD i (fun s y => a s y i) t x

def NavierStokes (ν : ℝ) (u : VectorField 3) (p : ScalarField 3)
    (f : VectorField 3) : Prop :=
  (∀ (t : ℝ), 0 ≤ t → ∀ x : Coord 3, ∀ i : Fin 3,
    timeD (fun s y => u s y i) t x + advection u (fun s y => u s y i) t x =
      -spatialD i p t x + ν * laplacian (fun s y => u s y i) t x + f t x i) ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ x, divergence u t x = 0) ∧
  (∀ x, u 0 x = 0)

def horizontal (x : Coord 3) : Coord 2 := ![x 0, x 1]

end VelocityDetection
end

noncomputable section
namespace VelocityDetection.Stacks
open scoped BigOperators Topology ContDiff
open Set Function Filter

inductive Move
  | right
  | stay
  | left
  deriving DecidableEq, Repr

def update (b : ℕ) (m : Move) (β x y : ℕ) : ℕ × ℕ :=
  match m with
  | .right => (b * x + β, y / b)
  | .stay => (x, y - y % b + β)
  | .left => (x / b, x % b + b * β + b ^ 2 * (y / b))

structure Rule (σ : Type*) (b : ℕ) where
  target : σ
  written : Fin b
  move : Move

structure Configuration (σ : Type*) where
  state : σ
  leftStack : ℕ
  rightStack : ℕ
  deriving DecidableEq

def applyRule {σ : Type*} {b : ℕ} (r : Rule σ b) (c : Configuration σ) : Configuration σ :=
  let st := update b r.move r.written c.leftStack c.rightStack
  ⟨r.target, st.1, st.2⟩

def address (B i x y : ℕ) : ℕ := 1 + x + B * y + B ^ 2 * i

def capacity (b m n : ℕ) : ℕ := b ^ (m + n)

end VelocityDetection.Stacks
end

noncomputable section
namespace VelocityDetection.Expanding
open scoped BigOperators Topology ContDiff
open Set Function Filter

def lambda (D : ℝ) : ℝ := 4 * D

def initialRadius (ν K D : ℝ) : ℝ :=
  1024 * 3000 * (1 + ν) * lambda D * (K * D + 2)

def radius (ν K D : ℝ) (n : ℕ) : ℝ := initialRadius ν K D * lambda D ^ n

end VelocityDetection.Expanding
end

noncomputable section
namespace VelocityDetection.Observation
open scoped BigOperators Topology ContDiff
open Set Function Filter
open MeasureTheory

def join (X : Coord 2) (z : ℝ) : Coord 3 := ![X 0, X 1, z]

def torusEvent (u : VectorField 3) : Prop :=
  letI := neZeroThree
  ∃ t : ℝ, 0 ≤ t ∧ ∃ x : Coord 3,
    1 / ((32 : ℕ) : ℝ) < x 1 ∧ x 1 < 1 / ((8 : ℕ) : ℝ) ∧ (1 / ((2 : ℕ) : ℝ) : ℝ) < u t x 2

def upperHalfPlane : Set (Coord 2) := {X | 0 < X 1}

def planeMass (u : VectorField 3) (t : ℝ) : ℝ :=
  letI := neZeroThree
  ∫ q in upperHalfPlane ×ˢ Ioc (0 : ℝ) 1,
    u t (join q.1 q.2) 2 ∂(volume.prod volume)

def planeEvent (u : VectorField 3) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ (1 / ((2 : ℕ) : ℝ) : ℝ) < planeMass u t

end VelocityDetection.Observation
end

noncomputable section
namespace VelocityDetection.SmoothProfiles
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff

abbrev step := Real.smoothTransition

end VelocityDetection.SmoothProfiles
end

noncomputable section
namespace VelocityDetection.TranslationGates
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open SmoothProfiles

def window (s : ℝ) : ℝ := step (s + 3) * step (3 - s)

end VelocityDetection.TranslationGates
end

noncomputable section
namespace VelocityDetection.CenterPaths
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open SmoothProfiles

def ramp (r : ℝ) : ℝ := step (2 * r - 1 / 2)

def theta (a T : ℝ) (j : ℕ) (t : ℝ) : ℝ := ramp (3 * (t - a) / T - j)

def privateRow (S : ℝ) (k : ℕ) : ℝ := -((k : ℝ) + 2) * S

def center (a T S S' σ : ℝ) (k l : ℕ) (t : ℝ) : Coord 2 :=
  ![(1 - theta a T 1 t) * S * k + theta a T 1 t * S' * l,
    -(1 - theta a T 0 t) * S +
      (theta a T 0 t - theta a T 2 t) * privateRow S k + theta a T 2 t * σ * S']

end VelocityDetection.CenterPaths
end

noncomputable section
namespace VelocityDetection.UniformDerivatives
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
variable {I E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def Bounded (f : I → E → F) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ n (f a) x‖ ≤ C

end VelocityDetection.UniformDerivatives
end

noncomputable section
namespace VelocityDetection.Stacks
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))

def lookup (c : Configuration (Fin N)) : Option (Rule (Fin N) b) :=
  table c.state ⟨c.rightStack % b, Nat.mod_lt _ hb⟩

end VelocityDetection.Stacks
end

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

def compatible (n : ℕ) : Submodule ℝ
    (C₀(Coord n, ℝ) × Lp ℝ 1 (volume : Measure (Coord n))) where
  carrier := {v | (fun X => v.2 X) =ᵐ[volume] (fun X => v.1 X)}
  zero_mem' := by exact Lp.coeFn_zero ..
  add_mem' := by
    intro v w hv hw
    change (fun X => (v.2 + w.2) X) =ᵐ[volume] (fun X => v.1 X + w.1 X)
    change (fun X => v.2 X) =ᵐ[volume] (fun X => v.1 X) at hv
    change (fun X => w.2 X) =ᵐ[volume] (fun X => w.1 X) at hw
    filter_upwards [Lp.coeFn_add v.2 w.2, hv, hw] with X hadd hvx hwx
    simpa [hvx, hwx] using hadd
  smul_mem' := by
    intro c v hv
    change (fun X => (c • v.2) X) =ᵐ[volume] (fun X => c * v.1 X)
    change (fun X => v.2 X) =ᵐ[volume] (fun X => v.1 X) at hv
    filter_upwards [Lp.coeFn_smul c v.2, hv] with X hsmul hvx
    simpa [hvx] using hsmul

end VelocityDetection.TailSpace
end

noncomputable section
namespace VelocityDetection.Cylinder
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

abbrev Space := Coord 2 × ℝ

abbrev Vect := Fin 3 → ℝ

def measure : Measure Space := volume.prod (volume.restrict (Ioc (0 : ℝ) 1))

def periodic (f : Space → ℝ) : Prop := ∀ X z, f (X, z + 1) = f (X, z)

def frame (i : Fin 3) : Space := ![(![1, 0], 0), (![0, 1], 0), (0, 1)] i

def D (i : Fin 3) (f : Space → ℝ) (x : Space) : ℝ := fderiv ℝ f x (frame i)

structure SliceH2 (v : Space → Vect) : Prop where
  smooth : ∀ i, ContDiff ℝ 2 (fun x => v x i)
  per : ∀ i, periodic (fun x => v x i)
  square_integrable : ∀ i, MemLp (fun x => v x i) 2 measure
  derivative_square_integrable : ∀ i k, MemLp (D k (fun x => v x i)) 2 measure
  second_square_integrable : ∀ i k l, MemLp (D l (D k (fun x => v x i))) 2 measure

structure PressureH1 (q : Space → ℝ) : Prop where
  smooth : ContDiff ℝ 1 q
  per : periodic q
  square_integrable : MemLp q 2 measure
  derivative_square_integrable : ∀ k, MemLp (D k q) 2 measure

theorem twoAtLeastTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

abbrev LpSpace {α : Type*} [MeasurableSpace α] (E : Type*) [NormedAddCommGroup E]
    (p : ENNReal) (μ : Measure α) : Type _ := Lp E p μ

abbrev L2Space : Type :=
  letI := twoAtLeastTwo
  LpSpace ℝ 2 measure

def dt (u : ℝ → Space → Vect) (t : ℝ) (x : Space) (i : Fin 3) : ℝ :=
  derivWithin (fun s => u s x i) (Ici 0) t

theorem spaceOuterMeasureClass : OuterMeasureClass (Measure Space) Space :=
  Measure.instOuterMeasureClass

def continuousL2On (g : ℝ → Space → ℝ) (T : ℝ) : Prop :=
  letI : IsTopologicalAddGroup ℝ := instIsTopologicalAddGroupReal
  letI := spaceOuterMeasureClass
  ∃ G : ℝ → L2Space, ContinuousOn G (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (fun x => G t x) =ᵐ[measure] g t

def continuousH2On (u : ℝ → Space → Vect) (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, SliceH2 (u t)) ∧
  (∀ i, continuousL2On (fun t x => u t x i) T) ∧
  (∀ i k, continuousL2On (fun t => D k (fun x => u t x i)) T) ∧
  (∀ i k l, continuousL2On (fun t => D l (D k (fun x => u t x i))) T)

def continuousH1On (p : ℝ → Space → ℝ) (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, PressureH1 (p t)) ∧ continuousL2On p T ∧
  (∀ i, continuousL2On (fun t => D i (p t)) T)

def C1L2On (u : ℝ → Space → Vect) (T : ℝ) : Prop :=
  letI : IsTopologicalAddGroup ℝ := instIsTopologicalAddGroupReal
  letI := spaceOuterMeasureClass
  ∃ U dU : ℝ → Fin 3 → L2Space,
    (∀ i, ContinuousOn (fun t => U t i) (Icc 0 T)) ∧
    (∀ i, ContinuousOn (fun t => dU t i) (Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, ∀ i, (fun x => U t i x) =ᵐ[measure] (fun x => u t x i)) ∧
    (∀ t ∈ Icc 0 T, ∀ i, (fun x => dU t i x) =ᵐ[measure] (fun x => dt u t x i)) ∧
    (∀ t ∈ Icc 0 T, ∀ i,
      HasDerivWithinAt (fun s => U s i) (dU t i) (Icc 0 T) t)

structure ComparisonClass (u : ℝ → Space → Vect) (p : ℝ → Space → ℝ) : Prop where
  velocity_H2 : ∀ T > 0, continuousH2On u T
  velocity_C1L2 : ∀ T > 0, C1L2On u T
  pressure_H1 : ∀ T > 0, continuousH1On p T
  time_derivative : ∀ t ≥ 0, ∀ x i,
    HasDerivWithinAt (fun s => u s x i) (dt u t x i) (Ici 0) t
  velocity_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => u y.1 y.2 i) (Icc 0 T ×ˢ univ)
  time_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => dt u y.1 y.2 i) (Icc 0 T ×ˢ univ)
  gradient_continuous : ∀ T > 0, ∀ i k,
    ContinuousOn (fun y : ℝ × Space => D k (fun x => u y.1 x i) y.2) (Icc 0 T ×ˢ univ)
  second_continuous : ∀ T > 0, ∀ i k l,
    ContinuousOn (fun y : ℝ × Space => D l (D k (fun x => u y.1 x i)) y.2) (Icc 0 T ×ˢ univ)
  pressure_continuous : ∀ T > 0,
    ContinuousOn (fun y : ℝ × Space => p y.1 y.2) (Icc 0 T ×ˢ univ)
  pressure_gradient_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => D i (p y.1) y.2) (Icc 0 T ×ˢ univ)
  bounds : ∀ T > 0, ∃ B : ℝ, 0 ≤ B ∧
    (∀ t ∈ Icc 0 T, ∀ x i, |u t x i| ≤ B) ∧
    (∀ t ∈ Icc 0 T, ∀ x i k, |D k (fun y => u t y i) x| ≤ B)

def join (x : Space) : Coord 3 :=
  letI := neZeroTwo
  ![x.1 0, x.1 1, x.2]

end VelocityDetection.Cylinder
end

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

def evalLinear (X : Coord 2) : compatible 2 →ₗ[ℝ] ℝ where
  toFun f := f.val.1 X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def eval (X : Coord 2) : compatible 2 →L[ℝ] ℝ where
  toLinearMap := evalLinear X
  cont := AddMonoidHomClass.continuous_of_bound (evalLinear X) 1 (fun f => by
    change ‖f.val.1 X‖ ≤ 1 * ‖f.val‖
    rw [one_mul]
    exact (BoundedContinuousFunction.norm_coe_le_norm f.val.1.toBCF X).trans (norm_fst_le f.val))

end VelocityDetection.TailSpace
end

noncomputable section
namespace VelocityDetection.History
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Stacks

structure Configuration (N : ℕ) where
  tape : Stacks.Configuration (Fin N)
  history : ℕ
  deriving DecidableEq

end VelocityDetection.History
end

noncomputable section
namespace VelocityDetection.History
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Stacks
variable {N b : ℕ} (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b))

def radix (N b : ℕ) : ℕ := N * b

def tag (c : Stacks.Configuration (Fin N)) : ℕ := b * c.state.val + c.rightStack % b

include hb in

def applyRule (r : Rule (Fin N) b) (c : Configuration N) : Configuration N :=
  ⟨Stacks.applyRule r c.tape, radix N b * c.history + tag (b := b) c.tape⟩

include hb in

def packedState (c : Configuration N) : ℕ := N * c.history + c.tape.state.val

def address (B : ℕ) (c : Configuration N) : ℕ :=
  Stacks.address B (packedState c) c.tape.leftStack c.tape.rightStack

abbrev Box (N B H : ℕ) := Fin N × Fin B × Fin B × Fin H

def config {B H : ℕ} (c : Box N B H) : Configuration N :=
  ⟨⟨c.1, c.2.1, c.2.2.1⟩, c.2.2.2⟩

def Active (B H : ℕ) := {c : Box N B H // (Stacks.lookup hb table (config c).tape).isSome}

def rule {B H : ℕ} (c : Active hb table B H) : Rule (Fin N) b :=
  (Stacks.lookup hb table (config c.val).tape).get c.property

def target {B H : ℕ} (c : Active hb table B H) : Configuration N :=
  applyRule (rule hb table c) (config c.val)

def sourceAddress {B H : ℕ} (c : Active hb table B H) : ℕ := address B (config c.val)

def targetAddress {B H : ℕ} (c : Active hb table B H) : ℕ := address (b * B) (target hb table c)

end VelocityDetection.History
end

noncomputable section
namespace VelocityDetection.TapeCodes
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Turing Stacks
variable {b N : ℕ} [NeZero b] [NeZero N]

def word (w : List (Fin b)) : ℕ := Nat.ofDigits b (w.map Fin.val)



end VelocityDetection.TapeCodes
end
end OAI


