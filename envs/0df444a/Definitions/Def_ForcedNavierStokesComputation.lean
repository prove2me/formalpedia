-- Prove2me | Definitions.Def_ForcedNavierStokesComputation
-- name    : ForcedNavierStokesComputation
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:11.70755+00:00
-- url     : https://prove2.me/theorems/2f4d27aa-a617-4bb4-a93f-502262bde7ba
-- statement:
--   This block sets up the definitions for a result about effective computation by forced Navier–Stokes flows; it states no theorem itself. A FiniteMachine is a Turing machine with states and symbols numbered 0..states and 0..symbols, an initial state, a blank symbol, and a partial transition function giving the new state, written symbol and a head move (stay, left or right). A TapeConfiguration is a state, an integer head position and a two-sided tape ℤ → symbols; the initial configuration writes the input word at positions 0,1,2,… with blanks elsewhere, machineStep applies one transition (and is undefined when no transition exists), and Halts(M,w) means some configuration reachable from the initial one has no successor. The machine is Gödel-coded as a natural number by encoding its sizes, initial state, blank and full transition table, and inputCode pairs this with the input word. Space is ℝ³, and a Field is a function of time and position; velocity fields are space-valued, pressures real-valued, and a Family assigns a field to every machine and input. The file defines time and spatial derivatives (the time derivative one-sided at t≥0), mixed multi-index derivatives, smoothness on t≥0, boundedness of all mixed derivatives, Sobolev-type L² regularity classes CH(k) and C1L2, divergence, Laplacian, convection (u·∇)u, gradient, the affine force f₀+νf₁, and the inertial and viscous coefficients. ZeroDataSolution(ν,f,u,p) says that u and p are smooth, u vanishes at time 0, u is divergence-free, and ∂ₜu+(u·∇)u=−∇p+νΔu+f for t≥0. ComparisonClass requires CH 2 for u, C1L2, bounds on u and its first spatial derivatives over each finite time slab, and p minus a function of time lies in CH 1; UniqueInComparison says every such solution in this class has velocity equal to U and a spatially constant pressure. Further predicates say that U, f₀ and f₁ vanish outside one common compact set, that a field is 1-periodic in time after t=1, and that X is a material flow of u (X(0,a)=a and ∂ₜX=u(t,X)). The detection geometry is the fixed point (4,0,0) and the open observer box (−1,2)³. A computability layer defines error 2⁻ⁿ, EffectiveFamily (computable rational approximations to every mixed derivative at rational points, computable uniform derivative bounds, and a computable support radius, all depending on the machine-input code), EffectiveFieldIn relative to an oracle set with the same approximation and bound requirements, real names as rational sequences within 2⁻ⁿ, computable reals, and the oracle given by such a name.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ForcedNavierStokesComputation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ForcedNavierStokesComputation.lean; bytes 16..7359
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

/-! A single main result: effective forced Navier–Stokes computation detected by a
fixed particle entering a fixed open box, exactly when the encoded machine halts. -/

namespace OAI.BalancedTransport
namespace Recorder
inductive Direction where
  | stay | left | right
  deriving DecidableEq

structure Transition (Q Γ : Type*) where
  state : Q
  write : Γ
  move : Direction
end Recorder

structure FiniteMachine where
  states : ℕ
  symbols : ℕ
  initial : Fin (states + 1)
  blank : Fin (symbols + 1)
  transition : Fin (states + 1) → Fin (symbols + 1) →
    Option (Recorder.Transition (Fin (states + 1)) (Fin (symbols + 1)))

abbrev Input (M : FiniteMachine) := List (Fin (M.symbols + 1))

structure TapeConfiguration (M : FiniteMachine) where
  state : Fin (M.states + 1)
  head : ℤ
  tape : ℤ → Fin (M.symbols + 1)

def initialConfiguration (M : FiniteMachine) (w : Input M) : TapeConfiguration M :=
  ⟨M.initial, 0, fun z => if 0 ≤ z then w[z.toNat]?.getD M.blank else M.blank⟩

def machineStep (M : FiniteMachine) (c : TapeConfiguration M) : Option (TapeConfiguration M) :=
  (M.transition c.state (c.tape c.head)).map fun v =>
    ⟨v.state, c.head + (match v.move with | .stay => 0 | .left => -1 | .right => 1),
      Function.update c.tape c.head v.write⟩

def Halts (M : FiniteMachine) (w : Input M) : Prop :=
  ∃ c, Relation.ReflTransGen (fun c d => machineStep M c = some d)
    (initialConfiguration M w) c ∧ machineStep M c = none

def Recorder.Direction.number : Recorder.Direction → ℕ
  | .stay => 0
  | .left => 1
  | .right => 2

def FiniteMachine.code (M : FiniteMachine) : ℕ :=
  Encodable.encode (M.states, M.symbols, M.initial.val, M.blank.val,
    (List.finRange (M.states + 1)).map fun q =>
      (List.finRange (M.symbols + 1)).map fun a =>
        (M.transition q a).map fun v => (v.state.val, v.write.val, v.move.number))

def inputCode (M : FiniteMachine) (w : Input M) : ℕ :=
  Encodable.encode (M.code, w.map Fin.val)

abbrev Space := Fin 3 → ℝ
abbrev Field (F : Type*) := ℝ → Space → F
abbrev Velocity := Field Space
abbrev Pressure := Field ℝ
abbrev Family (F : Type*) := (M : FiniteMachine) → Input M → F
abbrev MaterialFlow := ℝ → Space → Space
abbrev MultiIndex := List (Option (Fin 3))
abbrev RationalPoint := ℚ × (Fin 3 → ℚ)

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def timeD (v : Field F) : Field F :=
  fun t x => derivWithin (fun s => v s x) (Set.Ici 0) t

def spaceD (i : Fin 3) (v : Field F) : Field F :=
  fun t x => fderiv ℝ (v t) x (Pi.single i 1)

def mixedD : MultiIndex → Field F → Field F
  | [], v => v
  | none :: a, v => timeD (mixedD a v)
  | some i :: a, v => spaceD i (mixedD a v)

def spatialD : List (Fin 3) → Field F → Field F
  | [], v => v
  | i :: a, v => spaceD i (spatialD a v)

def Smooth (v : Field F) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Space => v z.1 z.2) (Set.Ici 0 ×ˢ Set.univ)

def BoundedMixed (v : Field F) : Prop :=
  ∀ a : MultiIndex, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x, ‖mixedD a v t x‖ ≤ C

def CH (k : ℕ) (v : Field F) : Prop :=
  ∀ a : List (Fin 3), a.length ≤ k →
    ∃ V : ℝ → Lp F 2 (volume : Measure Space),
      ContinuousOn V (Set.Ici 0) ∧
      ∀ t, 0 ≤ t → (V t : Space → F) =ᵐ[volume] spatialD a v t

def C1L2 (v : Field F) : Prop :=
  ∃ V W : ℝ → Lp F 2 (volume : Measure Space),
    ContinuousOn V (Set.Ici 0) ∧ ContinuousOn W (Set.Ici 0) ∧
    ∀ t, 0 ≤ t →
      (V t : Space → F) =ᵐ[volume] v t ∧
      (W t : Space → F) =ᵐ[volume] timeD v t ∧
      HasDerivWithinAt V (W t) (Set.Ici 0) t

def div (u : Velocity) (t : ℝ) (x : Space) : ℝ :=
  ∑ i, spaceD i u t x i

def laplacian (u : Velocity) : Velocity :=
  fun t x => ∑ i, spaceD i (spaceD i u) t x

def convection (u : Velocity) : Velocity :=
  fun t x => ∑ i, (u t x i) • spaceD i u t x

def gradient (p : Pressure) (t : ℝ) (x : Space) : Space :=
  fun i => spaceD i p t x

def affineForce (f₀ f₁ : Velocity) (ν : ℝ) : Velocity :=
  fun t x => f₀ t x + ν • f₁ t x

def inertialCoefficient (u : Velocity) : Velocity :=
  fun t x => timeD u t x + convection u t x

def viscousCoefficient (u : Velocity) : Velocity :=
  fun t x => -laplacian u t x

def ZeroDataSolution (ν : ℝ) (f u : Velocity) (p : Pressure) : Prop :=
  Smooth u ∧ Smooth p ∧
  (∀ x, u 0 x = 0) ∧
  (∀ t, 0 ≤ t → ∀ x, div u t x = 0) ∧
  (∀ t, 0 ≤ t → ∀ x,
    timeD u t x + convection u t x =
      -gradient p t x + ν • laplacian u t x + f t x)

def BoundedOnFiniteSlabs (u : Velocity) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 ≤ C ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      ‖u t x‖ ≤ C ∧ ∀ i : Fin 3, ‖spaceD i u t x‖ ≤ C

def ComparisonClass (u : Velocity) (p : Pressure) : Prop :=
  CH 2 u ∧ C1L2 u ∧ BoundedOnFiniteSlabs u ∧
    ∃ c : ℝ → ℝ, CH 1 (fun t x => p t x - c t)

def UniqueInComparison (ν : ℝ) (f U : Velocity) : Prop :=
  ∀ u p, ZeroDataSolution ν f u p → ComparisonClass u p →
    (∀ t, 0 ≤ t → ∀ x, u t x = U t x) ∧
    (∀ t, 0 ≤ t → ∀ x y, p t x = p t y)

def CommonCompactSupport (U f₀ f₁ : Velocity) : Prop :=
  ∃ K : Set Space, IsCompact K ∧
    ∀ t, 0 ≤ t → ∀ x, x ∉ K → U t x = 0 ∧ f₀ t x = 0 ∧ f₁ t x = 0

def PeriodicAfterOne (v : Velocity) : Prop :=
  ∀ t, 1 ≤ t → ∀ x, v (t + 1) x = v t x

def IsMaterialFlow (u : Velocity) (X : MaterialFlow) : Prop :=
  (∀ a, X 0 a = a) ∧
  ∀ a t, 0 ≤ t → HasDerivWithinAt (fun s => X s a) (u t (X t a)) (Set.Ici 0) t

def fixedLabel : Space := ![4, 0, 0]

def observer : Set Space :=
  Set.pi Set.univ (fun _ : Fin 3 => Set.Ioo (-1 : ℝ) 2)

def rationalSpace (x : Fin 3 → ℚ) : Space := fun i => (x i : ℝ)

def error (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

def EffectiveFamily (v : Family Velocity) : Prop :=
  ∃ E : (ℕ × MultiIndex × RationalPoint × ℕ) → (Fin 3 → ℚ),
  ∃ b : (ℕ × MultiIndex) → ℕ,
  ∃ R : ℕ → ℕ,
    Computable E ∧ Computable b ∧ Computable R ∧
    (∀ M w a z n, 0 ≤ z.1 → ∀ i,
      |(E (inputCode M w, a, z, n) i : ℝ) -
        mixedD a (v M w) (z.1 : ℝ) (rationalSpace z.2) i| ≤ error n) ∧
    (∀ M w a t, 0 ≤ t → ∀ x,
      ‖mixedD a (v M w) t x‖ ≤ (b (inputCode M w, a) : ℝ)) ∧
    (∀ M w t, 0 ≤ t → ∀ x,
      (R (inputCode M w) : ℝ) < ‖x‖ → v M w t x = 0)

def EffectiveFieldIn (O : Set (ℕ →. ℕ)) (v : Velocity) : Prop :=
  ∃ E : (MultiIndex × RationalPoint × ℕ) → (Fin 3 → ℚ),
  ∃ b : MultiIndex → ℕ,
    ComputableIn O E ∧ ComputableIn O b ∧
    (∀ a z n, 0 ≤ z.1 → ∀ i,
      |(E (a, z, n) i : ℝ) -
        mixedD a v (z.1 : ℝ) (rationalSpace z.2) i| ≤ error n) ∧
    (∀ a t, 0 ≤ t → ∀ x, ‖mixedD a v t x‖ ≤ (b a : ℝ))

def RealName (name : ℕ → ℚ) (x : ℝ) : Prop :=
  ∀ n, |(name n : ℝ) - x| ≤ error n

def ComputableReal (x : ℝ) : Prop :=
  ∃ name : ℕ → ℚ, Computable name ∧ RealName name x

def nameOracle (name : ℕ → ℚ) : ℕ →. ℕ :=
  fun n => Part.some (Encodable.encode (name n))

end



end OAI.BalancedTransport


