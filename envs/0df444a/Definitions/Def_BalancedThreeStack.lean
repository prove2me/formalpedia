-- Prove2me | Definitions.Def_BalancedThreeStack
-- name    : BalancedThreeStack
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:00.976496+00:00
-- url     : https://prove2.me/theorems/245e12d2-b8d1-4a0e-b78a-e4f3f8bb3f1b
-- statement:
--   This block defines finite deterministic tape machines with nonempty finite state and symbol sets, designated initial state and blank symbol, and optional transitions that write a symbol and move the integer-indexed head left, right, or nowhere; a missing transition halts execution. Input words occupy consecutive cells starting at zero, with blanks elsewhere, and halting means reaching a configuration with no successor after finitely many steps. Machines and machine–input pairs receive natural-number encodings. For time-dependent fields on ℝ³, it defines time differentiation within t≥0, coordinate derivatives, and arbitrary ordered mixed derivatives. Smoothness means joint infinite differentiability on t≥0; bounded mixed derivatives means each derivative has its own uniform bound over all nonnegative times and spatial points. CH(k) requires every spatial derivative of order at most k to have a continuous L²-valued representative in time, while C1L2 requires the field and its time derivative to form a continuously differentiable L²-valued curve. The standard divergence, Laplacian, convection term, and pressure gradient specify ZeroDataSolution(ν,f,u,p): smooth velocity and pressure, zero initial velocity, divergence-free velocity, and ∂ₜu+(u·∇)u=−∇p+νΔu+f for t≥0, without requiring ν>0. It also defines affine forcing f₀+νf₁ and coefficients ∂ₜu+(u·∇)u and −Δu. The comparison class requires CH(2), C1L2, uniform bounds for velocity and first spatial derivatives on every finite time slab, and CH(1) for pressure after subtracting a time-dependent scalar. UniqueInComparison asserts that every zero-data solution in this class has a specified velocity U and spatially constant pressure. Further predicates require U,f₀,f₁ to share a compact spatial support for all t≥0, or a velocity field to be one-periodic for t≥1. A material flow starts at each particle label and solves X′(t,a)=u(t,X(t,a)); the fixed label is (4,0,0), and the observer region is (−1,2)³. An effective family, indexed by machines and inputs, has computable procedures that approximate every mixed derivative component at nonnegative rational spacetime points within 2⁻ⁿ, give global natural-number bounds for each derivative, and give a natural-number radius outside which the field vanishes. EffectiveFieldIn requires oracle-relative computable derivative approximations and bounds for one field, without the support-radius requirement. Finally, a real name is a rational sequence approximating its real value within 2⁻ⁿ; a computable real has a computable such name, and nameOracle returns the encoded rational at each index as an everywhere-defined partial natural-number function. These are definitions and predicates, not assertions that such fluid simulations or effective families exist.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BalancedThreeStack.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BalancedThreeStack.lean; bytes 16..7344
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace BalancedTransport
namespace Recorder
inductive Direction where
  | stay | left | right
  deriving DecidableEq

instance : Fintype Direction :=
  ⟨{.stay, .left, .right}, by intro d; cases d <;> simp⟩

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
end BalancedTransport

namespace BalancedTransport



end BalancedTransport
end OAI


