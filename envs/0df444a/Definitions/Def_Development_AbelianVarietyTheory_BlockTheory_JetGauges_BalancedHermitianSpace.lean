-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_BalancedHermitianSpace
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_BalancedHermitianSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:25.381678+00:00
-- url     : https://prove2.me/theorems/5851fd5b-dbdd-4939-a73c-4ba5f629b472
-- title:
--   Balanced Hermitian Space
-- statement:
--   Definitions and structural lemmas for Balanced Hermitian Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/BalancedHermitianSpace.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
open NumberField NumberField.IsCMField TensorProduct
abbrev Bil (Y : Type) [AddCommGroup Y] : Type := Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ
section Forms
variable {Y : Type} [AddCommGroup Y]
def quad (β : Bil Y) (x : Y) : ℝ := β x x / 2
def IsPsd (β : Bil Y) : Prop := ∀ a, 0 ≤ β a a
def IsPosDefReal (β : Bil Y) : Prop :=
  ∀ (k : ℕ) (a : Fin k → Y), LinearIndependent ℤ a → (Matrix.of fun i j => β (a i) (a j)).PosDef
def IsIntegralFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z
def IsPositiveFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a, 0 ≤ (β : Bil Y) a a) → β ≠ 0 → 0 < l β
def IsAdmissible (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  IsIntegralFn S l ∧ IsPositiveFn S l
def leastExponent (S : Submodule ℝ (Bil Y)) (b : S) : ℝ :=
  sInf {x | ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l ∧ x = l b}
def evalSum (S : Submodule ℝ (Bil Y)) {k : ℕ} (x x' : Fin k → Y) : S →ₗ[ℝ] ℝ where
  toFun β := ∑ i, (β : Bil Y) (x i) (x' i)
  map_add' β γ := by simp [Finset.sum_add_distrib]
  map_smul' r β := by simp [Finset.mul_sum]
def HasShortFrame (β : Bil Y) (r : ℝ) : Prop :=
  ∃ v : Fin (Module.finrank ℤ Y) → Y, LinearIndependent ℤ v ∧ ∀ i, quad β (v i) ≤ r
end Forms
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
def HasTraceOne : Prop := ∃ w : 𝓞 E, w + ringOfIntegersComplexConj E w = 1
def upperConst : ℝ :=
  (|(discr E : ℝ)| ^ ((1 : ℝ) / (2 * (Module.finrank ℚ (maximalRealSubfield E) : ℝ)))) ^ 2 /
    (4 * (Module.finrank ℚ (maximalRealSubfield E) : ℝ))
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
def IsBalanced (β : Bil Y) : Prop :=
  (∀ x y, β x y = β y x) ∧
    ∀ (a : 𝓞 E) (x y : Y), β (a • x) y = β x (ringOfIntegersComplexConj E a • y)
def IsBalancedSpace (S : Submodule ℝ (Bil Y)) : Prop := ∀ β, β ∈ S ↔ IsBalanced E β
def balancedSpace (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] : Submodule ℝ (Bil Y) where
  carrier := {β | IsBalanced E β}
  add_mem' hβ hγ := ⟨fun x y => by simp [hβ.1 x y, hγ.1 x y], fun a x y => by simp [hβ.2 a x y, hγ.2 a x y]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' r β hβ := ⟨fun x y => by simp [hβ.1 x y], fun a x y => by simp [hβ.2 a x y]⟩
def SpansOverField {k : ℕ} (x : Fin k → Y) : Prop :=
  Submodule.span E (Set.range fun b => ((1 : E) ⊗ₜ[𝓞 E] x b : E ⊗[𝓞 E] Y)) = ⊤
def LowerBound (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ β : S, IsPsd (β : Bil Y) → ∀ (k : ℕ) (x : Fin k → Y), SpansOverField E x →
    leastExponent S β ≤ ∑ b, quad (β : Bil Y) (x b)
def UpperBound (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ β : S, IsPosDefReal (β : Bil Y) →
    HasShortFrame (β : Bil Y) (upperConst E * (Module.finrank ℤ Y : ℝ) ^ 2 * leastExponent S β)
def UpperBoundSemidef (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ β : S, IsPsd (β : Bil Y) → ∀ r : ℝ,
    upperConst E * (Module.finrank ℤ Y : ℝ) ^ 2 * leastExponent S β < r → HasShortFrame (β : Bil Y) r
def ReducedBasis (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ β : S, IsPosDefReal (β : Bil Y) →
    ∃ b : Module.Basis (Fin (Module.finrank ℤ Y)) ℤ Y,
      (∀ R : ℝ, upperConst E ≤ R → ∀ j,
        quad (β : Bil Y) (b j) ≤ R * (Module.finrank ℤ Y : ℝ) ^ 3 * leastExponent S β) ∧
      ∀ j z, |(β : Bil Y) (b j) z| ≤ 2 * Real.sqrt (Module.finrank ℤ Y : ℝ) * quad (β : Bil Y) z
omit [NumberField E] [IsCMField E] in

def AdmissibleAreSums (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ l : S →ₗ[ℝ] ℝ, IsAdmissible S l ↔
    IsPositiveFn S l ∧ ∃ (k : ℕ) (x x' : Fin k → Y), l = evalSum S x x'
def pairForm {k : ℕ} (x x' : Fin k → Y) (y y' : Module.Dual (𝓞 E) Y) : 𝓞 E :=
  ∑ i, (y (x i) * ringOfIntegersComplexConj E (y' (x' i)) +
    y (x' i) * ringOfIntegersComplexConj E (y' (x i)))
def IsHermOnDual (h : Module.Dual (𝓞 E) Y → Module.Dual (𝓞 E) Y → 𝓞 E) : Prop :=
  (∀ y₁ y₂ y', h (y₁ + y₂) y' = h y₁ y' + h y₂ y') ∧
  (∀ (a : 𝓞 E) y y', h (a • y) y' = a * h y y') ∧
  ∀ y y', h y' y = ringOfIntegersComplexConj E (h y y')
def IsPosDefOnDual (h : Module.Dual (𝓞 E) Y → Module.Dual (𝓞 E) Y → 𝓞 E) : Prop :=
  ∀ (σ : E →+* ℂ) (y : Module.Dual (𝓞 E) Y), y ≠ 0 → 0 < (σ (h y y : E)).re
def HermitianDictionary (S : Submodule ℝ (Bil Y)) : Prop :=
  (∀ h : Module.Dual (𝓞 E) Y → Module.Dual (𝓞 E) Y → 𝓞 E,
    IsHermOnDual E h ↔ ∃ (k : ℕ) (x x' : Fin k → Y), h = pairForm E x x') ∧
  (∀ (k m : ℕ) (x x' : Fin k → Y) (z z' : Fin m → Y),
    pairForm E x x' = pairForm E z z' ↔ evalSum S x x' = evalSum S z z') ∧
  ∀ (k : ℕ) (x x' : Fin k → Y), IsPosDefOnDual E (pairForm E x x') ↔ IsPositiveFn S (evalSum S x x')
def BoundsAt (S : Submodule ℝ (Bil Y)) : Prop :=
  LowerBound E S ∧ UpperBound E S ∧ UpperBoundSemidef E S ∧ ReducedBasis E S ∧
    AdmissibleAreSums S ∧ HermitianDictionary E S
def LeastExponentBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], HasTraceOne E →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (S : Submodule ℝ (Bil Y)), IsBalancedSpace E S → BoundsAt E S
end GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace


