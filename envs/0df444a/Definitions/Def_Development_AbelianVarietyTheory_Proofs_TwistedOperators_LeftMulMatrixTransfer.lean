-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:26.219288+00:00
-- url     : https://prove2.me/theorems/683a0d8a-c82e-4762-823a-8e0ab3b182f0
-- title:
--   Left Mul Matrix Transfer
-- statement:
--   Definitions and structural lemmas for Left Mul Matrix Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
namespace GlobalTheory.ClassParam
section Cyclic
def krylov {A : Type} [CommRing A] {r : ℕ} (g : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    Matrix (Fin r) (Fin r) A := Matrix.of fun i j => ((g ^ (j : ℕ)) *ᵥ v) i
end Cyclic
section Transfer
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S]
  [Algebra A B] {ι : Type} [Fintype ι] [DecidableEq ι]
end Transfer
section Forms
variable {A : Type} [CommRing A] {r : ℕ} (σ : A →+* A)
theorem hform_eq (J : Matrix (Fin r) (Fin r) A) (x y : Fin r → A) :
    hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
def hlin (J : Matrix (Fin r) (Fin r) A) (x : Fin r → A) : (Fin r → A) →ₗ[A] A where
  toFun y := hform σ J x y
  map_add' y z := by simp [hform_eq, Matrix.mulVec_add]
  map_smul' a y := by simp [hform_eq, Matrix.mulVec_smul]
end Forms
section Core
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
structure HidaSetting (σ : A →+* A) (τ : B →+* B) (α : B) (b : Module.Basis (Fin r) A B) : Prop where
  hσ : ∀ a, σ (σ a) = a
  hτ : ∀ y, τ (τ y) = y
  comp : ∀ a, τ (algebraMap A B a) = algebraMap A B (σ a)
  hα : α * τ α = 1
  pow : ∀ i, b i = α ^ (i : ℕ)
  perf : IsUnit (Algebra.traceMatrix A b).det
def tf (A : Type) [CommRing A] [Algebra A B] (τ : B →+* B) (x y y' : B) : A :=
  Algebra.trace A B (x * y * τ y')
def Iso (σ : A →+* A) (τ : B →+* B) (J : Matrix (Fin r) (Fin r) A) (x : B)
    (φ : B ≃ₗ[A] (Fin r → A)) : Prop :=
  ∀ y y', hform σ J (φ y') (φ y) = tf A τ x y y'
def Intw (α : B) (g : Matrix (Fin r) (Fin r) A) (φ : B ≃ₗ[A] (Fin r → A)) : Prop :=
  ∀ u, g *ᵥ u = φ (α * φ.symm u)
variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}
def HidaSetting.pb (S : HidaSetting σ τ α b) : PowerBasis A B := ⟨α, r, b, S.pow⟩
def mulUnit (A : Type) [CommRing A] [Algebra A B] (z : Bˣ) : B ≃ₗ[A] B :=
  LinearEquiv.ofLinear (LinearMap.mulLeft A (z : B)) (LinearMap.mulLeft A ((z⁻¹ : Bˣ) : B))
    (by ext; simp) (by ext; simp)
def gram (τ : B →+* B) (x : B) (e : Module.Basis (Fin r) A B) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun i j => tf A τ x (e i) (e j)
end Core
section Concrete
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
end Concrete
end GlobalTheory.ClassParam


