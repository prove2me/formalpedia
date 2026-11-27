-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TaylorCoefficientForms
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TaylorCoefficientForms
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-27T05:13:33.964889+00:00
-- url     : https://prove2.me/theorems/ac5571db-4547-41eb-8f31-b054585496df
-- title:
--   Taylor Coefficient Forms
-- statement:
--   Definitions and structural lemmas for Taylor Coefficient Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TaylorCoefficientForms.lean

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate Real
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms
open Formalism.DimensionVariation (mono mfact nsq liftBlock)
section Calculus
variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype κ]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
def dirDeriv (v : E) (F : E → ℂ) : E → ℂ := fun z => fderiv ℂ F z v
def monoDeriv (v : κ → E) (e : κ → ℕ) (F : E → ℂ) : E → ℂ :=
  (univ : Finset κ).toList.foldr (fun x G => (dirDeriv (v x))^[e x] G) F
def polyJet (v : κ → E) (Rc : (κ → ℕ) →₀ W) (F : E → ℂ) : W :=
  Rc.sum fun e A => monoDeriv v e F 0 • A
open Classical in

def coordVec (x : κ) : κ → ℂ := Pi.single x 1
def taylorCoeff (F : (κ → ℂ) → ℂ) (e : κ → ℕ) : ℂ :=
  monoDeriv coordVec e F 0 / (mfact e : ℂ)
end Calculus
def lineForm (ξ D D' : ℂ) : ℂ := 2 * (‖ξ‖ : ℂ) * (D * conj D')
def period (ξ D : ℂ) : ℝ := 1 / (π * (lineForm ξ D D).re)
def unitScale (ξ : ℂ) : ℝ := Real.sqrt (2 * π * ‖ξ‖)
section OnePlace
variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B] {n₀ n₁ : ℕ}
def homForm (x x' : A →L[ℂ] B) : ℂ :=
  LinearMap.trace ℂ A (LinearMap.adjoint (x' : A →ₗ[ℂ] B) ∘ₗ (x : A →ₗ[ℂ] B))
def matUnit (b₀ : OrthonormalBasis (Fin n₀) ℂ A) (b₁ : OrthonormalBasis (Fin n₁) ℂ B)
    (p : Fin n₁ × Fin n₀) : A →L[ℂ] B :=
  (innerSL ℂ (b₀ p.2)).smulRight (b₁ p.1)
def matEntry (b₀ : OrthonormalBasis (Fin n₀) ℂ A) (b₁ : OrthonormalBasis (Fin n₁) ℂ B)
    (x : A →L[ℂ] B) (p : Fin n₁ × Fin n₀) : ℂ :=
  b₁.repr (x (b₀ p.2)) p.1
end OnePlace
section AllPlaces
variable {Pl : Type} [Fintype Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ}
def bigForm (ξ : Pl → ℂ) (z z' : ∀ τ, X₀ τ →L[ℂ] X₁ τ) : ℂ :=
  2 * ∑ τ, (‖ξ τ‖ : ℂ) * homForm (z τ) (z' τ)
open Classical in

def letterTensor (τ : Pl) (D : ℂ) (x : X₀ τ →L[ℂ] X₁ τ) : ∀ σ, X₀ σ →L[ℂ] X₁ σ :=
  Pi.single (M := fun σ => X₀ σ →L[ℂ] X₁ σ) τ (D • x)
def letterUnit (D : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
    (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) (x : Pl × (Fin n₁ × Fin n₀)) :
    ∀ σ, X₀ σ →L[ℂ] X₁ σ :=
  letterTensor x.1 (D x.1) (matUnit (b₀ x.1) (b₁ x.1) x.2)
def unitCoord (ξ : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
    (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) (z : ∀ τ, X₀ τ →L[ℂ] X₁ τ) :
    Pl × (Fin n₁ × Fin n₀) → ℂ :=
  fun x => (unitScale (ξ x.1) : ℂ) * matEntry (b₀ x.1) (b₁ x.1) (z x.1) x.2
def ofUnitCoord (ξ : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
    (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) (u : Pl × (Fin n₁ × Fin n₀) → ℂ) :
    ∀ τ, X₀ τ →L[ℂ] X₁ τ :=
  fun τ => ∑ p, (u (τ, p) / (unitScale (ξ τ) : ℂ)) • matUnit (b₀ τ) (b₁ τ) p
end AllPlaces
def JetFrame : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (ξ D : Pl → ℂ), (∀ τ, ξ τ ≠ 0) → (∀ τ, D τ ≠ 0) →
    (∀ τ, 0 < period (ξ τ) (D τ)) ∧
    ∃ lam : Pl → ℂ, (∀ τ, ‖lam τ‖ ^ 2 = (period (ξ τ) (D τ))⁻¹) ∧
      ∀ (X₀ X₁ : Pl → Type)
        [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)]
        [∀ τ, FiniteDimensional ℂ (X₀ τ)]
        [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)]
        [∀ τ, FiniteDimensional ℂ (X₁ τ)]
        (n₀ n₁ : ℕ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
        (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)),
        (∀ z, ofUnitCoord ξ b₀ b₁ (unitCoord ξ b₀ b₁ z) = z) ∧
        (∀ u, unitCoord ξ b₀ b₁ (ofUnitCoord ξ b₀ b₁ u) = u) ∧
        (∀ z, (nsq (unitCoord ξ b₀ b₁ z) : ℂ) = π * bigForm ξ z z) ∧
        (∀ (τ : Pl) (d d' : ℂ) (x x' : X₀ τ →L[ℂ] X₁ τ),
          bigForm ξ (letterTensor τ d x) (letterTensor τ d' x') = lineForm (ξ τ) d d' * homForm x x') ∧
        ∀ Θ : (∀ τ, X₀ τ →L[ℂ] X₁ τ) → ℂ, Differentiable ℂ Θ →
          (∀ (x : Pl × (Fin n₁ × Fin n₀)) (z : ∀ τ, X₀ τ →L[ℂ] X₁ τ),
            dirDeriv (letterUnit D b₀ b₁ x) Θ z =
              lam x.1 * dirDeriv (coordVec x) (Θ ∘ ofUnitCoord ξ b₀ b₁) (unitCoord ξ b₀ b₁ z)) ∧
          (∀ u, HasSum (fun e => taylorCoeff (Θ ∘ ofUnitCoord ξ b₀ b₁) e * mono u e)
            (Θ (ofUnitCoord ξ b₀ b₁ u))) ∧
          ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] (n : Pl → ℕ)
            (Rc : (Pl × (Fin n₁ × Fin n₀) → ℕ) →₀ W),
            (∀ e ∈ Rc.support, ∀ τ, ∑ p, e (τ, p) = n τ) →
            polyJet (letterUnit D b₀ b₁) Rc Θ =
                (∏ τ, lam τ ^ n τ) • polyJet coordVec Rc (Θ ∘ ofUnitCoord ξ b₀ b₁) ∧
              polyJet (letterUnit D b₀ b₁) Rc Θ =
                liftBlock (taylorCoeff (Θ ∘ ofUnitCoord ξ b₀ b₁)) Rc lam ∧
              ∀ c : (Pl × (Fin n₁ × Fin n₀) → ℕ) → ℂ,
                (∀ u, HasSum (fun e => c e * mono u e) (Θ (ofUnitCoord ξ b₀ b₁ u))) →
                polyJet (letterUnit D b₀ b₁) Rc Θ = liftBlock c Rc lam
example (ξ D : ℂ) : period ξ D = 1 / (π * (2 * ‖ξ‖ * ‖D‖ ^ 2)) := by
  have : lineForm ξ D D = ((2 * ‖ξ‖ * ‖D‖ ^ 2 : ℝ) : ℂ) := by
    simp [lineForm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [period, this, Complex.ofReal_re]
example {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype κ] (v : κ → E) (F : E → ℂ) :
    monoDeriv v 0 F = F := by
  unfold monoDeriv
  induction (univ : Finset κ).toList with
  | nil => rfl
  | cons a l ih => simpa using ih
end GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms


