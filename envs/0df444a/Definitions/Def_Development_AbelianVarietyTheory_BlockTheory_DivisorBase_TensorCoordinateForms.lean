-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorCoordinateForms
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorCoordinateForms
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-27T05:13:49.02869+00:00
-- url     : https://prove2.me/theorems/d31cf086-0c98-4fef-9599-550331cc30d8
-- title:
--   Tensor Coordinate Forms
-- statement:
--   Definitions and structural lemmas for Tensor Coordinate Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TensorCoordinateForms.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms
def dirDeriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) (F : V → ℂ) : V → ℂ :=
  fun z => fderiv ℂ F z v
def wordDeriv {κ V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : κ → V) (w : List κ)
    (F : V → ℂ) : V → ℂ :=
  w.foldr (fun x G => dirDeriv (v x) G) F
def IsSpelling {κ : Type} [DecidableEq κ] (w : (κ → ℕ) → List κ) : Prop :=
  ∀ e x, (w e).count x = e x
def substJet {κ V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (w : (κ → ℕ) → List κ) (v : κ → V) (Rc : (κ → ℕ) →₀ W) (F : V → ℂ) : W :=
  Rc.sum (fun e A => wordDeriv v (w e) F 0 • A)
def lineForm (a : ℝ) (D D' : ℂ) : ℂ := 2 * (a : ℂ) * (D * conj D')
def omega (a : ℝ) (D : ℂ) : ℝ := 1 / (π * (lineForm a D D).re)
def letter (Om : ℝ) (ζ : ℂ) : ℂ := ((Om ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ζ
section OnePlace
variable {X X' : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [FiniteDimensional ℂ X'] {n₀ n₁ : ℕ}
def traceForm (x x' : X →L[ℂ] X') : ℂ :=
  LinearMap.trace ℂ X (LinearMap.adjoint (x' : X →ₗ[ℂ] X') ∘ₗ (x : X →ₗ[ℂ] X'))
def matrixUnit (b : OrthonormalBasis (Fin n₀) ℂ X) (b' : OrthonormalBasis (Fin n₁) ℂ X')
    (p : Fin n₁ × Fin n₀) : X →L[ℂ] X' :=
  (innerSL ℂ (b p.2)).smulRight (b' p.1)
end OnePlace
section Places
variable {Pl : Type} [Fintype Pl] [DecidableEq Pl] {X X' : Pl → Type}
  [∀ τ, NormedAddCommGroup (X τ)] [∀ τ, InnerProductSpace ℂ (X τ)] [∀ τ, FiniteDimensional ℂ (X τ)]
  [∀ τ, NormedAddCommGroup (X' τ)] [∀ τ, InnerProductSpace ℂ (X' τ)] [∀ τ, FiniteDimensional ℂ (X' τ)]
  {n₀ n₁ : ℕ}
def totalForm (a : Pl → ℝ) (z z' : ∀ τ, X τ →L[ℂ] X' τ) : ℂ :=
  2 * ∑ τ, (a τ : ℂ) * traceForm (z τ) (z' τ)
def tensorVec (τ : Pl) (D : ℂ) (x : X τ →L[ℂ] X' τ) : ∀ σ, X σ →L[ℂ] X' σ :=
  Pi.single τ (D • x)
def unitCoord (a : Pl → ℝ) (b : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X τ))
    (b' : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X' τ)) (z : ∀ τ, X τ →L[ℂ] X' τ) :
    Pl × (Fin n₁ × Fin n₀) → ℂ :=
  fun p => (Real.sqrt (2 * π * a p.1) : ℂ) *
    LinearMap.toMatrix (b p.1).toBasis (b' p.1).toBasis (z p.1 : X p.1 →ₗ[ℂ] X' p.1) p.2.1 p.2.2
def ofUnitCoord (a : Pl → ℝ) (b : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X τ))
    (b' : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X' τ)) (u : Pl × (Fin n₁ × Fin n₀) → ℂ) :
    ∀ τ, X τ →L[ℂ] X' τ :=
  fun τ => ∑ q, ((Real.sqrt (2 * π * a τ) : ℂ)⁻¹ * u (τ, q)) • matrixUnit (b τ) (b' τ) q
def frameVec (D : Pl → ℂ) (b : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X τ))
    (b' : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X' τ)) (p : Pl × (Fin n₁ × Fin n₀)) :
    ∀ σ, X σ →L[ℂ] X' σ :=
  tensorVec p.1 (D p.1) (matrixUnit (b p.1) (b' p.1) p.2)
end Places
def coordVec {κ : Type} [DecidableEq κ] (p : κ) : κ → ℂ := Pi.single p 1
def JetFrame : Prop :=
  ∀ (Pl : Type) [Fintype Pl] [DecidableEq Pl] (a : Pl → ℝ) (D : Pl → ℂ),
    (∀ τ, 0 < a τ) → (∀ τ, D τ ≠ 0) →
    ∃ ζ : Pl → ℂ,
      (∀ τ, ‖ζ τ‖ = 1) ∧ (∀ τ, 0 < omega (a τ) (D τ)) ∧
      (∀ τ, ‖letter (omega (a τ) (D τ)) (ζ τ)‖ ^ 2 = (omega (a τ) (D τ))⁻¹) ∧
      ∀ (X X' : Pl → Type)
        [∀ τ, NormedAddCommGroup (X τ)] [∀ τ, InnerProductSpace ℂ (X τ)] [∀ τ, FiniteDimensional ℂ (X τ)]
        [∀ τ, NormedAddCommGroup (X' τ)] [∀ τ, InnerProductSpace ℂ (X' τ)] [∀ τ, FiniteDimensional ℂ (X' τ)]
        (n₀ n₁ : ℕ) (b : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X τ))
        (b' : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X' τ)),
        (∀ u, unitCoord a b b' (ofUnitCoord a b b' u) = u) ∧
        (∀ z, ofUnitCoord a b b' (unitCoord a b b' z) = z) ∧
        (∀ z, ((Formalism.DimensionVariation.nsq (unitCoord a b b' z) : ℝ) : ℂ) = (π : ℂ) * totalForm a z z) ∧
        (∀ (τ : Pl) (d d' : ℂ) (x x' : X τ →L[ℂ] X' τ),
          totalForm a (tensorVec τ d x) (tensorVec τ d' x') = lineForm (a τ) d d' * traceForm x x') ∧
        ∀ Th : (∀ τ, X τ →L[ℂ] X' τ) → ℂ, Differentiable ℂ Th →
          (∀ (p : Pl × (Fin n₁ × Fin n₀)) (z : ∀ τ, X τ →L[ℂ] X' τ),
            dirDeriv (frameVec D b b' p) Th z =
              letter (omega (a p.1) (D p.1)) (ζ p.1) *
                dirDeriv (coordVec p) (Th ∘ ofUnitCoord a b b') (unitCoord a b b' z)) ∧
          ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
            (Rc : (Pl × (Fin n₁ × Fin n₀) → ℕ) →₀ W) (n : Pl → ℕ)
            (w : (Pl × (Fin n₁ × Fin n₀) → ℕ) → List (Pl × (Fin n₁ × Fin n₀))),
            IsSpelling w → (∀ e ∈ Rc.support, ∀ τ, ∑ q, e (τ, q) = n τ) →
            substJet w (frameVec D b b') Rc Th =
                (∏ τ, letter (omega (a τ) (D τ)) (ζ τ) ^ n τ) •
                  substJet w coordVec Rc (Th ∘ ofUnitCoord a b b') ∧
            ∀ c : (Pl × (Fin n₁ × Fin n₀) → ℕ) → ℂ,
              (∀ u, HasSum (fun e => c e * Formalism.DimensionVariation.mono u e) (Th (ofUnitCoord a b b' u))) →
              substJet w (frameVec D b b') Rc Th =
                Formalism.DimensionVariation.liftBlock c Rc (fun τ => letter (omega (a τ) (D τ)) (ζ τ))
example : omega (1 / (2 * π)) 1 = 1 := by
  have h : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have : lineForm (1 / (2 * π)) 1 1 = ((1 / π : ℝ) : ℂ) := by
    have h' : (π : ℂ) ≠ 0 := by exact_mod_cast h
    simp only [lineForm, map_one, mul_one]; push_cast; field_simp
  rw [omega, this, Complex.ofReal_re]; field_simp
end GlobalTheory.IndefiniteRowSideFullHecke.TensorCoordinateForms


