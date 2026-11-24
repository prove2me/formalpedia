-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:06.65626+00:00
-- url     : https://prove2.me/theorems/6efa0224-fee0-491f-a89a-2e442ebe0fbd
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
def zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}
def linPoly (A : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (A i j) * X j
def pullback (A : Matrix (Fin d) (Fin n) ℂ) : MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (linPoly A)
def projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  (Ideal.Quotient.mkₐ ℂ J).comp (pullback A)
structure IsFiniteProjection (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    Prop where

  injective : Function.Injective (projHom J A)

  finite : (projHom J A).toRingHom.Finite
def projDegree (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) : ℕ :=
  letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  Module.finrank (FractionRing (MvPolynomial (Fin d) ℂ))
    (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J))
def fibre (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (y : Fin d → ℂ) :
    Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ A.mulVec x = y}
def IsZariskiOpen (U : Set (Matrix (Fin d) (Fin n) ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin d × Fin n) ℂ),
    U = {A | ∃ p ∈ S, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0}
def orthoRows (d n : ℕ) : Set (Matrix (Fin d) (Fin n) ℂ) :=
  {A | A * A.conjTranspose = 1}
def GenericProjectionFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      (∃ U : Set (Matrix (Fin d) (Fin n) ℂ), IsZariskiOpen U ∧ U.Nonempty ∧
        ∀ A ∈ U, IsFiniteProjection J A) ∧
      {A : Matrix (Fin d) (Fin n) ℂ | IsFiniteProjection J A}.Nonempty ∧
      (∀ D : Set (Matrix (Fin d) (Fin n) ℂ), D ⊆ orthoRows d n → orthoRows d n ⊆ closure D →
        ∃ A ∈ D, IsFiniteProjection J A) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix.unitaryGroup (Fin n) ℂ),
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((F k : Matrix (Fin n) (Fin n) ℂ) * U).submatrix s id))
def FibreBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ y : Fin d → ℂ, (fibre J A y).Nonempty ∧ (fibre J A y).Finite ∧
        (fibre J A y).ncard ≤ projDegree J A
def DiscriminantCover.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y P ≠ 0 →
        (fibre J A y).Finite ∧ (fibre J A y).ncard = projDegree J A ∧
        ∀ x ∈ fibre J A y, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
          (g : (Fin d → ℂ) → (Fin n → ℂ)), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A.mulVec (g w) = w) ∧
            zeroSet J ∩ V = g '' U
def BadSetSmaller.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ P : MvPolynomial (Fin d) ℂ, P ≠ 0 →
        zeroSet (J ⊔ Ideal.span {pullback A P}) = zeroSet J ∩ {x | eval (A.mulVec x) P = 0} ∧
        ∀ Q ∈ (J ⊔ Ideal.span {pullback A P}).minimalPrimes,
          ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) < d
attribute [local instance] MvPolynomial.gradedAlgebra in

def ConeScaling.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) →
    ∀ t : ℂ, t ≠ 0 → t • zeroSet J = zeroSet J
section Inhabitants
def coneEq : MvPolynomial (Fin 3) ℂ := X 0 ^ 2 - X 1 * X 2
def coneIdeal : Ideal (MvPolynomial (Fin 3) ℂ) := Ideal.span {coneEq}
def coneProj : Matrix (Fin 2) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 1]
theorem finSuccEquiv_coneEq :
    finSuccEquiv ℂ 2 coneEq = Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1) := by
  have h1 : (X 1 : MvPolynomial (Fin 3) ℂ) = X (Fin.succ 0) := rfl
  have h2 : (X 2 : MvPolynomial (Fin 3) ℂ) = X (Fin.succ 1) := rfl
  rw [coneEq, h1, h2, map_sub, map_pow, map_mul, finSuccEquiv_X_zero, finSuccEquiv_X_succ,
    finSuccEquiv_X_succ, Polynomial.C_mul]
def coneMinPoly : Polynomial (MvPolynomial (Fin 2) ℂ) := Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1)
def coneQuotEquiv : (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) ≃+* AdjoinRoot coneMinPoly :=
  Ideal.quotientEquiv coneIdeal (Ideal.span {coneMinPoly}) (finSuccEquiv ℂ 2).toRingEquiv (by
    rw [coneIdeal, Ideal.map_span]
    congr 1
    simp only [Set.image_singleton]
    congr 1
    exact (finSuccEquiv_coneEq).symm)
end Inhabitants
end
end GroundTheory.Heights₂.Heights.ComplexSets


