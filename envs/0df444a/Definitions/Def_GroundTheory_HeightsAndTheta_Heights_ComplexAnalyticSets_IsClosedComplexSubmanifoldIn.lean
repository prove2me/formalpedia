-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:26.040167+00:00
-- url     : https://prove2.me/theorems/384f5d09-ceab-4829-9635-43eb5a224837
-- title:
--   Is Closed Complex Submanifold In
-- statement:
--   Definitions and structural lemmas for Is Closed Complex Submanifold In, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/IsClosedComplexSubmanifoldIn.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Pointwise
variable {n d : ℕ}
def linPoly (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (A (Pi.single j 1) i) * X j
def projAlgHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  aeval fun i => Ideal.Quotient.mk J (linPoly A i)
def IsFiniteProjection (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) : Prop :=
  Function.Injective (projAlgHom J A) ∧ (projAlgHom J A).toRingHom.Finite
def projDegree (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) : ℕ :=
  Module.finrank
    (IntermediateField.adjoin ℂ (Set.range fun i =>
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
        (projAlgHom J A (X i))))
    (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
def projFibre (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (y : Fin d → ℂ) : Set (Fin n → ℂ) :=
  zeroLocus ℂ J ∩ A ⁻¹' {y}
def pullPoly (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (P : MvPolynomial (Fin d) ℂ) :
    MvPolynomial (Fin n) ℂ :=
  aeval (linPoly A) P
def unitaryRows (d n : ℕ) : Set (Matrix (Fin d) (Fin n) ℂ) :=
  {M | M * M.conjTranspose = 1}
def IsClosedComplexSubmanifoldIn (S Ω : Set (Fin n → ℂ)) (k : ℕ) : Prop :=
  S ⊆ Ω ∧ IsClosed ((↑) ⁻¹' S : Set Ω) ∧
    ∀ z ∈ S, ∃ (V : Set (Fin n → ℂ)) (U : Set (Fin k → ℂ)) (π : (Fin n → ℂ) →L[ℂ] (Fin k → ℂ))
      (g : (Fin k → ℂ) → (Fin n → ℂ)),
      IsOpen V ∧ z ∈ V ∧ IsOpen U ∧ DifferentiableOn ℂ g U ∧ (∀ y ∈ U, π (g y) = y) ∧
        S ∩ V = g '' U
def GenericProjectionFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    (∃ S : Set (MvPolynomial (Fin d × Fin n) ℂ),
        (∃ M : Matrix (Fin d) (Fin n) ℂ, ∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) ∧
        ∀ M : Matrix (Fin d) (Fin n) ℂ,
          (∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) → IsFiniteProjection J M.mulVecLin) ∧
      (∃ M : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J M.mulVecLin) ∧
      (∀ D ⊆ unitaryRows d n, unitaryRows d n ⊆ closure D →
        ∃ M ∈ D, IsFiniteProjection J M.mulVecLin) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) ℂ),
        (∀ k, F k ∈ Matrix.unitaryGroup (Fin n) ℂ) →
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((U * F k).conjTranspose.submatrix s id).mulVecLin))
def FibreBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime],
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ), IsFiniteProjection J A →
    ∀ y : Fin d → ℂ, (projFibre J A y).Nonempty ∧ (projFibre J A y).encard ≤ projDegree J A
def DiscriminantCover.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime],
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ), IsFiniteProjection J A →
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      (∀ y : Fin d → ℂ, eval y P ≠ 0 →
        (projFibre J A y).encard = projDegree J A ∧
        ∀ z ∈ projFibre J A y, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
          (g : (Fin d → ℂ) → (Fin n → ℂ)),
          IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ z ∈ V ∧ DifferentiableOn ℂ g U ∧ g y = z ∧
            (∀ y' ∈ U, A (g y') = y') ∧ zeroLocus ℂ J ∩ V = g '' U) ∧
      IsClosedComplexSubmanifoldIn (zeroLocus ℂ J \ A ⁻¹' {y | eval y P = 0})
        (A ⁻¹' {y | eval y P = 0})ᶜ d
def BadSetSmaller.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ), IsFiniteProjection J A →
    ∀ P : MvPolynomial (Fin d) ℂ, P ≠ 0 →
      zeroLocus ℂ J ∩ A ⁻¹' {y | eval y P = 0} =
          zeroLocus ℂ (J ⊔ Ideal.span {pullPoly A P}) ∧
        ∀ Q ∈ (J ⊔ Ideal.span {pullPoly A P}).minimalPrimes,
          ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) < d
def ConeScaling.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), ReciprocityTheory.ChartRestriction.G.Geo.IsHomogIdeal ℂ J →
    ∀ t : ℂ, t ≠ 0 → t • zeroLocus ℂ J = zeroLocus ℂ J
def lineMap : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  aeval ![X 0, 0]
def lineIdeal : Ideal (MvPolynomial (Fin 2) ℂ) := RingHom.ker lineMap
theorem lineMap_surjective : Function.Surjective lineMap := by
  intro p
  refine ⟨rename (fun _ : Fin 1 => (0 : Fin 2)) p, ?_⟩
  have h : ((![X 0, 0] : Fin 2 → MvPolynomial (Fin 1) ℂ) ∘ fun _ : Fin 1 => (0 : Fin 2)) = X := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  simp only [lineMap, aeval_rename, h, aeval_X_left_apply]
instance lineIdeal_isPrime : lineIdeal.IsPrime := RingHom.ker_isPrime _
def lineEquiv : (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.quotientKerAlgEquivOfSurjective lineMap_surjective
theorem lineIdeal_dim : ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) = (1 : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv lineEquiv.toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
def lineProj : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := LinearMap.pi fun _ => LinearMap.proj 0
theorem lineEquiv_projAlgHom (p : MvPolynomial (Fin 1) ℂ) :
    lineEquiv (projAlgHom lineIdeal lineProj p) = p := by
  have h : (lineEquiv.toAlgHom.comp (projAlgHom lineIdeal lineProj)) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [Fin.fin_one_eq_zero i]
    simp [projAlgHom, lineEquiv, linPoly, lineProj, lineMap, Fin.sum_univ_two]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk lineMap_surjective (X 0)).trans
      (by simp [lineMap])
  exact congrArg (fun f => f p) h
theorem lineProj_finite : IsFiniteProjection lineIdeal lineProj := by
  have hinj : Function.Injective (projAlgHom lineIdeal lineProj) :=
    Function.LeftInverse.injective lineEquiv_projAlgHom
  have hsurj : Function.Surjective (projAlgHom lineIdeal lineProj) := by
    intro q
    refine ⟨lineEquiv q, lineEquiv.injective ?_⟩
    rw [lineEquiv_projAlgHom]
  exact ⟨hinj, RingHom.Finite.of_surjective _ hsurj⟩
example : lineIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) = (1 : ℕ) :=
  ⟨inferInstance, lineIdeal_dim⟩
example : lineIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) = (1 : ℕ) ∧
    IsFiniteProjection lineIdeal lineProj ∧ (X 0 : MvPolynomial (Fin 1) ℂ) ≠ 0 :=
  ⟨inferInstance, lineIdeal_dim, lineProj_finite, X_ne_zero _⟩
def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval (0 : Fin n → ℂ))
example : X 0 ∈ originIdeal 1 ∧ (1 : MvPolynomial (Fin 1) ℂ) ∉ originIdeal 1 := by
  simp [originIdeal]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


