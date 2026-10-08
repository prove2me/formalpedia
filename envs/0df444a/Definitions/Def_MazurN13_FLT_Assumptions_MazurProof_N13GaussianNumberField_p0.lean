-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNumberField_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianNumberField_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:15:45.889528+00:00
-- url     : https://prove2.me/theorems/d0ad8ddf-e441-48b8-899f-9caba12d83a2
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianNumberField source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianNumberField

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianNumberField
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCubicField_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFractionField_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TowerDiscriminant_p0
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

set_option autoImplicit false




/-!
# The absolute N13 number field

The N13 Gaussian cubic is a degree-three extension of the quadratic
Gaussian field.  Combining the structural bases in the two stages gives
the six-element rational basis

`1, α, α², i, iα, iα²`.

This is a tower-basis construction; no embeddings or field elements are
enumerated.
-/

open Algebra Module

namespace MazurProof.N13GaussianNumberField

noncomputable section

open N13GaussianGlobalArithmetic

abbrev K := FractionRing GI

abbrev L := AdjoinRoot N13GaussianCubicField.hK

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField

local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L

/- The subtype algebras otherwise prefer transitive `Subalgebra.algebra`
instances.  For a tower starting at `ℤ`, use the unique canonical integer
algebra structures so their modules are definitionally the usual `zsmul`
modules carried by the explicit bases. -/
local instance intAlgebraGI : Algebra ℤ GI :=
  Ring.toIntAlgebra GI

local instance intAlgebraRelativeIntegers :
    Algebra ℤ (integralClosure GI L) :=
  Ring.toIntAlgebra (integralClosure GI L)

local instance intAlgebraAbsoluteIntegers :
    Algebra ℤ (integralClosure ℤ L) :=
  Ring.toIntAlgebra (integralClosure ℤ L)

/-- The relative `K`-basis `(1, α, α²)`, with a fixed index type. -/
def relativeBasis : Basis (Fin 3) K L :=
  N13GaussianCubicField.powerBasis.basis.reindex
    (finCongr N13GaussianCubicField.powerBasis_dim)

@[simp] theorem relativeBasis_apply (j : Fin 3) :
    relativeBasis j =
      N13GaussianCubicField.alpha ^ (j : ℕ) := by
  rw [relativeBasis, Basis.reindex_apply,
    N13GaussianCubicField.powerBasis.basis_eq_pow]
  have hindex :
      (((finCongr
          N13GaussianCubicField.powerBasis_dim).symm j) :
        ℕ) = (j : ℕ) := rfl
  rw [hindex, N13GaussianCubicField.powerBasis_gen]

/-- The absolute tower basis
`1, α, α², i, iα, iα²`, indexed base-first. -/
def absoluteBasis : Basis (Fin 2 × Fin 3) ℚ L :=
  N13GaussianFractionField.gaussianBasis.smulTower
    relativeBasis

@[simp] theorem absoluteBasis_apply
    (ij : Fin 2 × Fin 3) :
    absoluteBasis ij =
      algebraMap K L
          (N13GaussianFractionField.gaussianBasis ij.1) *
        N13GaussianCubicField.alpha ^ (ij.2 : ℕ) := by
  rw [absoluteBasis, Basis.smulTower_apply,
    Algebra.smul_def, relativeBasis_apply]

instance finiteKL : Module.Finite K L :=
  N13GaussianCubicField.powerBasis.finite

instance finiteQL : Module.Finite ℚ L :=
  Module.Finite.trans K L

instance numberFieldL : NumberField L :=
  NumberField.of_module_finite K L

@[simp] theorem finrank_K_L :
    Module.finrank K L = 3 := by
  rw [Module.finrank_eq_card_basis relativeBasis]
  simp

@[simp] theorem finrank_Q_L :
    Module.finrank ℚ L = 6 := by
  rw [Module.finrank_eq_card_basis absoluteBasis]
  simp

/-- Independent tower-law check of the absolute degree. -/
theorem finrank_Q_L_tower :
    Module.finrank ℚ L =
      Module.finrank ℚ K * Module.finrank K L := by
  exact (Module.finrank_mul_finrank ℚ K L).symm

/-! ## The absolute ring of integers -/

/-- For an integral scalar extension `R → S`, integrality over `R` and
over `S` cut out the same subring in the top algebra. -/
theorem integralClosure_toSubring_eq_of_isIntegral
    {R S A : Type*}
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Algebra R A]
    [IsScalarTower R S A] [Algebra.IsIntegral R S] :
    (integralClosure R A).toSubring =
      (integralClosure S A).toSubring := by
  ext x
  change IsIntegral R x ↔ IsIntegral S x
  constructor
  · exact IsIntegral.tower_top
  · intro hx
    exact isIntegral_trans x hx

/-- Absolute and Gaussian-relative integral elements in `L` have the same
underlying carrier. -/
theorem absoluteIntegralClosure_toSubring_eq :
    (integralClosure ℤ L).toSubring =
      (integralClosure GI L).toSubring :=
  integralClosure_toSubring_eq_of_isIntegral
    (R := ℤ) (S := GI) (A := L)

/-- Change only the proof that an element of `L` is integral.  Since the
underlying carrier map is the identity, this is an algebra equivalence. -/
def relativeToAbsoluteAlgEquiv :
    integralClosure GI L ≃ₐ[ℤ] integralClosure ℤ L where
  toFun x := ⟨x.1, isIntegral_trans x.1 x.2⟩
  invFun x := ⟨x.1, x.2.tower_top⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The linear equivalence underlying the carrier-preserving algebra
equivalence. -/
def relativeToAbsoluteLinearEquiv :
    integralClosure GI L ≃ₗ[ℤ] integralClosure ℤ L :=
  relativeToAbsoluteAlgEquiv.toAddEquiv.toIntLinearEquiv

/-- The absolute integral basis obtained by composing the Gaussian integral
basis with the relative cubic integral basis. -/
def absoluteIntegralBasis :
    Basis (Fin 2 × Fin 3) ℤ (integralClosure ℤ L) :=
  (N13GaussianFractionField.gaussianIntBasis.smulTower
      N13GaussianCubicField.relativeIntegralBasis).map
    relativeToAbsoluteLinearEquiv

@[simp] theorem coe_absoluteIntegralBasis_apply
    (ij : Fin 2 × Fin 3) :
    ((absoluteIntegralBasis ij :
        integralClosure ℤ L) : L) =
      algebraMap GI L
          (N13GaussianFractionField.gaussianIntBasis ij.1) *
        N13GaussianCubicField.alpha ^ (ij.2 : ℕ) := by
  simp [absoluteIntegralBasis, relativeToAbsoluteLinearEquiv,
    relativeToAbsoluteAlgEquiv, Algebra.smul_def]

/- Mathlib packages the ring of integers as a separate definition rather
than exposing the integral-closure subtype directly.  This carrier-preserving
equivalence is the explicit bridge between the two presentations. -/
def integralClosureToRingOfIntegersRingEquiv :
    integralClosure ℤ L ≃+*
      NumberField.RingOfIntegers L :=
  (NumberField.RingOfIntegers.equiv
    (integralClosure ℤ L)).symm

/-- The carrier-preserving bridge respects the canonical integer algebra
structures. -/
def integralClosureToRingOfIntegersAlgEquiv :
    integralClosure ℤ L ≃ₐ[ℤ]
      NumberField.RingOfIntegers L :=
  AlgEquiv.ofRingEquiv
    (f := integralClosureToRingOfIntegersRingEquiv)
    (fun z => by simp)

/-- The explicit integral basis, transported to Mathlib's performance-oriented
`RingOfIntegers` wrapper. -/
def absoluteRingOfIntegersBasis :
    Basis (Fin 2 × Fin 3) ℤ
      (NumberField.RingOfIntegers L) :=
  absoluteIntegralBasis.map
    integralClosureToRingOfIntegersAlgEquiv.toAddEquiv.toIntLinearEquiv

/-! ## Absolute discriminant -/

/-- The tower basis before changing the integral-closure subtype has the
absolute discriminant `-10816`. -/
theorem relativeTowerBasis_discr :
    Algebra.discr ℤ
      (N13GaussianFractionField.gaussianIntBasis.smulTower
        N13GaussianCubicField.relativeIntegralBasis) =
      -10816 := by
  rw [TowerDiscriminant.discr_smulTower,
    N13GaussianFractionField.discr_gaussianIntBasis,
    N13GaussianCubicField.relativeIntegralBasis_discr]
  simp only [Fintype.card_fin,
    N13GaussianFractionField.algebraNorm_pi_sq]
  norm_num

/-- Discriminant of the explicit absolute integral basis. -/
@[simp] theorem absoluteIntegralBasis_discr :
    Algebra.discr ℤ absoluteIntegralBasis = -10816 := by
  calc
    Algebra.discr ℤ absoluteIntegralBasis =
        Algebra.discr ℤ
          (N13GaussianFractionField.gaussianIntBasis.smulTower
            N13GaussianCubicField.relativeIntegralBasis) := by
      symm
      have hfun :
          (relativeToAbsoluteAlgEquiv ∘
              (N13GaussianFractionField.gaussianIntBasis.smulTower
                N13GaussianCubicField.relativeIntegralBasis :
                Fin 2 × Fin 3 →
                  integralClosure GI L)) =
            (absoluteIntegralBasis :
              Fin 2 × Fin 3 → integralClosure ℤ L) := by
        funext ij
        rfl
      have hdisc :=
        Algebra.discr_eq_discr_of_algEquiv
          (N13GaussianFractionField.gaussianIntBasis.smulTower
            N13GaussianCubicField.relativeIntegralBasis)
          relativeToAbsoluteAlgEquiv
      rw [hfun] at hdisc
      exact hdisc
    _ = -10816 := relativeTowerBasis_discr

/-- Discriminant of the same basis in Mathlib's `RingOfIntegers` wrapper. -/
@[simp] theorem absoluteRingOfIntegersBasis_discr :
    Algebra.discr ℤ absoluteRingOfIntegersBasis = -10816 := by
  calc
    Algebra.discr ℤ absoluteRingOfIntegersBasis =
        Algebra.discr ℤ absoluteIntegralBasis := by
      symm
      have hfun :
          (integralClosureToRingOfIntegersAlgEquiv ∘
              (absoluteIntegralBasis :
                Fin 2 × Fin 3 → integralClosure ℤ L)) =
            (absoluteRingOfIntegersBasis :
              Fin 2 × Fin 3 →
                NumberField.RingOfIntegers L) := by
        funext ij
        rfl
      have hdisc :=
        Algebra.discr_eq_discr_of_algEquiv
          absoluteIntegralBasis
          integralClosureToRingOfIntegersAlgEquiv
      rw [hfun] at hdisc
      exact hdisc
    _ = -10816 := absoluteIntegralBasis_discr

/-- The absolute number-field discriminant. -/
@[simp] theorem numberField_discr :
    NumberField.discr L = -10816 := by
  have hcanonical :=
    NumberField.discr_eq_discr L
      absoluteRingOfIntegersBasis
  rw [← hcanonical]
  exact absoluteRingOfIntegersBasis_discr

end

end MazurProof.N13GaussianNumberField


