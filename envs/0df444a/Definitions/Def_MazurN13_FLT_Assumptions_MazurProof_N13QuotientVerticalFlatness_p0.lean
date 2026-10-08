-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuotientVerticalFlatness_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13QuotientVerticalFlatness_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:09:47.942989+00:00
-- url     : https://prove2.me/theorems/17278853-8a74-41c3-93ac-3f5bf7d7e8c6
-- title:
--   FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13QuotientVerticalFlatness
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralModelContraction_p0
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false




/-!
# Vertical saturation gives flat N13 quotients

The canonical contraction of a generic ideal is saturated with respect to
every nonzero two-adic scalar.  Consequently its affine quotient has no
two-adic torsion.  Since the two-adic integers form a Dedekind domain, the
quotient is flat even before finiteness has been established.

This separates the easy vertical part of the two-fibre argument from the
genuine no-escape/finiteness step.
-/

namespace MazurProof.N13QuotientVerticalFlatness

noncomputable section

universe uR uA

variable {R : Type uR} {A : Type uA}
variable [CommRing R] [IsDomain R]
variable [CommRing A] [Algebra R A]

/--
An ideal saturated with respect to every nonzero base scalar has a
torsion-free quotient over the base.
-/
theorem quotient_isTorsionFree_of_scalar_saturated
    (I : Ideal A)
    (hsaturated :
      ∀ (r : R), r ≠ 0 →
        ∀ a : A, algebraMap R A r * a ∈ I → a ∈ I) :
    Module.IsTorsionFree R (A ⧸ I) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r z hrz
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hsaturated r hr a
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    change
      algebraMap R (A ⧸ I) r *
          Ideal.Quotient.mk I a = 0
    simpa only [Algebra.smul_def] using hrz

/-- Torsion-freeness of an ideal quotient recovers cancellation by every
nonzero scalar from the base domain.

Together with `quotient_isTorsionFree_of_scalar_saturated`, this identifies
vertical saturation exactly with relative torsion-freeness of the quotient;
there is no additional ideal-theoretic hypothesis hidden in that change of
language. -/
theorem scalar_saturated_of_quotient_isTorsionFree
    (I : Ideal A)
    (hfree : Module.IsTorsionFree R (A ⧸ I)) :
    ∀ (r : R), r ≠ 0 →
      ∀ a : A, algebraMap R A r * a ∈ I → a ∈ I := by
  letI : Module.IsTorsionFree R (A ⧸ I) := hfree
  intro r hr a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hzero :
      r • Ideal.Quotient.mk I a = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [Algebra.smul_def] using ha
  exact (smul_eq_zero.mp hzero).resolve_left hr

/-- Vertical scalar saturation is equivalent to torsion-freeness of the
quotient module over the base domain. -/
theorem scalar_saturated_iff_quotient_isTorsionFree
    (I : Ideal A) :
    (∀ (r : R), r ≠ 0 →
        ∀ a : A, algebraMap R A r * a ∈ I → a ∈ I) ↔
      Module.IsTorsionFree R (A ⧸ I) := by
  constructor
  · exact quotient_isTorsionFree_of_scalar_saturated I
  · exact scalar_saturated_of_quotient_isTorsionFree I

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

/-- The quotient by a canonical vertical contraction is two-adically
torsion-free. -/
theorem contractQuotient_isTorsionFree
    (J : Ideal RationalRing) :
    Module.IsTorsionFree R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) := by
  apply quotient_isTorsionFree_of_scalar_saturated
  intro r hr a ha
  exact
    N13IntegralModelContraction.contractIdeal_vertical_saturated
      J r hr ha

/-- Over the two-adic DVR the same quotient is flat, with no finiteness
assumption. -/
theorem contractQuotient_flat
    (J : Ideal RationalRing) :
    Module.Flat R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) := by
  letI :
      Module.IsTorsionFree R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal J) :=
    contractQuotient_isTorsionFree J
  infer_instance

end

end MazurProof.N13QuotientVerticalFlatness


