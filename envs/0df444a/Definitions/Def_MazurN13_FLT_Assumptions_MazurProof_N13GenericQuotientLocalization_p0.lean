-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GenericQuotientLocalization_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GenericQuotientLocalization_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T23:58:57.474251+00:00
-- url     : https://prove2.me/theorems/1be4cb61-4f9d-45c9-9692-3124747e39f4
-- title:
--   FLT.Assumptions.MazurProof.N13GenericQuotientLocalization source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GenericQuotientLocalization

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GenericQuotientLocalization
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CanonicalContractionQuotient_p0
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Dimension.Localization

set_option autoImplicit false




/-!
# The generic fibre of a canonical N13 contraction

The quotient by a canonical vertical contraction becomes the original
Mumford quotient after inverting the nonzero two-adic scalars.  Consequently,
a contracted quadratic Mumford quotient has rank two over the two-adic
integers.  No preferred integral basis is used.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13GenericQuotientLocalization

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralModelContraction.R₂
abbrev Q₂ : Type := N13IntegralModelContraction.Q₂
abbrev IntegralRing : Type := N13IntegralModelContraction.IntegralRing
abbrev RationalRing : Type := N13IntegralModelContraction.RationalRing
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization

/-- The generic quotient map as a two-adic algebra homomorphism. -/
def genericQuotientAlgHom (J : Ideal RationalRing) :
    (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) →ₐ[R₂]
      (RationalRing ⧸ J) where
  toRingHom :=
    N13CanonicalContractionQuotient.genericQuotientMap J
  commutes' r :=
    DFunLike.congr_fun
      (N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap J)
      r

/-- The generic quotient map is localization at the nonzero two-adic
scalars. -/
theorem genericQuotient_isLocalized
    (J : Ideal RationalRing) :
    IsLocalizedModule (nonZeroDivisors R₂)
      (genericQuotientAlgHom J).toLinearMap := by
  let B :=
    IntegralRing ⧸
      N13IntegralModelContraction.contractIdeal J
  let G := RationalRing ⧸ J
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro s
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hs :
          algebraMap R₂ Q₂ (s : R₂) ≠ 0 := by
        exact
          (IsFractionRing.injective R₂ Q₂).ne
            (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
      apply_fun
        (fun z : G ↦
          (algebraMap R₂ Q₂ (s : R₂))⁻¹ • z) at hxy
      simpa [Module.algebraMap_end_apply,
        ← IsScalarTower.algebraMap_smul Q₂, hs] using hxy
    · intro y
      let c : Q₂ := algebraMap R₂ Q₂ (s : R₂)
      have hc : c ≠ 0 := by
        exact
          (IsFractionRing.injective R₂ Q₂).ne
            (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
      refine ⟨c⁻¹ • y, ?_⟩
      change c • (c⁻¹ • y) = y
      exact smul_inv_smul₀ hc y
  · intro y
    obtain ⟨z, rfl⟩ :=
      Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, s⟩, hz⟩ :=
      IsLocalization.surj
        N13IntegralModelContraction.verticalScalars z
    obtain ⟨r, hr, hs⟩ := s.property
    refine
      ⟨⟨Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a,
          ⟨r, hr⟩⟩,
        ?_⟩
    change
      r • Ideal.Quotient.mk J z =
        N13CanonicalContractionQuotient.genericQuotientMap J
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a)
    rw [N13CanonicalContractionQuotient.genericQuotientMap_mk,
      Algebra.smul_def]
    change
      Ideal.Quotient.mk J
          (algebraMap R₂ RationalRing r * z) =
        Ideal.Quotient.mk J
          (N13TwoAdicCoordinateBaseChange.integralToSextic a)
    apply congrArg (Ideal.Quotient.mk J)
    rw [mul_comm]
    calc
      z * algebraMap R₂ RationalRing r =
          z *
            N13TwoAdicCoordinateBaseChange.integralToSextic
              (s : IntegralRing) := by
        rw [← hs]
        congr 1
        symm
        change
          N13GoodSexticCoordinateEquiv.toSextic
              (N13IntegralModelContraction.integralToGood
                (algebraMap R₂ IntegralRing r)) =
            algebraMap R₂ RationalRing r
        rw [N13IntegralModelContraction.integralToGood_algebraMap,
          N13GoodSexticCoordinateEquiv.toSextic_algebraMap]
        exact
          (IsScalarTower.algebraMap_apply
            R₂ Q₂ RationalRing r).symm
      _ = N13TwoAdicCoordinateBaseChange.integralToSextic a := hz
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [one_smul]
    exact
      N13CanonicalContractionQuotient.genericQuotientMap_injective J hxy

/-- A quadratic generic Mumford quotient forces its canonical contracted
quotient to have rank two over the two-adic integers. -/
theorem contractQuotient_finrank_eq_two
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    Module.finrank R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (SexticMumford.mumfordIdeal Model D.u D.v)) =
      2 := by
  let J : Ideal RationalRing :=
    SexticMumford.mumfordIdeal Model D.u D.v
  let B :=
    IntegralRing ⧸
      N13IntegralModelContraction.contractIdeal J
  let G := RationalRing ⧸ J
  let q : B →ₗ[R₂] G :=
    (genericQuotientAlgHom J).toLinearMap
  letI : IsLocalizedModule (nonZeroDivisors R₂) q :=
    genericQuotient_isLocalized J
  have hloc :
      Module.finrank R₂ G =
        Module.finrank R₂ B :=
    IsLocalizedModule.finrank_eq
      (nonZeroDivisors R₂) q le_rfl
  have hrank :
      Module.rank Q₂ G =
        Module.rank R₂ G :=
    IsLocalization.rank_eq
      Q₂ (nonZeroDivisors R₂) le_rfl
  have hfield :
      Module.finrank Q₂ G =
        Module.finrank R₂ G := by
    simpa only [Module.finrank] using
      congrArg Cardinal.toNat hrank
  have hgeneric :
      Module.finrank Q₂ G = 2 := by
    rw [Module.finrank_eq_card_basis
      (SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg)]
    rfl
  change Module.finrank R₂ B = 2
  calc
    Module.finrank R₂ B =
        Module.finrank R₂ G := hloc.symm
    _ = Module.finrank Q₂ G := hfield.symm
    _ = 2 := hgeneric

end

end MazurProof.N13GenericQuotientLocalization


