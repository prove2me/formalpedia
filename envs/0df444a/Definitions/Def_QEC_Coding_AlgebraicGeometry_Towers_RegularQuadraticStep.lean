-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
-- name    : QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:49:13.062502+00:00
-- url     : https://prove2.me/theorems/e25070bc-93a9-4819-9027-48630f6e1040
-- title:
--   Regular Quadratic Step
-- statement:
--   Definitions and structural lemmas for Regular Quadratic Step, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularQuadraticStep.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
noncomputable def regularQuadraticArtinSchreierIntegralPolynomial
    (P : GlobalPlace F256 K) (b : P.valuationRing) : P.valuationRing[X] :=
  X ^ 2 + X + C b
theorem regularQuadraticArtinSchreierIntegralPolynomial_monic
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    (regularQuadraticArtinSchreierIntegralPolynomial P b).Monic := by
  rw [regularQuadraticArtinSchreierIntegralPolynomial, add_assoc]
  exact Monic.add_of_left (monic_X_pow 2) (by
    calc
      ((X : P.valuationRing[X]) + C b).degree ≤ (1 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_X_le
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 2).degree := by
        rw [degree_X_pow]
        norm_num)
@[simp]
theorem regularQuadraticArtinSchreierIntegralPolynomial_natDegree
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    (regularQuadraticArtinSchreierIntegralPolynomial P b).natDegree = 2 := by
  apply natDegree_eq_of_degree_eq_some
  rw [regularQuadraticArtinSchreierIntegralPolynomial, add_assoc,
    degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow (R := P.valuationRing) 2
  · calc
      ((X : P.valuationRing[X]) + C b).degree ≤ (1 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_X_le
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 2).degree := by
        rw [degree_X_pow]
        norm_num
noncomputable def regularQuadraticArtinSchreierPolynomial
    (P : GlobalPlace F256 K) (b : P.valuationRing) : K[X] :=
  (regularQuadraticArtinSchreierIntegralPolynomial P b).map
    (algebraMap P.valuationRing K)
theorem regularQuadraticArtinSchreierPolynomial_eq_explicit
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    regularQuadraticArtinSchreierPolynomial P b =
      X ^ 2 + X + C (b : K) := by
  simp [regularQuadraticArtinSchreierPolynomial,
    regularQuadraticArtinSchreierIntegralPolynomial]
theorem regularQuadraticArtinSchreierPolynomial_monic
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    (regularQuadraticArtinSchreierPolynomial P b).Monic :=
  (regularQuadraticArtinSchreierIntegralPolynomial_monic P b).map _
@[simp]
theorem regularQuadraticArtinSchreierPolynomial_natDegree
    (P : GlobalPlace F256 K) (b : P.valuationRing) :
    (regularQuadraticArtinSchreierPolynomial P b).natDegree = 2 := by
  rw [regularQuadraticArtinSchreierPolynomial,
    (regularQuadraticArtinSchreierIntegralPolynomial_monic P b).natDegree_map,
    regularQuadraticArtinSchreierIntegralPolynomial_natDegree]
theorem regularQuadraticArtinSchreierPolynomial_separable
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (regularQuadraticArtinSchreierPolynomial P b).Separable := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  rw [regularQuadraticArtinSchreierPolynomial_eq_explicit]
  simp only [derivative_add, derivative_X_pow, derivative_X, derivative_C]
  reduce_mod_char!
  norm_num
noncomputable def regularQuadraticArtinSchreierDefiningPolynomial
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (_hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) : K[X] :=
  regularQuadraticArtinSchreierPolynomial P b
theorem regularQuadraticArtinSchreierDefiningPolynomial_monic
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (regularQuadraticArtinSchreierDefiningPolynomial P b hirr).Monic := by
  simpa only [regularQuadraticArtinSchreierDefiningPolynomial] using
    regularQuadraticArtinSchreierPolynomial_monic P b
abbrev RegularQuadraticArtinSchreierField
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :=
  AdjoinRoot (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)
noncomputable instance regularQuadraticArtinSchreierPolynomialIrreducibleFact
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Fact (Irreducible
      (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)) :=
  ⟨by
    simpa only [regularQuadraticArtinSchreierDefiningPolynomial] using hirr⟩
noncomputable instance regularQuadraticArtinSchreierConstantScalarTower
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsScalarTower F256 K (RegularQuadraticArtinSchreierField P b hirr) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable def regularQuadraticArtinSchreierEmbedding
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    K →ₐ[F256] RegularQuadraticArtinSchreierField P b hirr :=
  (Algebra.ofId K (RegularQuadraticArtinSchreierField P b hirr)).restrictScalars F256
noncomputable def regularQuadraticArtinSchreierRoot
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    RegularQuadraticArtinSchreierField P b hirr :=
  AdjoinRoot.root (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)
noncomputable instance regularQuadraticArtinSchreierFiniteDimensional
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    FiniteDimensional K (RegularQuadraticArtinSchreierField P b hirr) :=
  (AdjoinRoot.powerBasis
    (regularQuadraticArtinSchreierDefiningPolynomial_monic
      P b hirr).ne_zero).finite
noncomputable instance regularQuadraticArtinSchreier_isSeparable
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Algebra.IsSeparable K (RegularQuadraticArtinSchreierField P b hirr) := by
  let y := regularQuadraticArtinSchreierRoot P b hirr
  have hysep : IsSeparable K y := by
    dsimp [y, regularQuadraticArtinSchreierRoot]
    rw [IsSeparable, AdjoinRoot.minpoly_root
      (regularQuadraticArtinSchreierDefiningPolynomial_monic P b hirr).ne_zero,
      (regularQuadraticArtinSchreierDefiningPolynomial_monic P b hirr).leadingCoeff,
      inv_one, C.map_one, mul_one]
    simpa only [regularQuadraticArtinSchreierDefiningPolynomial] using
      regularQuadraticArtinSchreierPolynomial_separable P b hirr
  letI : Algebra.IsSeparable K
      (IntermediateField.adjoin K
        ({y} : Set (RegularQuadraticArtinSchreierField P b hirr))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := RegularQuadraticArtinSchreierField P b hirr)
      (x := y)).mpr hysep
  have hAlgebraAdjoin : Algebra.adjoin K
      ({y} : Set (RegularQuadraticArtinSchreierField P b hirr)) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (regularQuadraticArtinSchreierDefiningPolynomial_monic
        P b hirr).ne_zero).adjoin_gen_eq_top
    simp only [y, regularQuadraticArtinSchreierRoot,
      AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hadjoin : IntermediateField.adjoin K
      ({y} : Set (RegularQuadraticArtinSchreierField P b hirr)) = ⊤ := by
    apply top_unique
    intro z _
    exact (IntermediateField.algebra_adjoin_le_adjoin K
      ({y} : Set (RegularQuadraticArtinSchreierField P b hirr))) (by
        rw [hAlgebraAdjoin]
        exact Set.mem_univ z)
  refine ⟨fun z => IntermediateField.isSeparable_of_mem_isSeparable
    (F := K) (E := RegularQuadraticArtinSchreierField P b hirr)
    (L := IntermediateField.adjoin K
      ({y} : Set (RegularQuadraticArtinSchreierField P b hirr))) ?_⟩
  rw [hadjoin]
  exact Set.mem_univ z
instance regularQuadraticArtinSchreierValuationRingScalarTower
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsScalarTower P.valuationRing K
      (RegularQuadraticArtinSchreierField P b hirr) :=
  IsScalarTower.of_algebraMap_eq' rfl
abbrev RegularQuadraticArtinSchreierIntegralClosure
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :=
  integralClosure P.valuationRing
    (RegularQuadraticArtinSchreierField P b hirr)
noncomputable instance regularQuadraticArtinSchreierIntegralClosureIsTorsionFree
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Module.IsTorsionFree P.valuationRing
      (RegularQuadraticArtinSchreierIntegralClosure P b hirr) := by
  letI : Module.IsTorsionFree P.valuationRing
      (RegularQuadraticArtinSchreierField P b hirr) :=
    Module.IsTorsionFree.trans_faithfulSMul P.valuationRing K
      (RegularQuadraticArtinSchreierField P b hirr)
  exact IsIntegralClosure.isTorsionFree P.valuationRing
    (RegularQuadraticArtinSchreierField P b hirr)
noncomputable instance regularQuadraticArtinSchreierIntegralClosureFinite
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Module.Finite P.valuationRing
      (RegularQuadraticArtinSchreierIntegralClosure P b hirr) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite P.valuationRing K
    (RegularQuadraticArtinSchreierField P b hirr)
    (RegularQuadraticArtinSchreierIntegralClosure P b hirr)
noncomputable instance regularQuadraticArtinSchreierIntegralClosureIsFractionRing
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsFractionRing (RegularQuadraticArtinSchreierIntegralClosure P b hirr)
      (RegularQuadraticArtinSchreierField P b hirr) :=
  integralClosure.isFractionRing_of_finite_extension K
    (RegularQuadraticArtinSchreierField P b hirr)
noncomputable instance regularQuadraticArtinSchreierIntegralClosureIsDedekindDomain
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsDedekindDomain (RegularQuadraticArtinSchreierIntegralClosure P b hirr) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain P.valuationRing K
    (RegularQuadraticArtinSchreierField P b hirr)
noncomputable def regularQuadraticArtinSchreierIntegralRoot
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    RegularQuadraticArtinSchreierIntegralClosure P b hirr := by
  refine ⟨regularQuadraticArtinSchreierRoot P b hirr, ?_⟩
  refine ⟨regularQuadraticArtinSchreierIntegralPolynomial P b,
    regularQuadraticArtinSchreierIntegralPolynomial_monic P b, ?_⟩
  change eval₂
      ((AdjoinRoot.of
        (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)).comp
        (algebraMap P.valuationRing K))
      (regularQuadraticArtinSchreierRoot P b hirr)
      (regularQuadraticArtinSchreierIntegralPolynomial P b) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root
    (regularQuadraticArtinSchreierDefiningPolynomial P b hirr)
theorem exists_regularQuadraticArtinSchreierUpperIdeal
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    ∃ Q : Ideal (RegularQuadraticArtinSchreierIntegralClosure P b hirr),
      Q.IsMaximal ∧
        Q.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := RegularQuadraticArtinSchreierIntegralClosure P b hirr)
    (IsLocalRing.maximalIdeal P.valuationRing)
noncomputable def regularQuadraticArtinSchreierUpperIdeal
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Ideal (RegularQuadraticArtinSchreierIntegralClosure P b hirr) :=
  Classical.choose (exists_regularQuadraticArtinSchreierUpperIdeal P b hirr)
theorem regularQuadraticArtinSchreierUpperIdeal_isMaximal
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (regularQuadraticArtinSchreierUpperIdeal P b hirr).IsMaximal :=
  (Classical.choose_spec
    (exists_regularQuadraticArtinSchreierUpperIdeal P b hirr)).1
theorem regularQuadraticArtinSchreierUpperIdeal_liesOver
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (regularQuadraticArtinSchreierUpperIdeal P b hirr).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
  (Classical.choose_spec
    (exists_regularQuadraticArtinSchreierUpperIdeal P b hirr)).2
noncomputable def regularQuadraticArtinSchreierUpperHeightOne
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    IsDedekindDomain.HeightOneSpectrum
      (RegularQuadraticArtinSchreierIntegralClosure P b hirr) :=
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : (regularQuadraticArtinSchreierUpperIdeal P b hirr).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
    regularQuadraticArtinSchreierUpperIdeal_liesOver P b hirr
  { asIdeal := regularQuadraticArtinSchreierUpperIdeal P b hirr
    isPrime :=
      (regularQuadraticArtinSchreierUpperIdeal_isMaximal P b hirr).isPrime
    ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
      (regularQuadraticArtinSchreierUpperIdeal P b hirr) }
noncomputable def regularQuadraticArtinSchreierAbovePlace
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    GlobalPlace F256 (RegularQuadraticArtinSchreierField P b hirr) where
  valuation := (regularQuadraticArtinSchreierUpperHeightOne P b hirr).valuation
    (RegularQuadraticArtinSchreierField P b hirr)
  normalized :=
    (regularQuadraticArtinSchreierUpperHeightOne P b hirr).valuation_surjective
      (RegularQuadraticArtinSchreierField P b hirr)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


