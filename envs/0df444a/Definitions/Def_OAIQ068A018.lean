-- Prove2me | Definitions.Def_OAIQ068A018
-- name    : OAIQ068A018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:50:22.328993+00:00
-- url     : https://prove2.me/theorems/820229c4-dd0c-43f5-91fc-117d988b3599
-- title:
--   Definitions bundle OAIQ068A018 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 85 declarations of OpenAI's Lean: 27 definitions, 1 inductive type or structure, 10 instances and 47 theorems. The definitions and types are `OAI.PiExponent.RamifiedLocalLength.coverOriginIdeal`, `OAI.PiExponent.RamifiedLocalLength.coverOriginLocalEquiv`, `OAI.PiExponent.ReesGradedModule.integerPiece`, `OAI.PiExponent.ReesGradedModule.ordinaryPowerEquivIntegerPiece`, `OAI.PiExponent.ReesPolynomialPresentation.presentation`, `OAI.PiExponent.ReesPolynomialPresentation.presentationAlgebra`, `OAI.PiExponent.ReesPushdown.ordinaryPowerEquivPiece`, `OAI.PiExponent.TranslatedPowerCover.toPolynomial`, `OAI.PiExponent.WeightedBezout.pointLength`, `OAI.PiExponent.irrationalityExponent`, `OAI.PiExponent.polynomialOfCoefficients`, `OAI.PiExponent.primeLocalDirectional`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluation`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluationRingHom`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateBasisLocalEquiv`, `OAI.PiExponentJets.W22.RetainedPrimeCycle`, `OAI.PiExponentJets.W22.RetainedPrimeCycle.coefficientAt`, `OAI.PiExponentJets.W22.actualMultiplicityCycle`, `OAI.PiExponentJets.W22.homogeneousListPrefix`, `OAI.PiExponentJets.W22.zeroHomogeneousIdeal`, `OAI.PiExponentJets.W64.quotientSectionFactor`, `OAI.PiExponentJets.W64.quotientSectionMultiply`, `OAI.PiExponentSiegel.W08.coordinateImageIdeal`, `OAI.PiExponentSiegel.W08.coordinateQuotientEquiv`, `OAI.PiExponentSiegel.W08.coordinateQuotientInverse`, `OAI.PiExponentSiegel.W08.coordinateQuotientMap`, `OAI.PiExponentSiegel.W08.coordinateQuotientSectionEquiv`, `OAI.PiExponentSiegel.W08.renameQuotientSectionEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ReesFiniteCover`, `PiExponent_Ampleness_ReesGradedModule`, `PiExponent_Ampleness_ReesPolynomialPresentation`, `PiExponent_Ampleness_ReesPushdown`, `PiExponent_Analysis_ColonSeriesTelescope`, `PiExponent_Jets_PrimeNormalCotangent`, `PiExponent_Jets_TransverseMultiplicity`, `PiExponent_LocalAlgebra_ColonHilbertStep`, `PiExponent_LocalAlgebra_CoordinateBasisSplitting`, `PiExponent_LocalAlgebra_MultiplicityCycles`, `PiExponent_LocalAlgebra_PrimeResidueAlgebraEquiv`, `PiExponent_LocalAlgebra_QuotientSections`, `PiExponent_LocalAlgebra_RamifiedPointMap`, `PiExponent_LocalAlgebra_RamifiedPowerLength`, `PiExponent_LocalAlgebra_RegularCutHistory`, `PiExponent_LocalAlgebra_RegularHilbertStep`, `PiExponent_LocalAlgebra_RetainedIntersectionCycles`, `PiExponent_LocalAlgebra_RetainedMinimalPrimeFamily`, `PiExponent_LocalAlgebra_SeparablePointLength`, `PiExponent_LocalAlgebra_SplitCoordinateClosedPoint`, `PiExponent_LocalAlgebra_WeightedBezout`, `PiExponent_LocalAlgebra_WeightedBezoutBound`, `PiExponent_Polynomials_AuxiliaryPolynomial`, `PiExponent_Polynomials_CoordinateQuotientGrading`, `PiExponent_Polynomials_HomogeneousHilbertExistence`, `PiExponent_Polynomials_HomogeneousHilbertPolynomial`, `PiExponent_Polynomials_HomogeneousListHistory`, `PiExponent_Polynomials_PolynomialPrimeDimension`, `PiExponent_Polynomials_TranslatedPowerCover`, `PiExponent_Statement`.
--
--   **Imports.** It imports the bundles `OAIQ068A001`, `OAIQ068A002`, `OAIQ068A003`, `OAIQ068A006`, `OAIQ068A007`, `OAIQ068A008`, `OAIQ068A009` and `OAIQ068A010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A026` and `OAIQ068A027`; the proofs of `OAI_PiExponent_CurveInequality_weighted_curve_inequality` and `OAI.PiExponent.CurveInequality.weighted_curve_inequality_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A001
import Definitions.Def_OAIQ068A002
import Definitions.Def_OAIQ068A003
import Definitions.Def_OAIQ068A006
import Definitions.Def_OAIQ068A007
import Definitions.Def_OAIQ068A008
import Definitions.Def_OAIQ068A009
import Definitions.Def_OAIQ068A010

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesPushdown
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.ReesPushdown

open Polynomial PiExponentSeshadri.ReesGrading

variable {R : Type*} [CommRing R]

def ordinaryPowerEquivPiece (I : Ideal R) (n : ℕ) : ↥(I ^ n : Ideal R) ≃ₗ[R] piece I n where
  toFun a := ⟨⟨monomial n a.val, reesAlgebra.monomial_mem.mpr a.property⟩,
    by simp [mem_piece]⟩
  invFun p := ⟨((p : reesAlgebra I) : R[X]).coeff n, p.val.property n⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((mem_piece I n p.val).mp p.property).symm
  map_add' a b := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change monomial n (a • b.val) = a • monomial n b.val
    exact (monomial n).map_smul a b.val

end PiExponent.ReesPushdown

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesPolynomialPresentation
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesPolynomialPresentation
noncomputable section
open scoped BigOperators
open Polynomial PiExponentSeshadri.ReesGrading
variable {R J : Type*} [CommRing R] (I : Ideal R) (a : J → I)

def presentation : MvPolynomial J R →ₐ[R] reesAlgebra I :=
  MvPolynomial.aeval (fun j => generator I (a j))

@[simp] theorem presentation_X (j : J) : presentation I a (MvPolynomial.X j) = generator I (a j) :=
  MvPolynomial.aeval_X _ _

theorem presentation_monomial_mem (b : J →₀ ℕ) (r : R) :
    presentation I a (MvPolynomial.monomial b r) ∈ piece I b.degree := by
  classical
  rw [presentation, MvPolynomial.aeval_monomial]
  have hp : (∏ j ∈ b.support, generator I (a j) ^ b j) ∈ piece I b.degree := by
    have h := SetLike.prod_mem_graded (piece I) (fun j => b j)
      (fun j => generator I (a j) ^ b j) (F := b.support)
      (fun j _ => by simpa using SetLike.pow_mem_graded (b j) (generator_mem I (a j)))
    change (∏ j ∈ b.support, generator I (a j) ^ b j) ∈ piece I (∑ j ∈ b.support, b j)
    exact h
  have hr : algebraMap R (reesAlgebra I) r ∈ piece I 0 := by
    simp [mem_piece]
  simpa only [zero_add, Finsupp.prod] using SetLike.mul_mem_graded hr hp

theorem presentation_homogeneous_mem {n : ℕ} {p : MvPolynomial J R}
    (hp : p.IsHomogeneous n) : presentation I a p ∈ piece I n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (piece I n).zero_mem
  | add p q hp hq ihp ihq => simpa only [map_add] using (piece I n).add_mem ihp ihq
  | monomial b r hb =>
      have hb' : b.degree = n := by rw [Finsupp.degree_eq_weight_one, ← Pi.one_def, hb]
      simpa only [hb'] using presentation_monomial_mem I a b r

theorem evaluation_presentation (p : MvPolynomial J R) :
    evaluation I (presentation I a p) = MvPolynomial.eval (fun j => (a j).val) p := by
  have h : (evaluation I).comp (presentation I a).toRingHom =
      (MvPolynomial.eval₂Hom (RingHom.id R) (fun j => (a j).val)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [presentation, evaluation]
    · intro j
      simp [presentation, evaluation_generator]
  exact DFunLike.congr_fun h p

theorem homogeneous_piece_surjective
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (z : piece I n) :
    ∃ p : MvPolynomial J R, p.IsHomogeneous n ∧ presentation I a p = z.val := by
  have hz : (((z.val : reesAlgebra I) : R[X]).coeff n) ∈
      (Ideal.span (Set.range fun j => (a j).val)) ^ n := by
    rw [ha]
    exact z.val.property n
  obtain ⟨p, hp, heval⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous
    (fun j => (a j).val) _).mp hz
  refine ⟨p, hp, ?_⟩
  have hmem := presentation_homogeneous_mem I a hp
  apply Subtype.ext
  rw [(mem_piece I n _).mp hmem, (mem_piece I n _).mp z.property]
  congr 1
  have h := evaluation_presentation I a p
  rw [evaluation, RingHom.comp_apply, AlgHom.toRingHom_eq_coe] at h
  change Polynomial.eval 1 ((presentation I a p : reesAlgebra I) : R[X]) = _ at h
  rw [(mem_piece I n _).mp hmem] at h
  simpa only [Polynomial.eval_monomial, one_pow, mul_one] using h.trans heval

theorem presentation_surjective
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    Function.Surjective (presentation I a) := by
  classical
  intro z
  have hn (n : ℕ) := homogeneous_piece_surjective I a ha n (component I n z)
  choose p hp hpres using hn
  refine ⟨∑ n ∈ ((z : reesAlgebra I) : R[X]).support, p n, ?_⟩
  rw [map_sum]
  simp_rw [hpres]
  apply Subtype.ext
  change (reesAlgebra I).val (∑ n ∈ ((z : reesAlgebra I) : R[X]).support,
    (component I n z).val) = (z : R[X])
  rw [map_sum]
  exact ((z : R[X]).as_sum_support).symm

@[instance_reducible]
def presentationAlgebra : Algebra (MvPolynomial J R) (reesAlgebra I) :=
  (presentation I a).toRingHom.toAlgebra

end
end PiExponent.ReesPolynomialPresentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesFiniteCover
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace PiExponent.ReesFiniteCover
open PiExponentSeshadri.ReesGrading
variable {R J : Type} [CommRing R] (I : Ideal R) (a : J → I)
variable (ha : Ideal.span (Set.range fun j => (a j).val) = I)
include ha

theorem adjoin_eq_top : Algebra.adjoin R (Set.range fun j => generator I (a j)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  apply top_unique
  intro z hz
  exact ReesPolynomialPresentation.presentation_surjective I a ha z

theorem adjoin_zero_eq_top :
    Algebra.adjoin (piece I 0) (Set.range fun j => generator I (a j)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  have hh : z ∈ Algebra.adjoin R (Set.range fun j => generator I (a j)) := by
    rw [adjoin_eq_top I a ha]
    trivial
  induction hh using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact (Algebra.adjoin (piece I 0) (Set.range fun j => generator I (a j))).algebraMap_mem
      (zeroEquiv I r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem iSup_generator_basicOpen :
    (⨆ j, Proj.basicOpen (piece I) (generator I (a j))) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (piece I) (fun j => generator I (a j))
    (fun j => ⟨1, generator_mem I (a j)⟩) (adjoin_zero_eq_top I a ha)

end PiExponent.ReesFiniteCover
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesGradedModule
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesGradedModule
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesPolynomialPresentation PiExponent.GradedPolynomialLaurent
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] (I : Ideal R) (a : J → I)

abbrev integerPiece : ℤ → AddSubgroup (reesAlgebra I) :=
  NatToIntGrading.piece (piece I)

instance integerGradedRing : GradedRing (integerPiece I) where
  toGradedMonoid := NatToIntGrading.gradedMonoid (piece I)
  toDecomposition := NatToIntGrading.decomposition (piece I)

def ordinaryPowerEquivIntegerPiece (n : ℕ) : ↥(I ^ n : Ideal R) ≃+ integerPiece I (n : ℤ) :=
  (ReesPushdown.ordinaryPowerEquivPiece I n).toAddEquiv

theorem polynomial_negative_eq_zero (n : ℕ) (p : MvPolynomial J R)
    (hp : p ∈ grading (J := J) (R := R) (.negSucc n)) : p = 0 := by
  apply MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials hp
  intro b hb
  have hnonneg : 0 ≤ Finsupp.weight (1 : J → ℤ) b := by
    rw [Finsupp.weight_eq_sum]
    exact Finset.sum_nonneg fun j _ => by simp
  omega

theorem presentation_integer_mem {d : ℤ} {p : MvPolynomial J R}
    (hp : p ∈ grading (J := J) (R := R) d) :
    presentation I a p ∈ integerPiece I d := by
  cases d with
  | ofNat n =>
      change presentation I a p ∈ piece I n
      apply presentation_homogeneous_mem I a
      change p ∈ MvPolynomial.weightedHomogeneousSubmodule R (1 : J → ℤ) (n : ℤ) at hp
      rw [GradedH0.integer_grading_eq_homogeneous (R := R) (ι := J) n] at hp
      exact hp
  | negSucc n =>
      rw [polynomial_negative_eq_zero n p hp, map_zero]
      exact zero_mem _

theorem gradedScalarAction :
    letI := presentationAlgebra I a
    SetLike.GradedSMul (grading (J := J) (R := R)) (integerPiece I) := by
  let := presentationAlgebra I a
  constructor
  intro i j p z hp hz
  change presentation I a p * z ∈ integerPiece I (i + j)
  exact SetLike.mul_mem_graded (presentation_integer_mem I a hp) hz

end
end PiExponent.ReesGradedModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_QuotientSections
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable instance quotientSection_finite (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.Finite k (quotientSection I n) := by
  unfold quotientSection
  infer_instance

noncomputable def quotientSectionMultiply (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    quotientSection I n →ₗ[k] quotientSection I (n + d) where
  toFun x := ⟨x.1 * Ideal.Quotient.mk I f, by
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    apply Submodule.mem_map.mpr
    refine ⟨p * f, hp.mul hf, ?_⟩
    change Ideal.Quotient.mk I (p * f) = x.1 * Ideal.Quotient.mk I f
    rw [map_mul]
    exact congrArg (fun y => y * Ideal.Quotient.mk I f) hpx⟩
  map_add' x y := by apply Subtype.ext; exact add_mul _ _ _
  map_smul' c x := by apply Subtype.ext; exact smul_mul_assoc _ _ _

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularHilbertStep
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

noncomputable def quotientSectionFactor (I J : Ideal (MvPolynomial σ k))
    (hIJ : I ≤ J) (n : ℕ) : quotientSection I n →ₗ[k] quotientSection J n where
  toFun x := ⟨Ideal.Quotient.factorₐ k hIJ x.1, by
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    apply Submodule.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    exact congrArg (Ideal.Quotient.factorₐ k hIJ) hpx⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul _ _ _

theorem quotientSectionFactor_surjective (I J : Ideal (MvPolynomial σ k))
    (hIJ : I ≤ J) (n : ℕ) :
    Function.Surjective (quotientSectionFactor I J hIJ n) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := Submodule.mem_map.mp y.2
  refine ⟨⟨Ideal.Quotient.mk I p, Submodule.mem_map.mpr ⟨p, hp, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hpy

theorem quotientSectionFactor_ker_eq (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.ker (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)) =
      LinearMap.range (quotientSectionMultiply I f hf n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    have hz : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) p = 0 := by
      have hxv := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change (Ideal.Quotient.factorₐ k le_sup_right) x.1 = 0 at hxv
      change (Ideal.Quotient.factorₐ k le_sup_right) (Ideal.Quotient.mk I p) = 0
      rw [hpx]
      exact hxv
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨a, ha, hpa⟩ := homogeneous_mem_step_decomposition I hI f p hf hp hmem
    apply LinearMap.mem_range.mpr
    refine ⟨⟨Ideal.Quotient.mk I a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I f = x.1
    rw [← map_mul]
    have he : Ideal.Quotient.mk I (p - a * f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hpa
    rw [map_sub, sub_eq_zero] at he
    exact he.symm.trans hpx
  · intro hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change (Ideal.Quotient.factorₐ k le_sup_right)
      (y.1 * Ideal.Quotient.mk I f) = 0
    rw [map_mul]
    change (Ideal.Quotient.factorₐ k le_sup_right) y.1 *
      Ideal.Quotient.mk (Ideal.span {f} ⊔ I) f = 0
    have hf0 : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) f = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hinc : Ideal.span {f} ≤ Ideal.span {f} ⊔ I := le_sup_left
      exact hinc (Ideal.subset_span (Set.mem_singleton f))
    rw [hf0, mul_zero]

theorem hilbert_step_of_degree_lt (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (hnd : n < d) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) =
      Module.finrank k (quotientSection I n) := by
  let φ := quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right n
  have hinj : Function.Injective φ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    have hz : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) p = 0 := by
      have hxv := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change (Ideal.Quotient.factorₐ k le_sup_right) x.1 = 0 at hxv
      change (Ideal.Quotient.factorₐ k le_sup_right) (Ideal.Quotient.mk I p) = 0
      rw [hpx]
      exact hxv
    have hpI := homogeneous_mem_step_of_degree_lt I hI f p hf hp hnd
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    apply Subtype.ext
    change x.1 = 0
    rw [← hpx]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  exact (LinearEquiv.ofBijective φ
    ⟨hinj, quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right n⟩).finrank_eq.symm

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ColonHilbertStep
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem quotientSectionFactor_colon_ker (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.ker (quotientSectionFactor I (I.colon {f})
      (ideal_le_colon_singleton I f) n) =
      LinearMap.ker (quotientSectionMultiply I f hf n) := by
  ext x
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
  change Ideal.Quotient.mk I p = x.1 at hpx
  simp only [LinearMap.mem_ker, Subtype.ext_iff]
  change (Ideal.Quotient.factorₐ k (ideal_le_colon_singleton I f)) x.1 = 0 ↔
    x.1 * Ideal.Quotient.mk I f = 0
  rw [← hpx]
  change Ideal.Quotient.mk (I.colon {f}) p = 0 ↔
    Ideal.Quotient.mk I (p * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
    Submodule.mem_colon_singleton, smul_eq_mul]

theorem quotientSectionMultiply_range_finrank_colon
    (I : Ideal (MvPolynomial σ k)) {d : ℕ}
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank k (LinearMap.range (quotientSectionMultiply I f hf n)) =
      Module.finrank k (quotientSection (I.colon {f}) n) := by
  let φ := quotientSectionFactor I (I.colon {f}) (ideal_le_colon_singleton I f) n
  have hd := (LinearMap.ker φ).finrank_quotient_add_finrank
  let e := φ.quotKerEquivOfSurjective
    (quotientSectionFactor_surjective I (I.colon {f}) (ideal_le_colon_singleton I f) n)
  rw [e.finrank_eq] at hd
  change Module.finrank k (quotientSection (I.colon {f}) n) +
    Module.finrank k (LinearMap.ker (quotientSectionFactor I (I.colon {f})
      (ideal_le_colon_singleton I f) n)) = _ at hd
  rw [quotientSectionFactor_colon_ker I f hf n] at hd
  have hm := (quotientSectionMultiply I f hf n).finrank_range_add_finrank_ker
  omega

theorem colon_hilbert_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) (n+d)) +
      Module.finrank k (quotientSection (I.colon {f}) n) =
      Module.finrank k (quotientSection I (n+d)) := by
  have hd := (LinearMap.range (quotientSectionMultiply I f hf n)).finrank_quotient_add_finrank
  rw [quotientSectionMultiply_range_finrank_colon I f hf n,
    ← quotientSectionFactor_ker_eq I hI f hf n] at hd
  let e := (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)).quotKerEquivOfSurjective
    (quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right (n+d))
  rw [e.finrank_eq] at hd
  exact hd

theorem sectionHilbertSeries_colon_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) :
    sectionHilbertSeries I = sectionHilbertSeries (Ideal.span {f} ⊔ I) +
      PowerSeries.X ^ d * sectionHilbertSeries (I.colon {f}) := by
  ext n
  rw [map_add, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_sectionHilbertSeries]
  by_cases hdn : d ≤ n
  · rw [ite_eq_left hdn]
    have h := colon_hilbert_step I hI f hf (n-d)
    rw [Nat.sub_add_cancel hdn] at h
    exact_mod_cast h.symm
  · rw [ite_eq_right hdn, add_zero]
    exact congrArg (fun m : ℕ => (m : ℤ))
      (hilbert_step_of_degree_lt I hI f hf (Nat.lt_of_not_ge hdn)).symm

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_ColonSeriesTelescope
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]

variable [Finite σ]

theorem iteratedColon_series_telescope (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m : ℕ) :
    sectionHilbertSeries I =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j *
        sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j)) +
      PowerSeries.X ^ m * sectionHilbertSeries (iteratedColon I f m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs := sectionHilbertSeries_colon_step (iteratedColon I f m)
      (iteratedColon_homogeneous I hI f hf m) f hf
    simp only [pow_one, ← iteratedColon_succ] at hs
    rw [ih, hs, Finset.sum_range_succ, pow_succ]
    ring

theorem stableColon_series (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1)
    (hstable : I.colon {f} = I) :
    sectionHilbertSeries I = sectionHilbertSeries (Ideal.span {f} ⊔ I) *
      (PowerSeries.invOneSubPow ℤ 1).val := by
  have hs := sectionHilbertSeries_colon_step I hI f hf
  rw [hstable, pow_one] at hs
  have he : (1 - PowerSeries.X) * sectionHilbertSeries I =
      sectionHilbertSeries (Ideal.span {f} ⊔ I) := by
    linear_combination hs
  have hunit : (1 - (PowerSeries.X : PowerSeries ℤ)) *
      (PowerSeries.invOneSubPow ℤ 1).val = 1 := by
    rw [← pow_one (1 - (PowerSeries.X : PowerSeries ℤ)),
      ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow ℤ 1).inv_val
  calc
    sectionHilbertSeries I = ((1-PowerSeries.X) * sectionHilbertSeries I) *
        (PowerSeries.invOneSubPow ℤ 1).val := by
          rw [mul_right_comm, hunit, one_mul]
    _ = _ := by rw [he]

theorem stabilized_iteratedColon_series (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m : ℕ)
    (hstable : iteratedColon I f (m+1) = iteratedColon I f m) :
    sectionHilbertSeries I =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j *
        sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j)) +
      PowerSeries.X ^ m *
        (sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f m) *
          (PowerSeries.invOneSubPow ℤ 1).val) := by
  rw [iteratedColon_series_telescope I hI f hf m,
    stableColon_series (iteratedColon I f m)
      (iteratedColon_homogeneous I hI f hf m) f hf hstable]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_PrimeNormalCotangent
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct

variable {C ι : Type*} [Field C] [Fintype ι]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

def primeLocalDirectional (v : ι → Q.ResidueField) :
    Derivation C (Localization.AtPrime Q) Q.ResidueField :=
  ∑ i, v i • primeLocalPartial Q i

@[simp]
theorem primeNormalPairing_toCotangent (v : ι → Q.ResidueField)
    (x : IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    primeNormalPairing Q v ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent x) =
      primeLocalDirectional Q v x := by
  change (∑ i, v i • primePartialNormal Q i) _ = _
  rw [LinearMap.sum_apply]
  change (∑ i, v i * primeLocalPartial Q i x.1) = _
  change (∑ i, v i * primeLocalPartial Q i x.1) =
    (Derivation.coeFnAddMonoidHom (∑ i, v i • primeLocalPartial Q i)) x.1
  rw [map_sum, Finset.sum_apply]
  rfl

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TransverseMultiplicity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

omit [DecidableEq σ] in
theorem rectangularPacket_surjective (n : σ → ℕ) :
    Function.Surjective (rectangularPacket (K := K) n) := by
  classical
  intro packet
  let f : MvPowerSeries σ K := fun d =>
    if hd : ∀ i, d i < n i then packet ⟨d, hd⟩ else 0
  refine ⟨f, ?_⟩
  funext d
  change (if hd : ∀ i, d.val i < n i then packet ⟨d.val, hd⟩ else 0) = packet d
  simp only [dite_eq_left d.property]
  exact congrArg packet (Subtype.ext rfl)

end
end PiExponentApprox.TransverseMultiplicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeResidueAlgebraEquiv
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S]
variable (e : R ≃ₐ[K] S) (P : Ideal R) [P.IsPrime]

theorem primeResidueAlgEquiv_transcendenceBasis {ι : Type*} (x : ι → P.ResidueField)
    (hx : IsTranscendenceBasis K x) :
    IsTranscendenceBasis K (fun i => primeResidueAlgEquiv e P (x i)) :=
  (primeResidueAlgEquiv e P).isTranscendenceBasis hx

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SplitCoordinateClosedPoint
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution
open scoped IntermediateField

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]

variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

theorem splitResidue_algebraic :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    Algebra.IsAlgebraic (SplitCoefficientField K β) (SplitResidue K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  have h := hB.isAlgebraic_field
  exact (Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (rationalResidueEquiv (splitLocalBeta K α β Q) hB.1)
    (RingEquiv.refl (SplitResidue K α β Q)) (by rfl)).mp h

def closedPointEvaluation :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    MvPolynomial α (SplitCoefficientField K β) →ₐ[SplitCoefficientField K β]
      SplitResidue K α β Q :=
  letI := splitCoefficientResidueAlgebra K α β Q hB
  MvPolynomial.aeval (fun i =>
    algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) (MvPolynomial.X (Sum.inl i)))

abbrev closedPointEvaluationRingHom :
    MvPolynomial α (SplitCoefficientField K β) →+* SplitResidue K α β Q :=
  letI := splitCoefficientResidueAlgebra K α β Q hB
  (closedPointEvaluation K α β Q hB).toRingHom

theorem closedPointEvaluation_kernel_maximal :
    (RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).IsMaximal := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitResidue_algebraic K α β Q hB
  exact algebraic_field_kernel_isMaximal (closedPointEvaluation K α β Q hB)

theorem closedPointEvaluation_coefficient (f : MvPolynomial β K) :
    closedPointEvaluation K α β Q hB
      (MvPolynomial.C (algebraMap (MvPolynomial β K) (SplitCoefficientField K β) f)) =
      MvPolynomial.aeval (splitResidueBeta K α β Q) f := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  rw [closedPointEvaluation, MvPolynomial.aeval_C]
  change ((rationalResidueEquiv (splitLocalBeta K α β Q) hB.1
    (algebraMap (MvPolynomial β K) (SplitCoefficientField K β) f)) :
      SplitResidue K α β Q) = _
  exact rationalResidueEquiv_polynomial (splitLocalBeta K α β Q) hB.1 f

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateBasisSplitting
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable {n : ℕ} {T : Type*} (j : T → Fin n) (hj : Function.Injective j)

variable (K : Type*) [Field K] (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
variable (t : Set Q.ResidueField) (j : t → Fin n) (hj : Function.Injective j)
variable (hcoord : ∀ a, residueCoordinate K n Q (j a) = (a : Q.ResidueField))
variable (ht : IsTranscendenceBasis K ((↑) : t → Q.ResidueField))

include hcoord ht in

theorem coordinateSplitPrime_basis :
    IsTranscendenceBasis K
      (splitResidueBeta K (RemainingCoordinate j) t (coordinateSplitPrime K Q t j hj)) := by
  have hb := primeResidueAlgEquiv_transcendenceBasis
    (coordinateBasisRenaming j hj K) Q ((↑) : t → Q.ResidueField) ht
  have he : splitResidueBeta K (RemainingCoordinate j) t (coordinateSplitPrime K Q t j hj) =
      fun a : t => primeResidueAlgEquiv (coordinateBasisRenaming j hj K) Q (a : Q.ResidueField) := by
    funext a
    rw [← hcoord a]
    change algebraMap (MvPolynomial (RemainingCoordinate j ⊕ t) K)
      (coordinateSplitPrime K Q t j hj).ResidueField (MvPolynomial.X (Sum.inr a)) =
      primeResidueAlgEquiv (coordinateBasisRenaming j hj K) Q
        (algebraMap (MvPolynomial (Fin n) K) Q.ResidueField (MvPolynomial.X (j a)))
    rw [primeResidueAlgEquiv_algebraMap]
    change algebraMap _ (coordinateSplitPrime K Q t j hj).ResidueField (MvPolynomial.X (Sum.inr a)) =
      algebraMap _ (coordinateSplitPrime K Q t j hj).ResidueField
        (MvPolynomial.rename (coordinateIndexSplitting j hj).symm (MvPolynomial.X (j a)))
    rw [MvPolynomial.rename_X, coordinateIndexSplitting_symm_selected]
  rw [he]
  exact hb

def coordinateBasisLocalEquiv : Localization.AtPrime Q ≃+*
    Localization.AtPrime (coordinateSplitPrime K Q t j hj) :=
  PiExponentSiegel.W23.atPrimeEquivOfRingEquiv (coordinateBasisRenaming j hj K).toRingEquiv Q

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialPrimeDimension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W24
open PiExponentSiegel.W23 PiExponentSiegelAux.W09
open PiExponentJets.PolynomialLocalResidueResolution

section Equivalence
variable {A B : Type*} [CommRing A] [CommRing B]

attribute [local instance] OAI.PiExponentJets.W24.imagePrime_isPrime
theorem ringEquiv_localizedIdeal_map (e : A ≃+* B)
    (P Q : Ideal A) [Q.IsPrime] :
    (parameterLocalizedIdeal P Q).map (atPrimeEquivOfRingEquiv e Q).toRingHom =
      parameterLocalizedIdeal (P.map e.toRingHom) (Q.map e.toRingHom) := by
  unfold parameterLocalizedIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact atPrimeEquivOfRingEquiv_algebraMap e Q a

end Equivalence


end PiExponentJets.W24

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_CoordinateQuotientGrading
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PiExponentSiegel.W08

section

open MvPolynomial

variable {k σ τ : Type*} [Field k]

theorem coordinateEval_surjective :
    Function.Surjective (coordinateEval (k := k) (σ := σ)) :=
  fun p => ⟨coordinateInclude p, coordinateEval_include p⟩

theorem coordinateEval_homogeneous {p : MvPolynomial (Option σ) k} {n : ℕ}
    (hp : p.IsHomogeneous n) : (coordinateEval p).IsHomogeneous n := by
  simpa only [coordinateEval, one_mul] using hp.aeval
    (fun o => Option.elim o 0 (MvPolynomial.X : σ → MvPolynomial σ k))
    (show ∀ o : Option σ, (Option.elim o 0 (MvPolynomial.X : σ → MvPolynomial σ k)).IsHomogeneous 1
      from fun o => by cases o with
        | none => exact (homogeneousSubmodule σ k 1).zero_mem
        | some i => exact isHomogeneous_X k i)

theorem coordinateInclude_homogeneous {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsHomogeneous n) : (coordinateInclude p).IsHomogeneous n :=
  hp.rename_isHomogeneous

noncomputable def coordinateImageIdeal (J : Ideal (MvPolynomial (Option σ) k)) :
    Ideal (MvPolynomial σ k) := J.map coordinateEval.toRingHom

theorem coordinateImageIdeal_homogeneous (J : Ideal (MvPolynomial (Option σ) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Option σ) k)) :
    (coordinateImageIdeal J).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) :=
  homogeneous_ideal_map_of_degree_preserving coordinateEval
    (fun _ _ hp => coordinateEval_homogeneous hp) J hJ

theorem coordinateInclude_eval_mod (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (p : MvPolynomial (Option σ) k) :
    Ideal.Quotient.mk J (coordinateInclude (coordinateEval p)) = Ideal.Quotient.mk J p := by
  have h : ((Ideal.Quotient.mkₐ k J).comp coordinateInclude).comp coordinateEval =
      Ideal.Quotient.mkₐ k J := by
    ext i
    cases i with
    | none => simpa [coordinateInclude] using (Ideal.Quotient.eq_zero_iff_mem.mpr hX).symm
    | some i => simp [coordinateInclude]
  exact AlgHom.congr_fun h p

noncomputable def coordinateQuotientMap (J : Ideal (MvPolynomial (Option σ) k)) :
    (MvPolynomial (Option σ) k ⧸ J) →ₐ[k]
      (MvPolynomial σ k ⧸ coordinateImageIdeal J) :=
  Ideal.quotientMapₐ (coordinateImageIdeal J) coordinateEval Ideal.le_comap_map

theorem coordinateInclude_image_mem (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) {p : MvPolynomial σ k} (hp : p ∈ coordinateImageIdeal J) :
    coordinateInclude p ∈ J := by
  obtain ⟨q, hq, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective coordinateEval.toRingHom coordinateEval_surjective).mp hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk J (coordinateInclude (coordinateEval q)) = 0
  rw [coordinateInclude_eval_mod J hX]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hq

noncomputable def coordinateQuotientInverse (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) :
    (MvPolynomial σ k ⧸ coordinateImageIdeal J) →ₐ[k]
      (MvPolynomial (Option σ) k ⧸ J) :=
  Ideal.quotientMapₐ J coordinateInclude (fun _ hp => coordinateInclude_image_mem J hX hp)

noncomputable def coordinateQuotientEquiv (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) :
    (MvPolynomial (Option σ) k ⧸ J) ≃ₐ[k]
      (MvPolynomial σ k ⧸ coordinateImageIdeal J) :=
  { coordinateQuotientMap J with
    invFun := coordinateQuotientInverse J hX
    left_inv := by
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact coordinateInclude_eval_mod J hX p
    right_inv := by
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk _ (coordinateEval (coordinateInclude p)) = _
      rw [coordinateEval_include] }

@[simp] theorem coordinateQuotientEquiv_mk (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (p : MvPolynomial (Option σ) k) :
    coordinateQuotientEquiv J hX (Ideal.Quotient.mk J p) =
      Ideal.Quotient.mk (coordinateImageIdeal J) (coordinateEval p) := rfl

theorem coordinateQuotientEquiv_section_map (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    (PiExponentJets.W64.quotientSection J n).map
      (coordinateQuotientEquiv J hX).toLinearEquiv.toLinearMap =
      PiExponentJets.W64.quotientSection (coordinateImageIdeal J) n := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨coordinateEval p, coordinateEval_homogeneous hp, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk J (coordinateInclude p), ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨coordinateInclude p, coordinateInclude_homogeneous hp, rfl⟩
    · change Ideal.Quotient.mk _ (coordinateEval (coordinateInclude p)) = _
      rw [coordinateEval_include]
      rfl

noncomputable def coordinateQuotientSectionEquiv (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    PiExponentJets.W64.quotientSection J n ≃ₗ[k]
      PiExponentJets.W64.quotientSection (coordinateImageIdeal J) n :=
  (coordinateQuotientEquiv J hX).toLinearEquiv.ofSubmodules _ _
    (coordinateQuotientEquiv_section_map J hX n)

theorem coordinateQuotientSection_finrank (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    Module.finrank k (PiExponentJets.W64.quotientSection J n) =
      Module.finrank k (PiExponentJets.W64.quotientSection (coordinateImageIdeal J) n) :=
  (coordinateQuotientSectionEquiv J hX n).finrank_eq

end

variable {k σ τ : Type*} [Field k]

theorem renameQuotientEquiv_section_map (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    (PiExponentJets.W64.quotientSection J n).map
      (renameQuotientEquiv e J).toLinearEquiv.toLinearMap =
      PiExponentJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨MvPolynomial.rename e p, hp.rename_isHomogeneous, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk J (MvPolynomial.rename e.symm p), ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨MvPolynomial.rename e.symm p, hp.rename_isHomogeneous, rfl⟩
    · change Ideal.Quotient.mk _ (MvPolynomial.rename e (MvPolynomial.rename e.symm p)) = _
      exact congrArg (Ideal.Quotient.mk _) ((MvPolynomial.renameEquiv k e).apply_symm_apply p)

noncomputable def renameQuotientSectionEquiv (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PiExponentJets.W64.quotientSection J n ≃ₗ[k]
      PiExponentJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n :=
  (renameQuotientEquiv e J).toLinearEquiv.ofSubmodules _ _
    (renameQuotientEquiv_section_map e J n)

theorem renameQuotientSection_finrank (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (PiExponentJets.W64.quotientSection J n) =
      Module.finrank k
        (PiExponentJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n) :=
  (renameQuotientSectionEquiv e J n).finrank_eq

end PiExponentSiegel.W08

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousHilbertExistence
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem sectionHilbertSeries_rename {σ τ : Type u} [Finite σ] [Finite τ]
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ k)) :
    sectionHilbertSeries I =
      sectionHilbertSeries (I.map (MvPolynomial.rename e).toRingHom) := by
  ext n
  simp only [coeff_sectionHilbertSeries,
    PiExponentSiegel.W08.renameQuotientSection_finrank e I n]

theorem sectionHilbertSeries_coordinate {σ : Type u} [Finite σ]
    (I : Ideal (MvPolynomial (Option σ) k)) (hX : MvPolynomial.X none ∈ I) :
    sectionHilbertSeries I =
      sectionHilbertSeries (PiExponentSiegel.W08.coordinateImageIdeal I) := by
  ext n
  simp only [coeff_sectionHilbertSeries,
    PiExponentSiegel.W08.coordinateQuotientSection_finrank I hX n]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousHilbertPolynomial
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem rational_hilbert_numerator {σ : Type u} [Fintype σ]
    (I : Ideal (MvPolynomial σ k)) (P : Polynomial ℤ)
    (hP : sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val) :
    rationalSectionHilbertSeries I =
      ((P.map (Int.castRingHom ℚ)) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card σ)).val := by
  rw [rationalSectionHilbertSeries, hP, map_mul, map_int_invOneSubPow,
    ← Polynomial.polynomial_map_coe]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RetainedIntersectionCycles
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

namespace ProjectiveComponent

variable {k : Type u} {σ : Type v} [Field k]

instance instIsPrimeMvPolynomialValIdealAndIsHomogeneousNatSubmoduleHomogeneousSubmoduleExistsNotMemX (P : ProjectiveComponent k σ) : P.val.IsPrime := P.property.1

end ProjectiveComponent

structure RetainedPrimeCycle (k : Type u) (σ : Type v) [Field k] where
  Index : Type w
  finiteIndex : Fintype Index
  component : Index → ProjectiveComponent k σ
  coefficient : Index → ℕ

namespace RetainedPrimeCycle

variable {k : Type u} {σ : Type v} [Field k] [Fintype σ]

instance instFintypeIndex (C : RetainedPrimeCycle.{u,v,w} k σ) : Fintype C.Index := C.finiteIndex

noncomputable def coefficientAt (C : RetainedPrimeCycle.{u,v,w} k σ)
    (P : ProjectiveComponent k σ) : ℕ :=
  ∑ a, if C.component a = P then C.coefficient a else 0

end RetainedPrimeCycle
end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RetainedMinimalPrimeFamily
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

namespace RetainedMinimalPrime

variable {I T : Ideal (MvPolynomial σ k)}

noncomputable instance finiteFamily (I T : Ideal (MvPolynomial σ k)) :
    Fintype (RetainedMinimalPrime I T) := by
  have hfinite : {Q : Ideal (MvPolynomial σ k) | Q ∈ I.minimalPrimes ∧ Q ≤ T}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial σ k) I).subset
      (fun _ h => h.1)
  exact hfinite.fintype

end RetainedMinimalPrime

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_MultiplicityCycles
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

noncomputable def actualMultiplicityCycle
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) :
    RetainedPrimeCycle.{u,u,u} k σ where
  Index := RetainedMinimalPrime I T
  finiteIndex := inferInstance
  component := RetainedMinimalPrime.toComponent hI v hv
  coefficient := fun P => actualLocalLength I P.val

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedBezout
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedBezout

open scoped BigOperators

variable {k σ τ : Type*} [Field k]

theorem translatedPowerSubstitution_factor (w : σ → ℕ) (a : σ → k) :
    translatedPowerSubstitution w a =
      (MvPolynomial.aeval (fun i => MvPolynomial.X i ^ w i)).comp (translation a) := by
  ext i
  simp [translatedPowerSubstitution, translation]

end PiExponent.WeightedBezout

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RamifiedPointMap
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.RamifiedLocalLength

open IsLocalRing WeightedBezout

variable {k σ : Type*} [Field k]

instance translatedPowerLocalMap_isLocalHom (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    IsLocalHom (translatedPowerLocalMap w a hw).toRingHom :=
  Localization.isLocalHom_localRingHom _ _ _
    (translatedPowerSubstitution_comap_origin w a hw).symm

end PiExponent.RamifiedLocalLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_TranslatedPowerCover
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TranslatedPowerCover

open WeightedBezout
open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

instance instCommRingRing (w : σ → ℕ) (a : σ → k) : CommRing (Ring w a) :=
  inferInstanceAs (CommRing (MvPolynomial σ k))

def toPolynomial (w : σ → ℕ) (a : σ → k) : Ring w a ≃+* MvPolynomial σ k :=
  RingEquiv.refl _

instance instAlgebraMvPolynomialRing (w : σ → ℕ) (a : σ → k) : Algebra (MvPolynomial σ k) (Ring w a) :=
  ((toPolynomial w a).symm.toRingHom.comp
    (translatedPowerSubstitution w a).toRingHom).toAlgebra

end
end PiExponent.TranslatedPowerCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RamifiedPowerLength
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.RamifiedLocalLength

open WeightedBezout
open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

abbrev coverOriginIdeal (w : σ → ℕ) (a : σ → k) :
    Ideal (TranslatedPowerCover.Ring w a) :=
  (pointIdeal (0 : σ → k)).comap (TranslatedPowerCover.toPolynomial w a).toRingHom

instance coverOriginIdeal_isMaximal (w : σ → ℕ) (a : σ → k) :
    (coverOriginIdeal w a).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ (TranslatedPowerCover.toPolynomial w a).surjective

omit [Fintype σ] in
theorem coverOriginIdeal_liesOver (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    (coverOriginIdeal w a).LiesOver (pointIdeal a) := by
  constructor
  change pointIdeal a =
    ((pointIdeal (0 : σ → k)).comap (TranslatedPowerCover.toPolynomial w a).toRingHom).comap
      (algebraMap (MvPolynomial σ k) (TranslatedPowerCover.Ring w a))
  rw [Ideal.comap_comap]
  exact (translatedPowerSubstitution_comap_origin w a hw).symm

omit [Fintype σ] in
theorem coverOriginIdeal_unique (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i)
    (Q : Ideal (TranslatedPowerCover.Ring w a)) (hQ : Q.IsPrime)
    (hQa : pointIdeal a ≤ Q.under (MvPolynomial σ k)) : Q = coverOriginIdeal w a := by
  let e := TranslatedPowerCover.toPolynomial w a
  let : Q.IsPrime := hQ
  have hmap : (Q.map e.toRingHom).IsPrime := Ideal.map_isPrime_of_equiv e
  let : (Q.map e.toRingHom).IsPrime := hmap
  have hcont : pointIdeal a ≤ (Q.map e.toRingHom).comap (translatedPowerSubstitution w a).toRingHom := by
    intro p hp
    exact Ideal.mem_map_of_mem e.toRingHom (hQa hp)
  have hle : pointIdeal (0 : σ → k) ≤ Q.map e.toRingHom := by
    rw [pointIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro polynomial ⟨index, rfl⟩
    have hcoordinate : MvPolynomial.X index - MvPolynomial.C (a index) ∈ pointIdeal a := by
      simp
    have hpower := hcont hcoordinate
    change translatedPowerSubstitution w a
      (MvPolynomial.X index - MvPolynomial.C (a index)) ∈ Q.map e.toRingHom at hpower
    have hvariable : MvPolynomial.X index ∈ Q.map e.toRingHom :=
      (hmap.pow_mem_iff_mem (w index) (hw index)).mp (by
        simpa only [map_sub, translatedPowerSubstitution_X, translatedPowerSubstitution_C,
          add_sub_cancel_left] using hpower)
    simpa using hvariable
  have hEq := ((inferInstance : (pointIdeal (0 : σ → k)).IsMaximal).eq_of_le
    hmap.ne_top hle).symm
  have hc := congrArg (Ideal.comap e.toRingHom) hEq
  rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at hc
  exact hc

def coverOriginLocalEquiv (w : σ → ℕ) (a : σ → k) :
    Localization.AtPrime (coverOriginIdeal w a) ≃+*
      Localization.AtPrime (pointIdeal (0 : σ → k)) :=
  Localization.localRingEquiv (coverOriginIdeal w a) (pointIdeal (0 : σ → k))
    (TranslatedPowerCover.toPolynomial w a) rfl

end
end PiExponent.RamifiedLocalLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularCutHistory
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

noncomputable def zeroHomogeneousIdeal : HomogeneousPolynomialIdeal k σ :=
  ⟨⊥, Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)⟩

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SeparablePointLength
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap_isLocalHom _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SeparablePointLength

open IsLocalRing TensorProduct

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

attribute [local instance] MvPolynomial.algebraMvPolynomial

instance pointLocalMap_isLocalHom (b : ι → E) :
    IsLocalHom (pointLocalMap (K := K) b) :=
  Localization.isLocalHom_localRingHom _ _ _ rfl

end PiExponent.SeparablePointLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousListHistory
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k]

noncomputable def homogeneousListPrefix
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i)) (j : ℕ) :
    HomogeneousPolynomialIdeal k σ :=
  ⟨Ideal.ofList (gs.take j), PiExponentSiegel.W20.prefixIdeal_homogeneous gs degrees hhom j⟩

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedBezoutBound
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace PiExponent.WeightedBezout

noncomputable def pointLength {k : Type*} [Field k] {n : ℕ}
    (a : Fin n → k) (I : Ideal (MvPolynomial (Fin n) k)) : ℕ∞ :=
  Module.length (Localization.AtPrime (pointIdeal a))
    (Localization.AtPrime (pointIdeal a) ⧸ I.map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime (pointIdeal a))))

end PiExponent.WeightedBezout

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_AuxiliaryPolynomial
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

noncomputable def polynomialOfCoefficients {d : ℕ} (S : Finset (Fin d → ℕ)) :
    (S → ℂ) →ₗ[ℂ] MvPolynomial (Fin d) ℂ := by
  classical
  exact
    { toFun := fun x => ∑ a : S, MvPolynomial.monomial
        (InterpolationMatrix.exponentVector a.val) (x a)
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun z x => by
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]  }

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Statement
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

noncomputable def irrationalityExponent (x : ℝ) : ℝ := sSup (ApproximationExponents x)

end PiExponent

end OAI
end


