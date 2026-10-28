-- Prove2me | Definitions.Def_OAIQ032L021
-- name    : OAIQ032L021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:10:03.454994+00:00
-- url     : https://prove2.me/theorems/df33e378-9b42-4983-99cc-017d3d380536
-- title:
--   Definitions bundle OAIQ032L021 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 151 declarations of OpenAI's Lean: 53 definitions, 5 instances and 93 theorems. The definitions and types are `OAI.Lech.IdealFiltered.zeroTermEquiv`, `OAI.Lech.IdealGraded.initialForm`, `OAI.Lech.ImageCech.mapCochains`, `OAI.Lech.LocalLine.basisEquiv`, `OAI.Lech.LocalLine.trivial`, `OAI.Lech.MonomialSpanning.pieceGenerator`, `OAI.Lech.PartialLaurent.localizationEquiv`, `OAI.Lech.PartialLaurent.polynomialCechEquiv`, `OAI.Lech.PartialLaurent.polynomialCochains`, `OAI.Lech.PartialLaurent.polynomialCochainsEquiv`, `OAI.Lech.PartialLaurent.polynomialD`, `OAI.Lech.PartialLaurent.polynomialLocalizationEquiv`, `OAI.Lech.PartialLaurent.polynomialTwistEquiv`, `OAI.Lech.PartialLaurent.polynomialTwistToLaurent`, `OAI.Lech.PartialLaurent.restrictAlgHom`, `OAI.Lech.PartialLaurent.twistToLaurent`, `OAI.Lech.PrimitiveRootModule.splitting`, `OAI.Lech.ProductLaurent.binaryForm`, `OAI.Lech.ProductLaurent.chartMap`, `OAI.Lech.ProductLaurent.chartUnit`, `OAI.Lech.ProductLaurent.clearedPolynomial`, `OAI.Lech.ProductLaurent.clearingBound`, `OAI.Lech.ProductLaurent.monomialHom`, `OAI.Lech.ProductLaurent.monomialUnit`, `OAI.Lech.ProductLaurent.permute`, `OAI.Lech.ProductLaurent.variableUnit`, `OAI.Lech.ProductSourceCover.ordinaryComplex`, `OAI.Lech.ProductSourceCover.ordinaryDivisorSequence`, `OAI.Lech.ProjectiveRoot.canonicalRing`, `OAI.Lech.ProjectiveRoot.coeffToIntersection`, `OAI.Lech.ProjectiveRoot.coeffToIntersectionModule`, `OAI.Lech.ProjectiveRoot.projectiveEulerInstance1`, `OAI.Lech.RestrictedPolynomialCech.cochains`, `OAI.Lech.RestrictedPolynomialCech.d`, `OAI.Lech.RootChartAtlas.D`, `OAI.Lech.RootChartAtlas.GridD`, `OAI.Lech.RootChartAtlas.moduleWork`, `OAI.Lech.RootInvariants.algebraBaseMapRight`, `OAI.Lech.RootInvariants.commonExtension`, `OAI.Lech.RootInvariants.gradedLineBasisAlgebra` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_AlternatingCechPrismPrimitive`, `Multiplicity_AlternatingCechUnaugmentedComplex`, `Multiplicity_AssociatedGradedReduction`, `Multiplicity_GradedChartCochains`, `Multiplicity_GradedLineBasisHasBasis`, `Multiplicity_IdealGradedRing`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_LechLevel`, `Multiplicity_LechSignedUnit`, `Multiplicity_LechTorsionOf`, `Multiplicity_NativeDescentCanonicalAlg`, `Multiplicity_OrderedRootBasis`, `Multiplicity_PartialLaurentTotalDegree`, `Multiplicity_PrincipalCoverRegularRegularMap`, `Multiplicity_ProductSourceCoverAllowedEmpty`, `Multiplicity_ProductSourceCoverFaceSlice`, `Multiplicity_ProductSourceCoverHighThreshold`, `Multiplicity_ReesRootUnfiltered`, `Multiplicity_RootChartAtlasGlobalCoefficient`, `Multiplicity_RootInvariantsWeightZero`, `Multiplicity_RootLineEuler`, `Multiplicity_RootOverlap`, `Multiplicity_RootPermutation`, `Multiplicity_RootProjectiveEuler`, `Multiplicity_RootRestriction`, `Multiplicity_RootUlrichModule`, `Multiplicity_RootUlrichSpan`, `Multiplicity_StandardFactorChartsL`, `Multiplicity_TwistedLocalizationPieceMap`, `Multiplicity_UniversalFactorMapMapChart`.
--
--   **Imports.** It imports the bundles `OAIQ032L010`, `OAIQ032L011`, `OAIQ032L012`, `OAIQ032L013`, `OAIQ032L014` and `OAIQ032L015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L024`, `OAIQ032L025`, `OAIQ032L026` and `OAIQ032L027`; the proofs of `OAI.Lech.MinimalReduction.exists_reduction` and `OAI.Lech.PowerSeries.maximal_power_colength`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L010
import Definitions.Def_OAIQ032L011
import Definitions.Def_OAIQ032L012
import Definitions.Def_OAIQ032L013
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L015

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLevel
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

open CategoryTheory


namespace Lech
universe u
variable {R : Type u} [CommRing R]

namespace MonomialSpanning
variable {h : ℕ} (z : Fin h → R)

noncomputable def pieceGenerator (a n : ℕ) (e : Bounded h a n) :
    IdealFiltration.Piece (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n :=
  Submodule.Quotient.mk (lift z a n e)

end MonomialSpanning
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.SourceGraded.target_graded _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory


namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)

variable {ι : Type*} (z : ι → R) (hz : Ideal.span (Set.range z) = I)

lemma generator_adjoin : Algebra.adjoin (R ⧸ I) (Set.range (generator I z hz)) = ⊤ := by
  let u : ι → reesAlgebra I := fun j => monomial I 1 ⟨z j, by
    rw [pow_one, ← hz]; exact Ideal.subset_span (Set.mem_range_self j)⟩
  have hupoly : Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (z j))) =
      reesAlgebra I := by
    rw [← adjoin_monomial_eq_reesAlgebra, ← hz, Submodule.map_span, Algebra.adjoin_span,
      ← Set.range_comp]
    rfl
  have hu : Algebra.adjoin R (Set.range u) = ⊤ := by
    apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, ← Set.range_comp]
    change Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (z j))) = _
    rw [hupoly]
    exact (Subalgebra.range_val _).symm
  let q := Ideal.Quotient.mkₐ R (shifted I)
  have hxR : Algebra.adjoin R (Set.range (generator I z hz)) = ⊤ := by
    have h := congrArg (Subalgebra.map q) hu
    rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top,
      (AlgHom.range_eq_top q).mpr Ideal.Quotient.mk_surjective] at h
    exact h
  apply Subalgebra.restrictScalars_injective R
  rw [Algebra.Subalgebra.restrictScalars_adjoin, hxR, sup_top_eq, Subalgebra.restrictScalars_top]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma polynomialMap_surjective : Function.Surjective (polynomialMap I z hz) :=
  Grading.polynomialMap_surjective _ _ _ (generator_adjoin I z hz)
end Lech.IdealGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory

attribute [local instance] Classical.propDecidable


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ} (z : Fin h → R)
  (hz : Ideal.span (Set.range z) = I)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev mapR : sourceGrade I h →+*ᵍ targetGrade I where
  toRingHom := (IdealGraded.polynomialMap I z hz).toRingHom
  map_mem := Graded.map_mem (IdealGraded.polynomialMap I z hz)

attribute [local instance] Homogeneous.awayAddCommGroup
attribute [local instance] kernel_addCommGroup kernel_module

end Lech.SourceGraded


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))

lemma denominator_unit : IsUnit (algebraMap (Poly R (h := h)) (Laurent R s) (denominator R s)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨single (negativeIndicator s) 1,?_⟩
  rw [denominator,algebraMap_single,single_mul_single,indicator_add_negative]
  simp only [mul_one]
  exact AddMonoidAlgebra.one_def.symm


lemma clear_single (e : exponents s) (r : R) : ∃ (n : ℕ) (a : Poly R (h := h)),
    single e r * algebraMap (Poly R (h := h)) (Laurent R s) ((denominator R s)^n) =
      algebraMap (Poly R (h := h)) (Laurent R s) a := by
  obtain ⟨n,a,ha⟩ := clear_exponent s e
  refine ⟨n,single a r,?_⟩
  rw [denominator,single_pow,one_pow,algebraMap_single,single_mul_single,ha,mul_one,
    algebraMap_single]
lemma clear_denominators (x : Laurent R s) : ∃ (n : ℕ) (a : Poly R (h := h)),
    x * algebraMap (Poly R (h := h)) (Laurent R s) ((denominator R s)^n) =
      algebraMap (Poly R (h := h)) (Laurent R s) a := by
  obtain ⟨f,rfl⟩ := coeffAddEquiv.symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero => exact ⟨0,0,by simp⟩
  | single e r => exact clear_single R s e r
  | add f g hf hg =>
    obtain ⟨n,a,ha⟩ := hf
    obtain ⟨m,b,hb⟩ := hg
    change ofCoeff f * _ = _ at ha
    change ofCoeff g * _ = _ at hb
    refine ⟨n+m,a*(denominator R s)^m + b*(denominator R s)^n,?_⟩
    change (ofCoeff f + ofCoeff g) * _ = _
    rw [pow_add,map_mul,add_mul,map_add,map_mul,map_mul]
    calc
      _ = (ofCoeff f * algebraMap _ _ ((denominator R s)^n)) *
          algebraMap _ _ ((denominator R s)^m) +
          (ofCoeff g * algebraMap _ _ ((denominator R s)^m)) *
          algebraMap _ _ ((denominator R s)^n) := by ring
      _ = _ := by rw [ha,hb]
 

instance localization : IsLocalization.Away (denominator R s) (Laurent R s) := by
  apply (isLocalization_iff (Submonoid.powers (denominator R s)) (Laurent R s)).mpr
  refine ⟨?_,?_,?_⟩
  · rintro ⟨a,n,rfl⟩
    rw [map_pow]
    exact (denominator_unit R s).pow n
  · intro x
    obtain ⟨n,a,ha⟩ := clear_denominators R s x
    exact ⟨⟨a,⟨(denominator R s)^n,n,rfl⟩⟩,ha⟩
  · intro a b hab
    exact ⟨1,by simpa using toLaurent_injective R s hab⟩


@[simp] lemma polynomialEquiv_X (i : Fin h) :
    polynomialEquiv R (MvPolynomial.X i) = AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  change (AddMonoidAlgebra.domCongr R R _) (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  rw [AddMonoidAlgebra.domCongr_single]
  congr 1
  ext j
  simp [Finsupp.single_apply,Pi.single_apply,eq_comm]
lemma polynomialEquiv_denominator :
    polynomialEquiv R (∏ i ∈ s, MvPolynomial.X i) = denominator R s := by
  classical
  rw [map_prod]
  simp_rw [polynomialEquiv_X]
  rw [AddMonoidAlgebra.prod_single]
  simp only [Finset.prod_const_one,denominator]
  congr 1
  ext i
  simp [indicator,Pi.single_apply]

lemma restrict_algebraMap {s t : Finset (Fin h)} (hst : s ⊆ t) (a : Poly R (h := h)) :
    restrict R hst (algebraMap _ _ a) = algebraMap _ _ a := by
  have he : (restrict R hst).comp (algebraMap (Poly R (h := h)) (Laurent R s)) =
      algebraMap (Poly R (h := h)) (Laurent R t) := by
    apply RingHom.coe_addMonoidHom_injective
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro e c
    change restrict R hst (algebraMap _ _ (single e c)) = algebraMap _ _ (single e c)
    rw [algebraMap_single,restrict_single,algebraMap_single]
    rfl
  exact RingHom.congr_fun he a

end Lech.PartialLaurent

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PartialLaurentTotalDegree
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
namespace Lech.PartialLaurent
open AddMonoidAlgebra HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
lemma denominator_homogeneous : denominator R s ∈ polyGrade R s.card := by
  rw [← total_indicator s]
  exact single_mem_gradeBy _ _ _
lemma algebraMap_homogeneous {n : ℕ} {a : Poly R (h := h)} (ha : a ∈ polyGrade R n) :
    algebraMap (Poly R (h := h)) (Laurent R s) a ∈ laurentGrade R s (n : ℤ) := by
  classical
  intro e he
  change e ∈ (Finsupp.mapDomain (fromNat s) a.coeff).support at he
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support he)
  rw [total_fromNat,ha v hv]
lemma algebraMap_homogeneous_iff {n : ℕ} {a : Poly R (h := h)} :
    algebraMap (Poly R (h := h)) (Laurent R s) a ∈ laurentGrade R s (n : ℤ) ↔
      a ∈ polyGrade R n := by
  refine ⟨?_,algebraMap_homogeneous R s⟩
  intro ha e he
  have hh : fromNat s e ∈ (algebraMap (Poly R (h := h)) (Laurent R s) a).coeff.support := by
    change fromNat s e ∈ (Finsupp.mapDomain (fromNat s) a.coeff).support
    rw [Finsupp.mem_support_iff,Finsupp.mapDomain_apply (fromNat_injective s)]
    exact Finsupp.mem_support_iff.mp he
  have hh := ha _ hh
  change totalDegreeInt s (fromNat s e) = (n : ℤ) at hh
  rw [total_fromNat] at hh
  exact Int.natCast_inj.mp hh

lemma inverse_denominator (n : ℕ) :
    algebraMap (Poly R (h := h)) (Laurent R s) ((denominator R s)^n) *
      single (n • negativeIndicator s) (1 : R) = 1 := by
  rw [denominator,single_pow,one_pow,algebraMap_single,single_mul_single,one_mul]
  have h : fromNat s (n • indicator s) + n • negativeIndicator s = 0 := by
    rw [map_nsmul,←nsmul_add,indicator_add_negative,nsmul_zero]
  rw [h]
  exact AddMonoidAlgebra.one_def.symm
end Lech.PartialLaurent


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TwistedLocalizationPieceMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.PartialLaurent
open AddMonoidAlgebra SetLike
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))

instance laurentScalarTower : IsScalarTower R (Poly R (h := h)) (Laurent R s) := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (mapDomainRingHom_comp_algebraMap (R := R) (A := R) (fromNat s)).symm

 

def localizationEquiv : Localization.Away (denominator R s) ≃ₐ[R] Laurent R s :=
  (IsLocalization.algEquiv (Submonoid.powers (denominator R s))
    (Localization.Away (denominator R s)) (Laurent R s)).restrictScalars R

lemma localizationEquiv_fraction (t n : ℕ) (a : polyGrade R (n*s.card+t)) :
    localizationEquiv R s
      (TwistedLocalization.fraction (polyGrade R) (f := denominator R s) t n a) =
      algebraMap (Poly R (h := h)) (Laurent R s) a * AddMonoidAlgebra.single (n • negativeIndicator s) 1 := by
  change IsLocalization.algEquiv (Submonoid.powers (denominator R s))
    (Localization.Away (denominator R s)) (Laurent R s)
      (Localization.mk (a : Poly R) ⟨(denominator R s)^n,n,rfl⟩) = _
  rw [Localization.mk_eq_mk',IsLocalization.algEquiv_mk']
  symm
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [mul_assoc,mul_comm (AddMonoidAlgebra.single _ _),inverse_denominator,mul_one]

lemma localizationEquiv_mem (t : ℕ)
    (x : TwistedLocalization.piece (polyGrade R) (f := denominator R s) (d := s.card) t) :
    localizationEquiv R s x ∈ laurentGrade R s (t : ℤ) := by
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction (polyGrade R)
    (denominator_homogeneous R s) t x
  rw [←ha,localizationEquiv_fraction]
  have hm := mul_mem_graded (algebraMap_homogeneous R s a.property)
    (inverse_denominator_homogeneous R s n)
  have hi : ((n*s.card+t : ℕ) : ℤ) + (-(n*s.card : ℕ) : ℤ) = (t : ℤ) := by omega
  simpa only [hi] using hm

 

def twistToLaurent (t : ℕ) :
    TwistedLocalization.piece (polyGrade R) (f := denominator R s) (d := s.card) t →ₗ[R]
      laurentGrade R s (t : ℤ) :=
  ((localizationEquiv R s).toLinearMap.comp
    (TwistedLocalization.piece (polyGrade R) (f := denominator R s) (d := s.card) t).subtype).codRestrict _ (localizationEquiv_mem R s t)

lemma twistToLaurent_surjective (t : ℕ) : Function.Surjective (twistToLaurent R s t) := by
  intro x
  obtain ⟨n,a,ha⟩ := clear_denominators R s x.val
  have hd : (denominator R s)^n ∈ polyGrade R (n*s.card) := by
    simpa only [nsmul_eq_mul,Nat.cast_id] using pow_mem_graded n (denominator_homogeneous R s)
  have hm := mul_mem_graded x.property (algebraMap_homogeneous R s hd)
  rw [ha] at hm
  have hap : a ∈ polyGrade R (n*s.card+t) := (algebraMap_homogeneous_iff R s).mp (by
    have hi : (t : ℤ) + ((n*s.card : ℕ) : ℤ) = ((n*s.card+t : ℕ) : ℤ) := by omega
    simpa only [hi] using hm)
  refine ⟨TwistedLocalization.pieceFraction (polyGrade R)
    (f := denominator R s) t n ⟨a,hap⟩,?_⟩
  apply Subtype.ext
  change localizationEquiv R s (TwistedLocalization.fraction _ t n ⟨a,hap⟩) = x.val
  rw [localizationEquiv_fraction,←ha,mul_assoc,inverse_denominator,mul_one]

end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ}

lemma polynomialEquiv_grade_iff {p : MvPolynomial (Fin h) R} {n : ℕ} :
    polynomialEquiv R p ∈ polyGrade R n ↔
      p ∈ MvPolynomial.homogeneousSubmodule (Fin h) R n := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,mem_supported]
  change (∀ a : Fin h → ℕ, a ∈ (polynomialEquiv R p).coeff.support →
    totalDegreeNat a = n) ↔ _
  constructor
  · intro hp a ha
    have hs : ((Finsupp.linearEquivFunOnFinite ℕ ℕ (Fin h)) a) ∈
        (polynomialEquiv R p).coeff.support := by
      rw [Finsupp.mem_support_iff]
      simpa [polynomialEquiv,coeff_domCongr] using Finsupp.mem_support_iff.mp ha
    have hh := hp _ hs
    change a.degree = n
    simpa only [totalDegreeNat,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
      Finsupp.degree_eq_sum,Finsupp.linearEquivFunOnFinite_apply] using hh
  · intro hp a ha
    let b := (Finsupp.linearEquivFunOnFinite ℕ ℕ (Fin h)).symm a
    have hb : b ∈ (AddMonoidAlgebra.coeff p).support := by
      rw [Finsupp.mem_support_iff]
      simpa [b,polynomialEquiv,coeff_domCongr] using Finsupp.mem_support_iff.mp ha
    have hh : b.degree = n := hp hb
    change (∑ i,a i) = n
    simpa only [Finsupp.degree_eq_sum,b,Finsupp.linearEquivFunOnFinite_symm_apply,
      Finsupp.linearEquivFunOnFinite_apply] using hh

end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra SetLike
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
attribute [local instance] MvPolynomial.gradedAlgebra

lemma polynomialDenominator_homogeneous :
    polynomialDenominator R s ∈ MvPolynomial.homogeneousSubmodule (Fin h) R s.card := by
  rw [←polynomialEquiv_grade_iff,polynomialDenominator,polynomialEquiv_denominator]
  exact denominator_homogeneous R s

instance polynomialLaurentAlgebra : Algebra (MvPolynomial (Fin h) R) (Laurent R s) :=
  ((algebraMap (Poly R (h := h)) (Laurent R s)).comp (polynomialEquiv R).toRingHom).toAlgebra

@[simp] lemma polynomial_algebraMap (a : MvPolynomial (Fin h) R) :
    algebraMap (MvPolynomial (Fin h) R) (Laurent R s) a =
      algebraMap (Poly R (h := h)) (Laurent R s) (polynomialEquiv R a) := rfl

instance polynomialLaurentTower : IsScalarTower R (MvPolynomial (Fin h) R) (Laurent R s) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  change algebraMap R (Laurent R s) r = algebraMap (Poly R) (Laurent R s)
    (polynomialEquiv R (algebraMap R (MvPolynomial (Fin h) R) r))
  rw [AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply R (Poly R) (Laurent R s) r

 

instance polynomialLocalization : IsLocalization.Away (polynomialDenominator R s) (Laurent R s) := by
  apply IsLocalization.of_ringEquiv_left (polynomialEquiv R).toRingEquiv
    (M₁ := Submonoid.powers (denominator R s))
  · rw [Submonoid.map_powers]
    congr 1
    exact polynomialEquiv_denominator R s
  · intro a
    rfl

def polynomialLocalizationEquiv : Localization.Away (polynomialDenominator R s) ≃ₐ[R] Laurent R s :=
  (IsLocalization.algEquiv (Submonoid.powers (polynomialDenominator R s))
    (Localization.Away (polynomialDenominator R s)) (Laurent R s)).restrictScalars R

lemma polynomialLocalizationEquiv_fraction (t n : ℕ)
    (a : MvPolynomial.homogeneousSubmodule (Fin h) R (n*s.card+t)) :
    polynomialLocalizationEquiv R s
      (TwistedLocalization.fraction (MvPolynomial.homogeneousSubmodule (Fin h) R)
        (f := polynomialDenominator R s) t n a) =
    algebraMap (Poly R (h := h)) (Laurent R s) (polynomialEquiv R a) *
      AddMonoidAlgebra.single (n • negativeIndicator s) 1 := by
  change IsLocalization.algEquiv (Submonoid.powers (polynomialDenominator R s))
    (Localization.Away (polynomialDenominator R s)) (Laurent R s)
      (Localization.mk (a : MvPolynomial (Fin h) R) ⟨(polynomialDenominator R s)^n,n,rfl⟩) = _
  rw [Localization.mk_eq_mk',IsLocalization.algEquiv_mk']
  symm
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  simp only [polynomial_algebraMap,map_pow,polynomialDenominator,polynomialEquiv_denominator]
  rw [mul_assoc,mul_comm (AddMonoidAlgebra.single _ _),←map_pow,inverse_denominator,mul_one]

lemma polynomialLocalizationEquiv_mem (t : ℕ)
    (x : TwistedLocalization.piece (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (f := polynomialDenominator R s) (d := s.card) t) :
    polynomialLocalizationEquiv R s x ∈ laurentGrade R s (t : ℤ) := by
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction _
    (polynomialDenominator_homogeneous R s) t x
  rw [←ha,polynomialLocalizationEquiv_fraction]
  have hm := mul_mem_graded (algebraMap_homogeneous R s
    ((polynomialEquiv_grade_iff R).mpr a.property)) (inverse_denominator_homogeneous R s n)
  have hi : ((n*s.card+t : ℕ) : ℤ) + (-(n*s.card : ℕ) : ℤ) = (t : ℤ) := by omega
  simpa only [hi] using hm

def polynomialTwistToLaurent (t : ℕ) :
    TwistedLocalization.piece (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (f := polynomialDenominator R s) (d := s.card) t →ₗ[R] laurentGrade R s (t : ℤ) :=
  ((polynomialLocalizationEquiv R s).toLinearMap.comp
    (TwistedLocalization.piece (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (f := polynomialDenominator R s) (d := s.card) t).subtype).codRestrict _
        (polynomialLocalizationEquiv_mem R s t)

lemma polynomialTwistToLaurent_surjective (t : ℕ) :
    Function.Surjective (polynomialTwistToLaurent R s t) := by
  intro x
  obtain ⟨y,hy⟩ := twistToLaurent_surjective R s t x
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction (polyGrade R)
    (denominator_homogeneous R s) t y
  have hx : algebraMap (Poly R (h := h)) (Laurent R s) a *
      AddMonoidAlgebra.single (n • negativeIndicator s) 1 = x.val := by
    rw [←localizationEquiv_fraction R s t n a,ha]
    exact congrArg Subtype.val hy
  let p := (polynomialEquiv R).symm (a : Poly R (h := h))
  have hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin h) R (n*s.card+t) := by
    rw [←polynomialEquiv_grade_iff]
    simpa only [p,AlgEquiv.apply_symm_apply] using a.property
  refine ⟨TwistedLocalization.pieceFraction _ (f := polynomialDenominator R s) t n ⟨p,hp⟩,?_⟩
  apply Subtype.ext
  change polynomialLocalizationEquiv R s (TwistedLocalization.fraction _ t n ⟨p,hp⟩) = x.val
  rw [polynomialLocalizationEquiv_fraction]
  simpa only [p,AlgEquiv.apply_symm_apply] using hx

 

def polynomialTwistEquiv (t : ℕ) :
    TwistedLocalization.piece (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (f := polynomialDenominator R s) (d := s.card) t ≃ₗ[R] laurentGrade R s (t : ℤ) :=
  LinearEquiv.ofBijective (polynomialTwistToLaurent R s t)
    ⟨fun _ _ he => Subtype.ext ((polynomialLocalizationEquiv R s).injective
      (congrArg Subtype.val he)),polynomialTwistToLaurent_surjective R s t⟩
end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra SetLike
universe u
variable (R : Type u) [CommRing R] {h : ℕ} {s v : Finset (Fin h)} (hsv : s ⊆ v)
attribute [local instance] MvPolynomial.gradedAlgebra

 
def restrictAlgHom : Laurent R s →ₐ[R] Laurent R v :=
  { restrict R hsv with
    commutes' := fun r => by
      change restrict R hsv (algebraMap R (Laurent R s) r) = algebraMap R (Laurent R v) r
      rw [IsScalarTower.algebraMap_apply R (Poly R (h := h)) (Laurent R s),
        restrict_algebraMap, ←IsScalarTower.algebraMap_apply R (Poly R (h := h)) (Laurent R v)] }

@[simp] lemma polynomialLocalizationEquiv_algebraMap (a : MvPolynomial (Fin h) R) :
    polynomialLocalizationEquiv R s (algebraMap _ _ a) =
      algebraMap _ (Laurent R s) a := by
  exact (IsLocalization.algEquiv (Submonoid.powers (polynomialDenominator R s))
    (Localization.Away (polynomialDenominator R s)) (Laurent R s)).commutes a

 

lemma polynomialLocalizationEquiv_naturality :
    (restrictAlgHom R hsv).comp (polynomialLocalizationEquiv R s).toAlgHom =
    (polynomialLocalizationEquiv R v).toAlgHom.comp
      (TwistedLocalization.ambientTo (R := R)
        (GradedChart.denominator_dvd (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) hsv)) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (polynomialDenominator R s))
  apply AlgHom.ext
  intro a
  change restrict R hsv (polynomialLocalizationEquiv R s (algebraMap _ _ a)) =
    polynomialLocalizationEquiv R v (TwistedLocalization.ambientTo (R := R)
      (GradedChart.denominator_dvd (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) hsv)
      (algebraMap _ _ a))
  rw [polynomialLocalizationEquiv_algebraMap,TwistedLocalization.ambientTo_algebraMap]
  change restrict R hsv (algebraMap (MvPolynomial (Fin h) R) (Laurent R s) a) =
    polynomialLocalizationEquiv R v
      (algebraMap (MvPolynomial (Fin h) R) (Localization.Away (polynomialDenominator R v)) a)
  rw [polynomialLocalizationEquiv_algebraMap,polynomial_algebraMap,restrict_algebraMap,
    polynomial_algebraMap]



def polynomialCechEquiv (s : Finset (Fin h)) (t : ℕ) :
    GradedChart.term (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) s t ≃ₗ[R]
      homogeneous R s (t : ℤ) :=
  (polynomialTwistEquiv R s t).trans
    (LinearEquiv.ofEq _ _ (homogeneous_eq_grade R s (t : ℤ)).symm)

lemma polynomialCechEquiv_naturality (t : ℕ)
    (x : GradedChart.term (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) s t) :
    polynomialCechEquiv R v t
      (GradedChart.restrict (MvPolynomial.homogeneousSubmodule (Fin h) R)
        MvPolynomial.X (fun i => MvPolynomial.isHomogeneous_X R i) hsv t x) =
    coefficientChartRestrict R hsv (t : ℤ) (polynomialCechEquiv R s t x) := by
  apply Subtype.ext
  exact (AlgHom.congr_fun (polynomialLocalizationEquiv_naturality R hsv) x.val).symm
end Lech.PartialLaurent
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedChartCochains
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.PartialLaurent
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev polynomialCochains (h n t : ℕ) :=
  GradedChart.cochains (MvPolynomial.homogeneousSubmodule (Fin h) R)
    (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) n t

def polynomialD (h n t : ℕ) : polynomialCochains R h n t →ₗ[R] polynomialCochains R h (n+1) t :=
  GradedChart.d _ MvPolynomial.X (MvPolynomial.isHomogeneous_X R) n t

def polynomialCochainsEquiv (h n t : ℕ) : polynomialCochains R h n t ≃ₗ[R]
    ActualCech.laurentCochains R h n (t : ℤ) :=
  LinearEquiv.piCongrRight (fun a => polynomialCechEquiv R (ActualCech.intersection a) t)

lemma polynomialCochainsEquiv_d (h n t : ℕ) (f : polynomialCochains R h n t) :
    polynomialCochainsEquiv R h (n+1) t (polynomialD R h n t f) =
      ActualCech.laurentD R h n (t : ℤ) (polynomialCochainsEquiv R h n t f) := by
  funext a
  change polynomialCechEquiv R (ActualCech.intersection a) t
    (∑ i : Fin (n+1), (-1 : R)^i.val • GradedChart.restrict _ _ _
      (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))) = _
  simp only [map_sum,map_smul,polynomialCechEquiv_naturality]
  rfl

lemma polynomialD_square (h n t : ℕ) (f : polynomialCochains R h n t) :
    polynomialD R h (n+1) t (polynomialD R h n t f)=0 := by
  apply (polynomialCochainsEquiv R h (n+2) t).injective
  rw [polynomialCochainsEquiv_d,polynomialCochainsEquiv_d,ActualCech.laurentD_square,map_zero]


end Lech.PartialLaurent


namespace Lech.RestrictedPolynomialCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev cochains (h n t : ℕ) := GradedChart.cochains (grade R S h) MvPolynomial.X n t

def d (h n t : ℕ) : cochains R S h n t →ₗ[R] cochains R S h (n+1) t :=
  GradedChart.d _ MvPolynomial.X (MvPolynomial.isHomogeneous_X S) n t

end Lech.RestrictedPolynomialCech


namespace Lech.ImageCech
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)


def mapCochains (n t : ℕ) : GradedChart.cochains G y n t →ₗ[R] cochains G H g y n t :=
  LinearMap.pi (fun a => (mapTerm G H g hg y hy (ActualCech.intersection a) t).comp
    (LinearMap.proj a))

include hy in
lemma mapCochains_surjective (hsurj : Function.Surjective g) (n t : ℕ) :
    Function.Surjective (mapCochains G H g hg y hy n t) := by
  intro f
  choose k hk using fun a => mapTerm_surjective G H g hg y hy hsurj
    (ActualCech.intersection a) t (f a)
  exact ⟨k,funext hk⟩
end Lech.ImageCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrincipalCoverRegularRegularMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductLaurent
open AddMonoidAlgebra Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def chartMap (σ : Fin n → Bool) : ProductLinearChart.Ring R n →ₐ[R] Ring R n :=
  mapDomainAlgHom R R (signedExponent n σ)
lemma chartMap_injective (σ : Fin n → Bool) : Function.Injective (chartMap R n σ) :=
  mapDomain_injective (signedExponent_injective n σ)
lemma chartMap_monomial (σ : Fin n → Bool) (e : Fin n →₀ ℕ) (r : R) :
    chartMap R n σ (MvPolynomial.monomial e r)=single (signedExponent n σ e) r :=
  mapDomain_single

def monomialUnit (e : Exponent n) : (Ring R n)ˣ where
  val := single e 1
  inv := single (-e) 1
  val_inv := by rw [single_mul_single,add_neg_cancel,one_mul,←one_def]
  inv_val := by rw [single_mul_single,neg_add_cancel,one_mul,←one_def]
abbrev variableUnit (i : Fin n) : (Ring R n)ˣ := monomialUnit R n (Finsupp.single i 1)
lemma monomialUnit_add (e f : Exponent n) : monomialUnit R n (e+f)=monomialUnit R n e*monomialUnit R n f := by
  apply Units.ext
  change single (e+f) (1:R)=single e 1*single f 1
  rw [single_mul_single,one_mul]
lemma monomialUnit_neg (e : Exponent n) : monomialUnit R n (-e)=(monomialUnit R n e)⁻¹ := by
  apply Units.ext
  rfl
lemma chartMap_X (σ : Fin n → Bool) (i : Fin n) :
    chartMap R n σ (MvPolynomial.X i)=(if σ i then (variableUnit R n i)⁻¹ else variableUnit R n i : (Ring R n)ˣ) := by
  rw [MvPolynomial.X,chartMap_monomial]
  have he : signedExponent n σ (Finsupp.single i 1)=if σ i then -Finsupp.single i 1 else Finsupp.single i 1 := by
    ext j
    by_cases hj : j=i
    · subst j; cases h : σ i <;> simp [signedExponent_apply,h]
    · cases h : σ i <;> simp [signedExponent_apply,hj]
  rw [he]
  cases h : σ i <;> simp only [Bool.false_eq_true,↓reduceIte] <;> rfl
 

def chartUnit (σ : Fin n → Bool) : (Ring R n)ˣ := ∏ i,if σ i then variableUnit R n i else 1
lemma chartMap_a (σ : Fin n → Bool) (i : Fin n) :
    chartMap R n σ (ProductLinearChart.a R n σ i)=
      (if σ i then (variableUnit R n i)⁻¹ else 1 : (Ring R n)ˣ)*(variableUnit R n i:Ring R n) := by
  cases hs : σ i
  · simp only [ProductLinearChart.a,hs,Bool.false_eq_true,↓reduceIte,chartMap_X,Units.val_one,one_mul]
  · simp only [ProductLinearChart.a,hs,↓reduceIte,map_one,Units.inv_mul]
lemma chartMap_b (σ : Fin n → Bool) (i : Fin n) :
    chartMap R n σ (ProductLinearChart.b R n σ i)=
      (if σ i then (variableUnit R n i)⁻¹ else 1 : (Ring R n)ˣ) := by
  cases hs : σ i <;> simp [ProductLinearChart.b,hs,chartMap_X]
 
def binaryForm : (Ring R n)[X] := ∏ i,(C (variableUnit R n i:Ring R n)*Polynomial.X+1)
lemma chartMap_factor (σ : Fin n → Bool) (i : Fin n) :
    (C (ProductLinearChart.a R n σ i)*Polynomial.X+C (ProductLinearChart.b R n σ i)).map
      (chartMap R n σ).toRingHom=
    C (if σ i then (↑((variableUnit R n i)⁻¹) : Ring R n) else 1)*
      (C (variableUnit R n i:Ring R n)*Polynomial.X+1) := by
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X]
  change C (chartMap R n σ (ProductLinearChart.a R n σ i))*Polynomial.X+
    C (chartMap R n σ (ProductLinearChart.b R n σ i))=_
  rw [chartMap_a,chartMap_b]
  cases hi : σ i <;> simp only [Bool.false_eq_true,↓reduceIte,Units.val_one,C_1,one_mul]
  rw [map_mul,mul_add,mul_one,mul_assoc]
lemma chartUnit_inv (σ : Fin n → Bool) :
    (chartUnit R n σ)⁻¹=∏ i,if σ i then (variableUnit R n i)⁻¹ else 1 := by
  rw [chartUnit,←Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases h : σ i <;> simp
lemma chartMap_product (σ : Fin n → Bool) :
    (ProductLinearChart.product R n σ).map (chartMap R n σ).toRingHom=
      C (↑((chartUnit R n σ)⁻¹) : Ring R n)*binaryForm R n := by
  unfold binaryForm
  rw [ProductLinearChart.product,Polynomial.map_prod]
  simp_rw [chartMap_factor]
  rw [Finset.prod_mul_distrib]
  have hunit : (∏ i,if σ i then (↑((variableUnit R n i)⁻¹) : Ring R n) else 1)=
      (↑((chartUnit R n σ)⁻¹) : Ring R n) := by
    rw [chartUnit_inv]
    rw [Units.coe_prod]
    apply Finset.prod_congr rfl
    intro i _
    cases h : σ i <;> rfl
  rw [←map_prod,hunit]
lemma chartMap_coefficient (σ : Fin n → Bool) (k : ℕ) :
    chartMap R n σ ((ProductLinearChart.product R n σ).coeff k)=
      (↑((chartUnit R n σ)⁻¹) : Ring R n)*(binaryForm R n).coeff k := by
  have h := congrArg (fun p : (Ring R n)[X] => p.coeff k) (chartMap_product R n σ)
  simpa only [Polynomial.coeff_map,Polynomial.coeff_C_mul,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using h


def clearingBound (x : Ring R n) : ℕ :=
  x.coeff.support.sup (fun e => Finset.univ.sup (fun i : Fin n => (e i).natAbs))
lemma clearingBound_nonneg (x : Ring R n) (e : Exponent n) (he : e∈x.coeff.support) (i : Fin n) :
    0≤(uniformExponent n (clearingBound R n x)+e) i := by
  have hn : (e i).natAbs ≤ clearingBound R n x :=
    (Finset.le_sup (f:=fun i : Fin n => (e i).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (f:=fun e : Exponent n => Finset.univ.sup (fun i : Fin n => (e i).natAbs)) he)
  have hn' : |e i|≤(clearingBound R n x:ℤ) := by
    rw [←Int.natCast_natAbs];exact_mod_cast hn
  have hl := neg_le_abs (e i)
  simp only [Finsupp.add_apply,uniformExponent_apply]
  omega
 

def clearedPolynomial (x : Ring R n) : ProductLinearChart.Ring R n :=
  ∑ e∈x.coeff.support,MvPolynomial.monomial
    (naturalPart n (uniformExponent n (clearingBound R n x)+e)) (x.coeff e)
lemma clearing_identity (x : Ring R n) :
    chartMap R n (fun _ => false) (clearedPolynomial R n x)=
      (monomialUnit R n (uniformExponent n (clearingBound R n x)):Ring R n)*x := by
  rw [clearedPolynomial,map_sum]
  simp only [chartMap_monomial]
  calc
    _ = ∑ e∈x.coeff.support,single (uniformExponent n (clearingBound R n x)+e) (x.coeff e) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [naturalPart_lift n _ (clearingBound_nonneg R n x e he)]
    _ = single (uniformExponent n (clearingBound R n x)) (1:R)*
        (∑ e∈x.coeff.support,single e (x.coeff e)) := by
      rw [Finset.mul_sum]
      simp only [single_mul_single,one_mul]
    _ = _ := by
      change _ * x.coeff.sum single=_
      rw [AddMonoidAlgebra.sum_coeff_single]
      rfl
 

theorem chartMap_regular (p : ProductLinearChart.Ring R n) (hp : IsRegular p) :
    IsRegular (chartMap R n (fun _ => false) p) := by
  have hz (x : Ring R n) (hx : chartMap R n (fun _ => false) p*x=0) : x=0 := by
    let u := monomialUnit R n (uniformExponent n (clearingBound R n x))
    have hc : chartMap R n (fun _ => false) (p*clearedPolynomial R n x)=0 := by
      rw [map_mul,clearing_identity]
      change chartMap R n (fun _ => false) p*((u:Ring R n)*x)=0
      rw [mul_left_comm,hx,mul_zero]
    have hc' : p*clearedPolynomial R n x=0 :=
      (chartMap_injective R n (fun _ => false)) (hc.trans (map_zero _).symm)
    have hpoly : clearedPolynomial R n x=0 := hp.left (by simpa only [mul_zero] using hc')
    have heq : (u:Ring R n)*x=0 := by
      rw [←clearing_identity,hpoly,map_zero]
    exact u.isUnit.isRegular.left (by simpa only [mul_zero] using heq)
  rw [isRegular_iff_eq_zero_of_mul]
  exact ⟨hz,fun x hx => hz x (by simpa only [mul_comm] using hx)⟩
lemma binaryForm_coefficient_regular (k : Fin (n+1)) : IsRegular ((binaryForm R n).coeff k) := by
  have hf : chartUnit R n (fun _ => false)=1 := by simp [chartUnit]
  have hc := chartMap_regular R n ((ProductLinearChart.product R n (fun _ => false)).coeff k)
    (ProductLinearChart.coefficient_regular R n (fun _ => false) k)
  rwa [chartMap_coefficient,hf,inv_one,Units.val_one,one_mul] at hc
end Lech.ProductLaurent


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechPrismPrimitive
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open AlternatingCech
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma faceSlice_delta (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p) :
    faceSlice R n k (p+1) (delta R (LaurentModule R (n+1)) p f)=
    delta R (LaurentModule R n) p (faceSlice R n k p f) := by
  apply evaluation_injective R (LaurentModule R n) (p+1)
  apply funext;intro a
  rw [faceSlice_eval,evaluation_delta,evaluation_delta]
  simp only [FiniteCoverCech.delta,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [faceSlice_eval]
  rfl
lemma faceSlice_lift (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R n) (ι:=Chart n) p) :
    faceSlice R n k p (faceLift R n k p f)=f := by
  apply evaluation_injective R (LaurentModule R n) p
  apply funext;intro a
  rw [faceSlice_eval,faceLift_eval R n k p f _ (fun _ => rfl),exponentSlice_insert]
  rfl
end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverFaceSlice
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.ProductSourceCover
open AlternatingCech
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma faceSlice_kernel (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p)
    (hf : f∈cochains R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) p) :
    faceSlice R n k p f=0 ↔
      f∈cochains R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons (k-1) m)) p := by
  constructor
  · intro hz a
    apply (neighbor_mem_iff R n k m _ _ (hf a)).mpr
    intro ht
    have ha : trueFace n ∘ (Fin.tail ∘ a)=a := by
      funext i j
      refine Fin.cases ?_ (fun _ => rfl) j
      exact (ht (a i) (by simp [FiniteCoverCech.intersection])).symm
    have hh := congrArg (fun g => evaluation R (LaurentModule R n) p g (Fin.tail ∘ a)) hz
    rw [faceSlice_eval,ha,map_zero] at hh
    exact hh
  · intro hl
    apply evaluation_injective R (LaurentModule R n) p
    apply funext;intro a
    rw [faceSlice_eval,map_zero]
    apply (neighbor_mem_iff R n k m _ _ (hf (trueFace n ∘ a))).mp (hl (trueFace n ∘ a))
    intro σ hσ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hσ
    rfl

end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechUnaugmentedComplex
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open AlternatingCech CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma ordinarySections_mono (m : Fin n → ℤ) : Monotone (ordinarySections R n m) :=
  zeroAugmentation_mono R (LaurentModule R n) (sections R n m) (sections_mono R n m)
lemma ordinaryCochains_pos (m : Fin n → ℤ) (p : ℕ) (hp : 0<p) :
    ordinaryCochains R n m p=divisorCochains R n m p :=
  zeroAug_cochains_pos R (LaurentModule R n) (sections R n m) p hp
lemma ordinaryCochains_zero (m : Fin n → ℤ) (f : ordinaryCochains R n m 0) : f=0 :=
  Subtype.ext (zeroAug_cochains_zero R (LaurentModule R n) (sections R n m) f.val f.property)
lemma ordinary_slice_mem (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : ordinaryCochains R (n+1) (Fin.cons k m) p) :
    faceSlice R n k p f.val∈ordinaryCochains R n m p := by
  cases p with
  | zero =>
    rw [ordinaryCochains_zero R (n+1) (Fin.cons k m) f]
    change faceSlice R n k 0 0∈ordinaryCochains R n m 0
    rw [map_zero]
    exact (ordinaryCochains R n m 0).zero_mem
  | succ p =>
    rw [ordinaryCochains_pos R n m (p+1) (by omega)]
    apply faceSlice_mem R n k m
    exact zeroAug_cochains_le R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) (p+1) f.property
lemma ordinary_lift_mem (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : ordinaryCochains R n m p) : faceLift R n k p f.val∈ordinaryCochains R (n+1) (Fin.cons k m) p := by
  cases p with
  | zero =>
    rw [ordinaryCochains_zero R n m f]
    change faceLift R n k 0 0∈ordinaryCochains R (n+1) (Fin.cons k m) 0
    rw [map_zero]
    exact (ordinaryCochains R (n+1) (Fin.cons k m) 0).zero_mem
  | succ p =>
    rw [ordinaryCochains_pos R (n+1) (Fin.cons k m) (p+1) (by omega)]
    apply faceLift_mem R n k m (p+1) (by omega)
    exact zeroAug_cochains_le R (LaurentModule R n) (sections R n m) (p+1) f.property
lemma ordinary_neighbor_le (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    ordinaryCochains R (n+1) (Fin.cons (k-1) m) p ≤ ordinaryCochains R (n+1) (Fin.cons k m) p := by
  intro f hf
  cases p with
  | zero => rw [zeroAug_cochains_zero R (LaurentModule R (n+1)) _ f hf];exact (ordinaryCochains R (n+1) _ 0).zero_mem
  | succ p =>
    rw [ordinaryCochains_pos R (n+1) (Fin.cons (k-1) m) (p+1) (by omega)] at hf
    rw [ordinaryCochains_pos R (n+1) (Fin.cons k m) (p+1) (by omega)]
    exact (divisorInclusion R n k m (p+1) ⟨f,hf⟩).property
def ordinaryComplex (m : Fin n → ℤ) :=
  complex R (LaurentModule R n) (ordinarySections R n m) (ordinarySections_mono R n m)
end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AssociatedGradedReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.SourceGraded.target_graded _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open DirectSum

namespace Lech.IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def initialForm (n : ℕ) : ↥(I^n) →ₗ[R] Ring I := (quotientR I).comp (monomial I n)

end Lech.IdealGraded

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverAllowedEmpty
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open AddMonoidAlgebra AlternatingCech CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
local instance ordinaryDecEq_r68bee7_1 : DecidableEq (Chart n) := LinearOrder.toDecidableEq
omit [LinearOrder (Chart n)] in
lemma ordinary_zero_isZero (m : Fin n → ℤ) : IsZero ((ordinaryComplex R n m).X 0) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (ordinaryCochains R n m 0)
  exact subsingleton_of_forall_eq 0 (ordinaryCochains_zero R n m)
omit [LinearOrder (Chart n)] in
lemma ordinary_homology_zero (m : Fin n → ℤ) : IsZero ((ordinaryComplex R n m).homology 0) := by
  exact (HomologicalComplex.ExactAt.of_isZero (ordinary_zero_isZero R n m)).isZero_homology


end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AlternatingCech CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma ordinary_slice_zero (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p)
    (hf : f∈ordinaryCochains R (n+1) (Fin.cons (k-1) m) p) : faceSlice R n k p f=0 := by
  apply (faceSlice_kernel R n k m p f
    (zeroAug_cochains_le R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) p
      (ordinary_neighbor_le R n k m p hf))).mpr
  exact zeroAug_cochains_le R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons (k-1) m)) p hf
 

def ordinaryDivisorSequence (k : ℤ) (m : Fin n → ℤ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  complexSequence R (LaurentModule R (n+1)) (LaurentModule R (n+1)) (LaurentModule R n)
    (ordinarySections R (n+1) (Fin.cons (k-1) m)) (ordinarySections R (n+1) (Fin.cons k m)) (ordinarySections R n m)
    (ordinarySections_mono R (n+1) (Fin.cons (k-1) m)) (ordinarySections_mono R (n+1) (Fin.cons k m)) (ordinarySections_mono R n m)
    (fun _ => LinearMap.id) (faceSlice R n k)
    (fun p _ hf => ordinary_neighbor_le R n k m p hf) (fun p f hf => ordinary_slice_mem R n k m p ⟨f,hf⟩)
    (fun _ _ => rfl) (faceSlice_delta R n k) (ordinary_slice_zero R n k m)
theorem ordinaryDivisorSequence_shortExact (k : ℤ) (m : Fin n → ℤ) :
    (ordinaryDivisorSequence R n k m).ShortExact := by
  unfold ordinaryDivisorSequence
  apply complexSequence_shortExact_injective
  · intro p
    exact Function.injective_id
  · intro p f hf hz
    refine ⟨f,?_,rfl⟩
    cases p with
    | zero =>
      rw [zeroAug_cochains_zero R (LaurentModule R (n+1)) _ f hf]
      exact (ordinaryCochains R (n+1) _ 0).zero_mem
    | succ p =>
      change f∈ordinaryCochains R (n+1) (Fin.cons (k-1) m) (p+1)
      rw [ordinaryCochains_pos R (n+1) (Fin.cons (k-1) m) (p+1) (by omega)]
      exact (faceSlice_kernel R n k m (p+1) f
        (zeroAug_cochains_le R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) (p+1) hf)).mp hz
  · intro p f hf
    exact ⟨faceLift R n k p f,ordinary_lift_mem R n k m p ⟨f,hf⟩,faceSlice_lift R n k p f⟩
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
@[simp] lemma ordinaryDivisorSequence_X1 (k : ℤ) (m : Fin n → ℤ) :
    (ordinaryDivisorSequence R n k m).X₁=ordinaryComplex R (n+1) (Fin.cons (k-1) m) := rfl
@[simp] lemma ordinaryDivisorSequence_X2 (k : ℤ) (m : Fin n → ℤ) :
    (ordinaryDivisorSequence R n k m).X₂=ordinaryComplex R (n+1) (Fin.cons k m) := rfl
@[simp] lemma ordinaryDivisorSequence_X3 (k : ℤ) (m : Fin n → ℤ) :
    (ordinaryDivisorSequence R n k m).X₃=ordinaryComplex R n m := rfl
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverHighThreshold
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma monomialUnit_sum {ι : Type} (s : Finset ι) (e : ι → Exponent n) :
    ProductLaurent.monomialUnit R n (∑ i∈s,e i)=∏ i∈s,ProductLaurent.monomialUnit R n (e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty];apply Units.ext;rfl
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,ProductLaurent.monomialUnit_add,ih]
lemma chartUnit_monomial (σ : Chart n) :
    ProductLaurent.chartUnit R n σ=ProductLaurent.monomialUnit R n (twistExponent n (fun _ => 1) σ) := by
  have he : twistExponent n (fun _ => 1) σ=∑ i : Fin n,if σ i then Finsupp.single i 1 else 0 := by
    ext j
    simp only [twistExponent_apply,Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single j]
    · cases h : σ j <;> simp
    · intro i _ hij
      cases h : σ i <;> simp [Finsupp.single_eq_of_ne (Ne.symm hij)]
    · simp
  rw [he,monomialUnit_sum,ProductLaurent.chartUnit]
  apply Finset.prod_congr rfl
  intro i _
  cases hs : σ i
  · simp only [Bool.false_eq_true,↓reduceIte]
    apply Units.ext
    rfl
  · rfl
end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProjectiveCoefficientChart


open MvPolynomial HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
attribute [local instance] MvPolynomial.gradedAlgebra
variable {d : ℕ} (g : MvPolynomial (Fin (n+1)) R) (hg : g∈grading R n d)
lemma backward_localizationElem :
    backward R n k (Away.isLocalizationElem (isHomogeneous_X R k) hg)=evaluate R n k g := by
  convert backward_mk R n k d g (by simpa using hg) using 1; simp [Away.isLocalizationElem]
lemma equiv_evaluate_localizationElem :
    equiv R n k (evaluate R n k g)=Away.isLocalizationElem (isHomogeneous_X R k) hg := by
  apply (equiv R n k).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact (backward_localizationElem R n k g hg).symm


end Lech.ProjectiveCoefficientChart


namespace Lech.ProductSourceCover

section

section
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma monomialUnit_nsmul (e : Exponent n) (N : ℕ) :
    ProductLaurent.monomialUnit R n (N • e)=ProductLaurent.monomialUnit R n e^N := by
  induction N with
  | zero => rw [zero_smul,pow_zero];apply Units.ext;rfl
  | succ N ih => rw [succ_nsmul,ProductLaurent.monomialUnit_add,ih,pow_succ]
end


open Polynomial
universe u
end


universe u
end Lech.ProductSourceCover


namespace Lech.UniversalSplitting
open Polynomial
universe u

attribute [instance] Data.ring Data.algebra


end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootInvariantsWeightZero
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.RootInvariants

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroRightBaseAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroRightBaseScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

def algebraBaseMapRight : algebra f n hn t v hv d ⊗[A] B →ₐ[algebra f n hn t v hv d] d.S :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom A B d.S)
    (fun _ _ => Commute.all _ _)

lemma algebraBaseMapRight_eq : (algebraBaseMapRight f n hn t v hv d).restrictScalars A=
    ((algebraBaseMap f n hn t v hv d).restrictScalars A).comp
      (Algebra.TensorProduct.comm A (algebra f n hn t v hv d) B).toAlgHom := by
  ext x <;> simp [algebraBaseMapRight,algebraBaseMap]

end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroOverAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroOverScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroSectionsAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroDiagonalAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroBinaryFormAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroBinaryFormScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl


end


open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance weightZeroProductSectionAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)

end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_StandardFactorChartsL
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance instAlgebraS_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
end Lech.RootInvariants


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NativeDescentCanonicalAlg
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

lemma polynomial_square : (f.map (algebraMap A B)).map (algebraMap B (R (A := A) (B := B) (T := T)))=
    (f.map (algebraMap A T)).map (includeT (A := A) (B := B)).toRingHom := by
  simp only [Polynomial.map_map]
  congr 1
  rw [← IsScalarTower.algebraMap_eq A B (R (A := A) (B := B) (T := T))]
  exact (includeT (A := A) (B := B)).comp_algebraMap.symm

include hf in
lemma form : ((f.map (algebraMap A B)).map (algebraMap B (R (A := A) (B := B) (T := T)))).homogenize n=
    MvPolynomial.C (Units.map (includeT (A := A) (B := B)).toMonoidHom w:R (A := A) (B := B) (T := T))*∏ i,
      (MvPolynomial.C (includeT (a i))*MvPolynomial.X 0+MvPolynomial.C (includeT (b i))*MvPolynomial.X 1) := by
  rw [polynomial_square,Polynomial.homogenize_map,hf]
  simp only [map_mul,map_prod,map_add,MvPolynomial.map_C,MvPolynomial.map_X]
  rfl


def denominator (i : Fin n) : (R (A := A) (B := B) (T := T))ˣ :=
  FactorNormalization.denominator _ n (natDegree_map_le.trans (natDegree_map_le.trans hn))
    (algebraMap B _ t) (Units.map (algebraMap B (R (A := A) (B := B) (T := T))).toMonoidHom v)
    (Units.map (includeT (A := A) (B := B)).toMonoidHom w) (value f t v hv)
    (fun i => includeT (a i)) (fun i => includeT (b i)) (form f n w a b hf) i

lemma denominator_val (i : Fin n) :
    (denominator f n hn t v hv w a b hf i:R (A := A) (B := B) (T := T))=
      algebraMap B _ t*includeT (a i)+includeT (b i) :=
  FactorNormalization.denominator_val _ _ _ _ _ _ _ _ _ _ _

end Lech.UniversalFactorMap


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

lemma denominator_product :
    Units.map (includeT (A := A) (B := B)).toMonoidHom w*∏ i,denominator f n hn t v hv w a b hf i=
      Units.map (algebraMap B (R (A := A) (B := B) (T := T))).toMonoidHom v :=
  FactorNormalization.unit_product _ _ _ _ _ _ _ _ _ _

end Lech.UniversalFactorMap


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_UniversalFactorMapMapChart
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.FaithfullyFlat A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance mapChartUniqueAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance mapChartUniqueScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
end Lech.UniversalFactorMap


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.FaithfullyFlat A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (w w' : Tˣ) (a b a' b' : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))
  (hf' : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w':T)*∏ i,
    (MvPolynomial.C (a' i)*MvPolynomial.X 0+MvPolynomial.C (b' i)*MvPolynomial.X 1))
variable (c : Fin n → Tˣ) (ha : ∀ i,a' i=(c i:T)*a i) (hb : ∀ i,b' i=(c i:T)*b i)
include ha hb in
omit [Module.FaithfullyFlat A B] in
lemma denominator_rescale (i : Fin n) :
    denominator f n hn t v hv w' a' b' hf' i=
      Units.map (includeT (A:=A) (B:=B)).toMonoidHom (c i)*denominator f n hn t v hv w a b hf i := by
  apply Units.ext
  rw [Units.val_mul,denominator_val,denominator_val,ha,hb]
  change algebraMap B (R (A:=A) (B:=B) (T:=T)) t*includeT ((c i:T)*a i)+includeT ((c i:T)*b i)=
    includeT (A:=A) (B:=B) (c i:T)*(algebraMap B _ t*includeT (a i)+includeT (b i))
  simp only [map_mul]
  ring
end Lech.UniversalFactorMap


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.RootChartAtlas

section
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
abbrev GridD := RootInvariants.algebra (f R n k) n (hn R n k) t v hv d

end


open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
abbrev D := RootInvariants.algebra (f R n k) n (hn R n k) t v hv d
end Lech.RootChartAtlas


namespace Lech.LocalLine
open scoped TensorProduct
universe u v w z
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]
variable (L : Type z) [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]


attribute [local instance] OAI.Lech.LocalLine.instAlgebraTensorProduct_solutions
attribute [local instance] OAI.Lech.LocalLine.instIsScalarTowerTensorProduct_solutions
def trivial (e : S ⊗[R] M ≃ₗ[S] S) :
    (L ⊗[R] S) ⊗[L] (L ⊗[R] M) ≃ₗ[L ⊗[R] S] L ⊗[R] S :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R L (L ⊗[R] S) (L ⊗[R] S) M ≪≫ₗ
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R S (L ⊗[R] S) (L ⊗[R] S) M).symm ≪≫ₗ
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (L ⊗[R] S) _) e ≪≫ₗ
  TensorProduct.AlgebraTensorModule.rid S (L ⊗[R] S) (L ⊗[R] S)

omit [Module.FaithfullyFlat R S] in
lemma trivial_tmul (e : S ⊗[R] M ≃ₗ[S] S) (m : M) :
    trivial L e (1 ⊗ₜ[L] (1 ⊗ₜ[R] m))=1 ⊗ₜ[R] e (1 ⊗ₜ[R] m) := by
  simp only [trivial,LinearEquiv.trans_apply,TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    one_smul,TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  rw [Algebra.smul_def,mul_one]
  rfl


def basisEquiv (e : S ⊗[R] M ≃ₗ[S] S) (m : M)
    (hu : IsUnit (1 ⊗ₜ[R] e (1 ⊗ₜ[R] m) : L ⊗[R] S)) :
    L ≃ₗ[L] L ⊗[R] M :=
  UnitSection.equiv (L ⊗[R] S) (1 ⊗ₜ[R] m) (trivial L e) hu.unit
    ((trivial_tmul L e m).trans hu.unit_spec.symm)

lemma basisEquiv_apply (e : S ⊗[R] M ≃ₗ[S] S) (m : M)
    (hu : IsUnit (1 ⊗ₜ[R] e (1 ⊗ₜ[R] m) : L ⊗[R] S)) (x : L) :
    basisEquiv L e m hu x=x ⊗ₜ[R] m := by
  change x • ((1:L) ⊗ₜ[R] m)=_
  rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

lemma section_relation (e : S ⊗[R] M ≃ₗ[S] S) (m y : M) (r : L)
    (h : (algebraMap L (L ⊗[R] S) r)*(1 ⊗ₜ[R] e (1 ⊗ₜ[R] m))=
      1 ⊗ₜ[R] e (1 ⊗ₜ[R] y)) :
    r ⊗ₜ[R] m=(1:L) ⊗ₜ[R] y := by
  have hinj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := L) (B := L ⊗[R] S) (L ⊗[R] M)
  apply hinj
  apply (trivial L e).injective
  have ht : (1:L ⊗[R] S) ⊗ₜ[L] (r ⊗ₜ[R] m)=
      r • ((1:L ⊗[R] S) ⊗ₜ[L] ((1:L) ⊗ₜ[R] m)) := by
    rw [← TensorProduct.tmul_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  change trivial L e (1 ⊗ₜ[L] (r ⊗ₜ[R] m))=trivial L e (1 ⊗ₜ[L] ((1:L) ⊗ₜ[R] y))
  have hh : trivial L e (r • ((1:L ⊗[R] S) ⊗ₜ[L] ((1:L) ⊗ₜ[R] m)))=
      r • trivial L e ((1:L ⊗[R] S) ⊗ₜ[L] ((1:L) ⊗ₜ[R] m)) :=
    ((trivial L e).restrictScalars L).map_smul r _
  rw [ht,hh,trivial_tmul,trivial_tmul,Algebra.smul_def]
  exact h
end Lech.LocalLine


namespace Lech.RootInvariants


open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance tensorWorkAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedLineBasisHasBasis
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance gradedLineBasisAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)

end Lech.RootInvariants


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable [Module.FaithfullyFlat A B]

local instance transitionWorkAlgebra_r68bee7_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
abbrev commonExtension := C ⊗[algebra f n hn t v hv d] d.S

end Lech.RootInvariants


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechSignedUnit
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def monomialHom : Multiplicative (Exponent n) →* (Ring R n)ˣ where
  toFun e := monomialUnit R n e.toAdd
  map_one' := by apply Units.ext;exact (one_def).symm
  map_mul' := monomialUnit_add R n
lemma monomialUnit_zsmul (e : Exponent n) (m : ℤ) :
    monomialUnit R n (m • e)=(monomialUnit R n e)^m :=
  (monomialHom R n).map_zpow (Multiplicative.ofAdd e) m
lemma monomialUnit_sum {ι : Type*} (s : Finset ι) (e : ι → Exponent n) :
    monomialUnit R n (∑ i∈s,e i)=∏ i∈s,monomialUnit R n (e i) := by
  induction s using Finset.cons_induction with
  | empty => exact (monomialHom R n).map_one
  | cons a s ha ih => rw [Finset.sum_cons,Finset.prod_cons,monomialUnit_add,ih]
lemma signedProduct (m : Fin n → ℤ) (σ : Fin n → Bool) :
    (∏ i,(if σ i then variableUnit R n i else 1)^m i)=
      monomialUnit R n (ProductSourceCover.twistExponent n m σ) := by
  have he : ProductSourceCover.twistExponent n m σ=∑ i : Fin n, (if σ i then m i else 0) • Finsupp.single i 1 := by
    ext j
    simp only [ProductSourceCover.twistExponent_apply,Finset.sum_apply']
    rw [Finset.sum_eq_single j]
    · cases σ j <;> simp
    · intro b _ hb
      cases σ b <;> simp [Finsupp.single_eq_of_ne hb.symm]
    · simp
  rw [he,monomialUnit_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [monomialUnit_zsmul]
  cases σ i <;> simp only [Bool.false_eq_true,↓reduceIte,zpow_zero,one_zpow]
end Lech.ProductLaurent


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_OrderedRootBasis
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
open Polynomial
universe u

variable {R : Type u} [CommRing R] {n : ℕ} {f : R[X]}

 

theorem Data.exists_equiv (d e : Data R n f) :
    ∃ h : d.S ≃ₐ[R] e.S, ∀ i,h (d.roots i)=e.roots i := by
  obtain ⟨φ,hφ,hφu⟩ := d.universal e.S e.roots e.factorization
  obtain ⟨ψ,hψ,hψu⟩ := e.universal d.S d.roots d.factorization
  refine ⟨AlgEquiv.ofAlgHom φ ψ ?_ ?_,hφ⟩
  · apply e.hom_ext
    intro i
    change φ (ψ (e.roots i))=e.roots i
    rw [hψ,hφ]
  · apply d.hom_ext
    intro i
    change ψ (φ (d.roots i))=d.roots i
    rw [hφ,hψ]

 

theorem Data.exists_power_basis_of_top (d : Data R n f)
    (hf : f.natDegree≤n) (ht : f.coeff n=1) :
    ∃ b : Module.Basis (PowerIndex n) R d.S, ∀ e,b e=powerMonomial n d.roots e := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl h =>
      let : Subsingleton d.S := Module.subsingleton R _
      exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton d.S (PowerIndex n →₀ R)),
        fun _ => Subsingleton.elim _ _⟩
  | inr h =>
      have hn : f.natDegree=n := le_antisymm hf (le_natDegree_of_ne_zero (ht ▸ one_ne_zero))
      obtain ⟨e,b,hb⟩ := exists_power_data n R f (monic_of_natDegree_le_of_coeff_eq_one n hf ht) hn
      obtain ⟨φ,hφ⟩ := e.exists_equiv d
      refine ⟨b.map φ.toLinearEquiv,?_⟩
      intro x
      rw [Module.Basis.map_apply,hb]
      change φ (powerMonomial n e.roots x)=_
      have hh := map_powerMonomial φ.toMonoidHom n e.roots x
      change φ (powerMonomial n e.roots x)=powerMonomial n (fun i => φ (e.roots i)) x at hh
      rw [hh]
      congr 1
      funext i
      exact hφ i

end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootChartAtlasGlobalCoefficient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.PrimitiveRootModule
open Polynomial
open scoped TensorProduct
universe u
variable {A : Type u} [CommRing A]

def splitting (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) : UniversalSplitting.Data (chart f) n
    (BinaryChange.normalized (f.map (algebraMap A (chart f))) n (coordinate f) (valueUnit f)) := by
  let g := BinaryChange.normalized (f.map (algebraMap A (chart f))) n (coordinate f) (valueUnit f)
  have hdeg : (f.map (algebraMap A (chart f))).natDegree≤n := natDegree_map_le.trans hn
  have hgn : g.natDegree≤n :=
    (natDegree_C_mul_le _ _).trans (BinaryChange.transform_degree _ n (coordinate f))
  have hgt : g.coeff n=1 := BinaryChange.normalized_top _ (coordinate f) (valueUnit f)
    hdeg (eval_valueUnit f)
  exact Classical.choice (BinaryCover.ordered_splitting_of_top (chart f) n g hgn hgt)



end Lech.PrimitiveRootModule


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance moduleWork : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
end Lech.RootChartAtlas


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootOverlap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProjectiveRoot

open MvPolynomial HomogeneousLocalization ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra


variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hk : k ∈ s)


lemma isLocalization :
    let := coefficientAlgebra R n k s hk
    IsLocalization.Away (targetProduct R n k s) (Ring R n s) := by
  let := coefficientAlgebra R n k s hk
  let := chartAlgebra R n k s hk
  let : IsLocalization.Away
      (Away.isLocalizationElem (isHomogeneous_X R k)
        (projectiveRemainder_homogeneous R n k s)) (Ring R n s) :=
    Away.isLocalization_mul (isHomogeneous_X R k)
      (projectiveRemainder_homogeneous R n k s) (product_eq R n k s hk) (by decide)
  apply IsLocalization.of_ringEquiv_left (ProjectiveCoefficientChart.equiv R n k).toRingEquiv
    (M₁ := Submonoid.powers (Away.isLocalizationElem (isHomogeneous_X R k)
      (projectiveRemainder_homogeneous R n k s)))
  · rw [Submonoid.map_powers]
    congr 1
    rw [←projectiveRemainder_evaluate R n k s hk]
    exact ProjectiveCoefficientChart.equiv_evaluate_localizationElem R n k
      (projectiveRemainder R n k s) (projectiveRemainder_homogeneous R n k s)
  · intro a
    rfl

local instance canonicalRing : CommRing (Ring R n s) := inferInstance
variable [hks : Fact (k ∈ s)]
local instance coeffToIntersection : Algebra (UniversalCoefficientChart.Ring R n k) (Ring R n s) :=
  coefficientAlgebra R n k s hks.out
local instance coeffToIntersectionModule : Module (UniversalCoefficientChart.Ring R n k) (Ring R n s) := Algebra.toModule
local instance coeffLocalization :
    IsLocalization.Away (targetProduct R n k s) (Ring R n s) :=
  isLocalization R n k s hks.out


end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootRestriction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProjectiveRoot
open MvPolynomial HomogeneousLocalization ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma product_sdiff {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    product R n t = product R n s * product R n (t \ s) := by
  exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)


end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootUnfiltered
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)

def zeroTermEquiv (Q : ModuleCat.{u} R) (p : ℤ) :
    (complex I F h 0 (zero_order_bound I F) Q).X p ≃ₗ[R] (tensorComplex F Q).X p :=
  LinearEquiv.ofBijective (term I F h 0 Q p).subtype ⟨Subtype.val_injective,by
    intro x
    exact ⟨⟨x,by rw [zero_term_top]; trivial⟩,rfl⟩⟩

@[simp] lemma zeroTermEquiv_apply (Q : ModuleCat.{u} R) (p : ℤ)
    (x : (complex I F h 0 (zero_order_bound I F) Q).X p) :
    zeroTermEquiv I F h Q p x=x.val := rfl
end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichSpan
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
open Polynomial
universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]



variable {n : ℕ} {f : R[X]}
lemma Data.binaryPower_span_eq_top (d : Data R n f) (hf : f.natDegree≤n) (ht : f.coeff n=1) (t : R) :
    Submodule.span R (Set.range (binaryPower t n d.roots))=⊤ := by
  obtain ⟨b,hb⟩ := d.exists_power_basis_of_top hf ht
  apply top_unique
  rw [←b.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨e,rfl⟩
  rw [hb]
  exact powerMonomial_mem_binary_span t n d.roots e



theorem Data.exists_binary_basis (d : Data R n f) (hf : f.natDegree≤n) (ht : f.coeff n=1) (t : R) :
    ∃ b : Module.Basis (PowerIndex n) R d.S, ∀ e,b e=binaryPower t n d.roots e := by
  classical
  obtain ⟨b,hb⟩ := d.exists_power_basis_of_top hf ht
  let : Module.Finite R d.S := d.finite
  let g := Finsupp.linearCombination R (binaryPower t n d.roots)
  have hg : Function.Surjective g := by
    apply LinearMap.range_eq_top.mp
    rw [Finsupp.range_linearCombination]
    exact d.binaryPower_span_eq_top hf ht t
  have hbij := OrzechProperty.bijective_of_surjective_of_injective b.repr.symm.toLinearMap g
    b.repr.symm.injective hg
  let bb : Module.Basis (PowerIndex n) R d.S := Module.Basis.ofRepr (LinearEquiv.ofBijective g hbij).symm
  refine ⟨bb,?_⟩
  intro e
  change (LinearEquiv.ofBijective g hbij) (Finsupp.single e 1)=_
  simp [g]

end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.RootInvariants
open Polynomial UniversalSplitting
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance rootUlrichModuleAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootLineEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.RootInvariants
open Polynomial
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance lineEulerInstance1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance lineEulerInstance2 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl


end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootPermutation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProductLaurent
open AddMonoidAlgebra Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Equiv.Perm (Fin n))

def permute : Ring R n ≃ₐ[R] Ring R n := domCongr R R (Finsupp.domCongr σ)

lemma permute_ringHom_apply (x : Ring R n) :
    (permute R n σ).toRingHom x=permute R n σ x := rfl

lemma permute_variable (i : Fin n) :
    permute R n σ (variableUnit R n i : Ring R n)=(variableUnit R n (σ i) : Ring R n) := by
  change domCongr R R (Finsupp.domCongr σ) (single (Finsupp.single i 1) 1)=_
  rw [domCongr_single]
  congr 1
  ext j
  simp only [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply,Finsupp.single_apply]
  congr 1
  exact propext (σ.eq_symm_apply)

lemma permute_binaryForm : (binaryForm R n).map (permute R n σ).toRingHom=binaryForm R n := by
  simp only [binaryForm,Polynomial.map_prod,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_X,Polynomial.map_one,permute_ringHom_apply]
  simp only [permute_variable]
  exact Equiv.prod_comp σ (fun i => C (variableUnit R n i : Ring R n)*X+1)

lemma permute_coefficient (i : Fin (n+1)) :
    permute R n σ ((binaryForm R n).coeff i)=(binaryForm R n).coeff i := by
  simpa only [Polynomial.coeff_map,permute_ringHom_apply] using congrArg (fun p : (Ring R n)[X] => p.coeff i) (permute_binaryForm R n σ)

lemma permute_symm : (permute R n σ).symm=permute R n σ.symm := by
  simp only [permute,domCongr_symm,Finsupp.domCongr_symm]
end Lech.ProductLaurent

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootProjectiveEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.ProjectiveRoot
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

section Intersection
variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hs : s.Nonempty) [hks : Fact (k∈s)]
local instance projectiveEulerInstance1 : Algebra (UniversalCoefficientChart.Ring R n k) (Ring R n s) :=
  coefficientAlgebra R n k s hks.out

end Intersection



end Lech.ProjectiveRoot

end

end OAI
end


