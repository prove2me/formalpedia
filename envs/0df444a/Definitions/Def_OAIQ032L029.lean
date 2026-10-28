-- Prove2me | Definitions.Def_OAIQ032L029
-- name    : OAIQ032L029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:35:58.6717+00:00
-- url     : https://prove2.me/theorems/e1590377-0245-4c49-8d6e-92223ccd8295
-- title:
--   Definitions bundle OAIQ032L029 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 24 definitions, 2 instances and 24 theorems. The definitions and types are `OAI.Lech.ProductSourceCover.globalBasis`, `OAI.Lech.ProductSourceCover.globalCoefficientEquiv`, `OAI.Lech.ProductSourceCover.highTwistH0`, `OAI.Lech.ProductSourceCover.highTwistH0Basis`, `OAI.Lech.ProductSourceCover.ordinaryCohomologyIso`, `OAI.Lech.ProductSourceCover.ordinaryRingIso`, `OAI.Lech.ProductSourceCover.unaugmentedSource`, `OAI.Lech.ReesRoot.scalarCechHomotopy`, `OAI.Lech.ReesRoot.scalarCechIso`, `OAI.Lech.ReesRoot.scalarHomologyIso`, `OAI.Lech.ReesRoot.scalarSectionEquiv`, `OAI.Lech.RestrictedPolynomialImageCech.comparison`, `OAI.Lech.RestrictedPolynomialImageCech.complex`, `OAI.Lech.RootInvariants.consecutiveSection`, `OAI.Lech.RootInvariants.homogeneousSection`, `OAI.Lech.SourceGraded.degreeKernelAdd`, `OAI.Lech.SourceGraded.degreeKernelModule`, `OAI.Lech.SourceGraded.exceptionalCech`, `OAI.Lech.SourceGraded.filteredLayerSequence`, `OAI.Lech.SourceGraded.filteredReductionCech`, `OAI.Lech.SourceGraded.gradedMapR`, `OAI.Lech.SourceGraded.torsionGradedKernelAdd`, `OAI.Lech.SourceGraded.torsionGradedKernelModule`, `OAI.Lech.SourceGraded.twistMapR`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_GradedChartCochains`, `Multiplicity_LechCokernelComp`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechTorsionOf`, `Multiplicity_ProductSourceCoverAllowedEmpty`, `Multiplicity_ProductSourceCoverCechNat`, `Multiplicity_ProductSourceCoverOrdinaryPositive`, `Multiplicity_RestrictedPolynomialImageCechComparisonHomology`, `Multiplicity_RootInvariantsWeightZero`, `Multiplicity_RootPermutation`, `Multiplicity_RootUlrichModule`, `Multiplicity_ScalarCechComparison`, `Multiplicity_ScalarCechEuler`, `Multiplicity_ScalarChartComparison`, `Multiplicity_TorsionChartKernel`.
--
--   **Imports.** It imports the bundles `OAIQ032L024`, `OAIQ032L025`, `OAIQ032L026` and `OAIQ032L027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L030` and `OAIQ032L031`; the proofs of `OAI.Lech.ReesRoot.coefficientComparisonLinear_kernel_zero`, `OAI.Lech.ReesRoot.scalarEuler_value`, `OAI.Lech.ReesRoot.scalarHomology_value` and `OAI.Lech.SourceGraded.finiteThickening_homology_zeroClass`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L024
import Definitions.Def_OAIQ032L025
import Definitions.Def_OAIQ032L026
import Definitions.Def_OAIQ032L027

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

abbrev gradedMapR (n : ℕ) : sourceGrade I h n →ₗ[R] targetGrade I n :=
  Homogeneous.gradedMap (R := R) (A := MvPolynomial (Fin h) (R ⧸ I))
    (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) n

attribute [local instance] Homogeneous.awayAddCommGroup
attribute [local instance] kernel_addCommGroup kernel_module

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedChartCochains
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.RestrictedPolynomialImageCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  {h : ℕ} (H : ℕ → Submodule R B) [GradedAlgebra H]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (g : (RestrictedPolynomialCech.grade R S h) →+*ᵍ H)
  (hg : ∀ (r : R) (a : MvPolynomial (Fin h) S), g (r • a) = r • g a)

lemma mapCochains_naturality (n t : ℕ) (f : RestrictedPolynomialCech.cochains R S h n t) :
    mapCochains H g hg (n+1) t (RestrictedPolynomialCech.d R S h n t f) =
      d H g n t (mapCochains H g hg n t f) :=
  ImageCech.mapCochains_naturality _ H g hg MvPolynomial.X
    (MvPolynomial.isHomogeneous_X S) n t f

include hg in
lemma d_square (hsurj : Function.Surjective g) (n t : ℕ) (f : cochains H g n t) :
    d H g (n+1) t (d H g n t f)=0 := by
  obtain ⟨x,rfl⟩ := mapCochains_surjective H g hg hsurj n t f
  rw [←mapCochains_naturality,←mapCochains_naturality,
    RestrictedPolynomialCech.d_square,map_zero]


def complex (hsurj : Function.Surjective g) (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains H g n t))
    (fun n => ModuleCat.ofHom (d H g n t)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact d_square H g hg hsurj n t f)

 
def comparison (hsurj : Function.Surjective g) (t : ℕ) :
    RestrictedPolynomialCech.complex R S h t ⟶ complex H g hg hsurj t :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (mapCochains H g hg n t)) (fun n => by
    change (ModuleCat.ofHom (mapCochains H g hg n t)) ≫
      (CochainComplex.of.d (fun n => ModuleCat.of R (cochains H g n t))
        (fun n => ModuleCat.ofHom (d H g n t)) n (n+1)) =
      (CochainComplex.of.d (fun n => ModuleCat.of R (RestrictedPolynomialCech.cochains R S h n t))
        (fun n => ModuleCat.ofHom (RestrictedPolynomialCech.d R S h n t)) n (n+1)) ≫
        ModuleCat.ofHom (mapCochains H g hg (n+1) t)
    rw [CochainComplex.of_d,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (mapCochains_naturality H g hg n t f).symm)
end Lech.RestrictedPolynomialImageCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RestrictedPolynomialImageCechComparisonHomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)
  (ell : AllModuleLength R)
  {f : MvPolynomial (Fin h) (R ⧸ I)} {d : ℕ} (hf : f ∈ sourceGrade I h d)

attribute [local irreducible] TwistedLocalization.piece IdealGraded.polynomialMap
 

def twistMapR (t : ℕ) :=
  TwistedLocalization.pieceMap (R := R) (A := MvPolynomial (Fin h) (R ⧸ I))
    (B := IdealGraded.Ring I) (sourceGrade I h) hf (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) t

end Lech.SourceGraded


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)
  (ell : AllModuleLength R)
attribute [local instance] MvPolynomial.gradedAlgebra


def exceptionalCech (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  RestrictedPolynomialImageCech.complex (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I) (h := h) (targetGrade I) (mapR I z hz)
    (mapR_smul I z hz) (mapR_surjective I z hz) t


attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap ImageCech.mapTerm IdealGraded.polynomialMap

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece FilteredFraction.piece IdealGraded.polynomialMap


def filteredReductionCech (t : ℕ) :
    FilteredCech.complex I z (coordinate_mem I z hz) t ⟶ exceptionalCech I z hz t :=
  cochainOfMap
    (hX := fun n => ModuleCat.hom_ext (LinearMap.ext (LocalizationCech.d_square z
      (FilteredCech.term I z t) (FilteredCech.restriction_mem I z (coordinate_mem I z hz) t) n)))
    (hY := fun n => ModuleCat.hom_ext (LinearMap.ext (RestrictedPolynomialImageCech.d_square
      (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I) (h := h) (targetGrade I)
      (mapR I z hz) (mapR_smul I z hz) (mapR_surjective I z hz) n t)))
    (fun n => ModuleCat.ofHom (filteredReductionCochains I z hz n t))
    (fun n x => (filteredReductionCochains_d I z hz n t x).symm)

lemma filteredReductionCech_comp_zero (t : ℕ) :
    FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_succ t) ≫
      filteredReductionCech I z hz t=0 := by
  ext n x
  have hx : LocalizationCech.inclusionLinear z (FilteredCech.term I z (t+1))
      (FilteredCech.term I z t) (fun _ => FilteredFraction.antitone I _ _ (Nat.le_succ t)) n x ∈
      (filteredReductionCochains I z hz n t).ker := by
    rw [filteredReductionCochains_kernel]
    exact ⟨x,rfl⟩
  exact hx

 

def filteredLayerSequence (t : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_succ t))
    (filteredReductionCech I z hz t) (filteredReductionCech_comp_zero I z hz t)

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverAllowedEmpty
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)


def globalCoefficientEquiv (m : Fin n → ℤ) : ringSections R n m ∅ ≃ₗ[R] (GlobalIndex n m →₀ R) :=
  ((coeffLinearEquiv R : Ambient R n ≃ₗ[R] LaurentModule R n).ofSubmodule' (sections R n m ∅)).trans
    (Finsupp.supportedEquivFinsupp {e | allowed n m ∅ e})

def globalBasis (m : Fin n → ℤ) : Module.Basis (GlobalIndex n m) R (ringSections R n m ∅) :=
  Finsupp.basisSingleOne.map (globalCoefficientEquiv R n m).symm
instance globalSections_finite (m : Fin n → ℤ) : Module.Finite R (ringSections R n m ∅) :=
  Module.Finite.of_basis (globalBasis R n m)
instance globalSections_free (m : Fin n → ℤ) : Module.Free R (ringSections R n m ∅) :=
  Module.Free.of_basis (globalBasis R n m)
lemma globalSections_isZero (m : Fin n → ℤ) (i : Fin n) (hi : m i<0) :
    CategoryTheory.Limits.IsZero (ModuleCat.of R (ringSections R n m ∅)) := by
  have : IsEmpty (GlobalIndex n m) := ⟨fun e => by
    have he := (allowed_empty n m e.val).mp e.property i
    omega⟩
  have : Subsingleton (ringSections R n m ∅) := (globalCoefficientEquiv R n m).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
abbrev unaugmentedSource (m : Fin n → ℤ) :=
  AlternatingCech.unaugmentedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
 

def highTwistH0 (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) :
    (unaugmentedSource R n m).homology 1 ≅ ModuleCat.of R (ringSections R n m ∅) :=
  AlternatingCech.unaugmented_homology_one R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
    (ring_sorted_acyclic R n m hm 1)
 

lemma highTwistHigher (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) (q : ℕ) :
    IsZero ((unaugmentedSource R n m).homology (q+2)) := by
  apply (exactAt_iff_isZero_homology _ _).mp
  exact AlternatingCech.unaugmented_exactAt R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
    q (ring_sorted_acyclic R n m hm (q+2))

def highTwistH0Basis (m : Fin n → ℤ) (hm : ∀ i,-1 ≤ m i) :
    Module.Basis (GlobalIndex n m) R ((unaugmentedSource R n m).homology 1) :=
  (globalBasis R n m).map (highTwistH0 R n m hm).toLinearEquiv.symm
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
attribute [local instance] OAI.Lech.ProductSourceCover.endpointRingDecEq
lemma ringEndpointProjector_carrier (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (x : Ambient R n)
    (hx : x∈ringSections R n m (s∪s.image (endpointVertex n j b))) :
    ringEndpointProjector R n j b x∈ringSections R n m s := by
  change (ringEndpointProjector R n j b x).coeff∈sections R n m s
  rw [ringEndpointProjector_coeff]
  exact endpointProjector_carrier R n m j hj s b x.coeff hx
lemma ringEndpointProjector_zero (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (x : Ambient R n)
    (hx : x∈ringSections R n m (s.image (endpointVertex n j b))) :
    ringEndpointProjector R n j b x=0 := by
  apply (coeffLinearEquiv R).injective
  change (ringEndpointProjector R n j b x).coeff = _
  rw [ringEndpointProjector_coeff,map_zero]
  exact endpointProjector_zero R n m j hj s b x.coeff hx
theorem ring_endpoint_acyclic (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) :
    (AlternatingCech.complex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)).Acyclic := by
  have hdec : endpointRingDecEq n = Classical.decEq (Chart n) := Subsingleton.elim _ _
  have hcarrier := ringEndpointProjector_carrier R n m j hj
  have hzero := ringEndpointProjector_zero R n m j hj
  rw [hdec] at hcarrier hzero ⊢
  exact AlternatingCech.projection_prism_acyclic R (Ambient R n) (ringSections R n m)
    (ringSections_mono R n m) (ringEndpointProjector R n j) (ringEndpointProjector_sum R n j)
    (endpointVertex n j) (endpointVertex_idem n j) hcarrier hzero
theorem ring_endpoint_sorted_acyclic (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) :
    (AlternatingCech.sortedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)).Acyclic := by
  intro q
  apply (ring_endpoint_acyclic R n m j hj q).of_iso
  convert AlternatingCech.cochainsSortedIso R (Ambient R n) (ringSections R n m) (ringSections_mono R n m) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
 

theorem endpointCohomology_isZero (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) (q : ℕ) :
    IsZero ((unaugmentedSource R n m).homology (q+1)) := by
  cases q with
  | zero =>
    exact (globalSections_isZero R n m j (by omega)).of_iso
      (AlternatingCech.unaugmented_homology_one R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
        (ring_endpoint_sorted_acyclic R n m j hj 1))
  | succ q =>
    apply (exactAt_iff_isZero_homology _ _).mp
    exact AlternatingCech.unaugmented_exactAt R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)
      q (ring_endpoint_sorted_acyclic R n m j hj (q+2))
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra AlternatingCech CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
local instance ordinaryDecEq_r1330bd_1 : DecidableEq (Chart n) := LinearOrder.toDecidableEq
omit [LinearOrder (Chart n)] in
lemma ringSections_coeff_map (m : Fin n → ℤ) (s : Finset (Chart n)) :
    (ringSections R n m s).map (coeffLinearEquiv R).toLinearMap=sections R n m s := by
  exact Submodule.map_comap_eq_of_surjective (coeffLinearEquiv R).surjective _
 

def ordinaryRingIso (m : Fin n → ℤ) : ordinaryComplex R n m ≅ unaugmentedSource R n m :=
  by
    letI ordinaryRingIsoDecEq : DecidableEq (Chart n) := Classical.decEq _
    have hh : ordinaryComplex R n m = complex R (LaurentModule R n)
        (ordinarySections R n m) (ordinarySections_mono R n m) := by
      unfold ordinaryComplex
      congr 1
    have hs : sortedComplex R (LaurentModule R n) (ordinarySections R n m) (ordinarySections_mono R n m) =
        unaugmentedComplex R (LaurentModule R n) (sections R n m) (sections_mono R n m) := by
      unfold unaugmentedComplex
      congr 1
      unfold ordinarySections
      congr 1
      exact Subsingleton.elim _ _
    exact eqToIso hh ≪≫
      cochainsSortedIso R (LaurentModule R n) (ordinarySections R n m) (ordinarySections_mono R n m) ≪≫ eqToIso hs ≪≫
      (sortedUnaugmentedFamilyIso R (Ambient R n) (LaurentModule R n) (ringSections R n m) (sections R n m)
        (coeffLinearEquiv R).toLinearMap (coeffLinearEquiv R).injective (ringSections_coeff_map R n m)
        (ringSections_mono R n m) (sections_mono R n m)).symm
def ordinaryCohomologyIso (m : Fin n → ℤ) (p : ℕ) :
    (ordinaryComplex R n m).homology p ≅ (unaugmentedSource R n m).homology p :=
  (homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) p).mapIso (ordinaryRingIso R n m)


theorem ordinary_endpoint_acyclic (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1) :
    (ordinaryComplex R n m).Acyclic := by
  intro p
  apply (exactAt_iff_isZero_homology _ _).mpr
  cases p with
  | zero => exact ordinary_homology_zero R n m
  | succ p => exact (endpointCohomology_isZero R n m j hj p).of_iso (ordinaryCohomologyIso R n m (p+1))
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverOrdinaryPositive
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)


attribute [local instance] OAI.Lech.ProductSourceCover.chartOrder
theorem ordinary_positive_pure (m : Fin n → ℤ) (d r : ℕ) (hd : 0<d)
    (hm : PureCohomology R (ordinaryComplex R n m) d r) (a : ℕ) :
    PureCohomology R (ordinaryComplex R (n+1) (Fin.cons (a:ℤ) m)) d ((a+1)*r) := by
  induction a with
  | zero =>
    have hz := pureCohomology_acyclic (ordinaryComplex R (n+1) (Fin.cons (-1) m))
      (ordinary_endpoint_acyclic R (n+1) (Fin.cons (-1) m) 0 rfl) d
    have h := pureCohomology_middle (ordinaryDivisorSequence R n 0 m)
      (ordinaryDivisorSequence_shortExact R n 0 m) hd hz hm
    simpa using h
  | succ a ih =>
    have hi : PureCohomology R (ordinaryComplex R (n+1) (Fin.cons ((a+1:ℕ):ℤ) m)) d (((a+1)*r)+r) := by
      apply pureCohomology_middle (ordinaryDivisorSequence R n ((a+1:ℕ):ℤ) m)
        (ordinaryDivisorSequence_shortExact R n ((a+1:ℕ):ℤ) m) hd _ hm
      simpa only [ordinaryDivisorSequence_X1,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using ih
    convert hi using 1 <;> first | rfl | ring
 

theorem ordinary_negative_pure (m : Fin n → ℤ) (d r : ℕ)
    (hm : PureCohomology R (ordinaryComplex R n m) d r) (a : ℕ) :
    PureCohomology R (ordinaryComplex R (n+1) (Fin.cons (-(a:ℤ)-2) m)) (d+1) ((a+1)*r) := by
  induction a with
  | zero =>
    have hz := pureCohomology_acyclic (ordinaryComplex R (n+1) (Fin.cons (-1) m))
      (ordinary_endpoint_acyclic R (n+1) (Fin.cons (-1) m) 0 rfl) (d+1)
    have h := pureCohomology_left (ordinaryDivisorSequence R n (-1) m)
      (ordinaryDivisorSequence_shortExact R n (-1) m)
      (ordinary_homology_zero R (n+1) (Fin.cons (-1-1) m)) hz hm
    simpa using h
  | succ a ih =>
    have hi := pureCohomology_left (ordinaryDivisorSequence R n (-(a:ℤ)-2) m)
      (ordinaryDivisorSequence_shortExact R n (-(a:ℤ)-2) m)
      (ordinary_homology_zero R (n+1) (Fin.cons (-(a:ℤ)-2-1) m)) ih hm
    rw [ordinaryDivisorSequence_X1] at hi
    convert hi using 1
    · congr 2
      push_cast
      ring
    · ring
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] OAI.Lech.ProductSourceCover.zeroDimChartOrder
lemma ordinary_zero_dim_pure (m : Fin 0 → ℤ) :
    PureCohomology R (ordinaryComplex R 0 m) 1 1 := by
  have hm : ∀ i,-1 ≤ m i := fun i => Fin.elim0 i
  refine ⟨?_,?_⟩
  · intro p hp
    cases p with
    | zero => exact ordinary_homology_zero R 0 m
    | succ p =>
      cases p with
      | zero => exact (hp rfl).elim
      | succ p => exact (highTwistHigher R 0 m hm p).of_iso (ordinaryCohomologyIso R 0 m (p+2))
  · let b := (highTwistH0Basis R 0 m hm).map (ordinaryCohomologyIso R 0 m 1).toLinearEquiv.symm
    exact ⟨b.reindex (Fintype.equivFinOfCardEq (by rw [globalIndex_card];simp))⟩
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R]


attribute [local instance] OAI.Lech.ProductSourceCover.signedChartOrder
theorem ordinary_signed_pure (n : ℕ) (m : Fin n → ℤ) :
    PureCohomology R (ordinaryComplex R n m) (negativeCount m+1) (signedRank m) := by
  induction n with
  | zero => simpa [negativeCount,signedRank] using ordinary_zero_dim_pure R m
  | succ n ih =>
    have hh := ih (Fin.tail m)
    rw [←Fin.cons_self_tail m]
    by_cases hz : m 0=-1
    · have he := ordinary_endpoint_acyclic R (n+1) (Fin.cons (m 0) (Fin.tail m)) 0 hz
      have hp := pureCohomology_acyclic _ he (negativeCount (Fin.cons (m 0) (Fin.tail m))+1)
      simpa [signedRank_cons,hz] using hp
    · by_cases hk : 0 ≤ m 0
      · obtain ⟨a,ha⟩ := Int.eq_ofNat_of_zero_le hk
        have hp := ordinary_positive_pure R n (Fin.tail m) (negativeCount (Fin.tail m)+1)
          (signedRank (Fin.tail m)) (by omega) hh a
        rw [ha]
        have hlt : ¬ (a:ℤ) < -1 := by omega
        have habs : ((a:ℤ)+1).natAbs=a+1 := by
          rw [show (a:ℤ)+1=((a+1:ℕ):ℤ) by omega,Int.natAbs_natCast]
        simpa only [negativeCount_cons,ite_eq_right hlt,zero_add,signedRank_cons,habs] using hp
      · have hk' : m 0≤-2 := by omega
        obtain ⟨a,ha⟩ := Int.eq_ofNat_of_zero_le (show 0≤-m 0-2 by omega)
        have hhead : m 0= -(a:ℤ)-2 := by omega
        have hp := ordinary_negative_pure R n (Fin.tail m) (negativeCount (Fin.tail m)+1)
          (signedRank (Fin.tail m)) hh a
        rw [hhead]
        convert hp using 1
        · rw [negativeCount_cons]
          have : -(a:ℤ)-2 < -1 := by omega
          simp [this,Nat.add_comm]
        · rw [signedRank_cons]
          congr 1
          have he : -(a:ℤ)-2+1= -((a+1:ℕ):ℤ) := by push_cast;ring
          rw [he,Int.natAbs_neg,Int.natAbs_natCast]
end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverCechNat
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

section

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

theorem sourceSigned_pure (m : Fin n → ℤ) :
    PureCohomology R (sourceCech R n m) (negativeCount m+1) (signedRank m) :=
  pureCohomology_of_iso R (ordinaryComplex R n m) (sourceCech R n m)
    (ordinaryCohomologyIso R n m) _ _ (ordinary_signed_pure R n m)


end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators Classical
universe u
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootInvariantsWeightZero
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

attribute [local instance] OAI.Lech.RootInvariants.weightZeroSectionsAlgebra
lemma section_chart_generator (i : Fin n) :
    (sectionY f n hn t v hv d i:d.S)+algebraMap B d.S t*(sectionX f n hn t v hv d i:d.S)=1 := by
  change (1+algebraMap B d.S t*d.roots i)+algebraMap B d.S t*(-d.roots i)=1
  ring
end


open Polynomial
open scoped TensorProduct
universe u

end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
lemma toH_chartFunction (σ τ : Fin n → Bool) :
    toH R n k t v hv d τ (algebraMap (D R n k t v hv d) (L R n k t v hv d τ) (q R n k t v hv d σ))=
      (↑((ProductLinearChart.denominator R n τ k)⁻¹):H R n k τ)*∏ i,
        (if σ i then algebraMap (ProductLinearChart.Ring R n) (H R n k τ) (ProductLinearChart.a R n τ i)
          else algebraMap (ProductLinearChart.Ring R n) (H R n k τ) (ProductLinearChart.b R n τ i)) := by
  rw [toH,UniversalFactorMap.chartMap_from,UniversalFactorMap.map_chartFunction]
end Lech.RootChartAtlas


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootPermutation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProductSourceCover
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Equiv.Perm (Fin n))

lemma permute_ringSections (m : Fin n → ℤ) (x : Ambient R n) (hx : x∈ringSections R n m ∅) :
    ProductLaurent.permute R n σ x∈ringSections R n (permuteWeight n σ m) ∅ := by
  rw [ringSections_mem] at hx ⊢
  intro e he
  rw [ProductLaurent.permute,domCongr_support] at he
  obtain ⟨a,ha,hae⟩ := Finset.mem_map.mp he
  rw [←hae]
  have hh := (allowed_empty n m a).mp (hx a ha)
  apply (allowed_empty n _ _).mpr
  intro i
  change 0 ≤ a (σ.symm i) ∧ a (σ.symm i) ≤ m (σ.symm i)
  exact hh (σ.symm i)

end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

attribute [local instance] OAI.Lech.RootInvariants.rootUlrichModuleAlgebra
local instance rootUlrichModuleIsScalarTower_r1330bd_1 : IsScalarTower A B d.S :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma homogeneous_product_member (m e : Fin n → ℕ) (he : ∀ i,e i ≤ m i) :
    (∏ i,(-d.roots i)^(e i)*(1+algebraMap B d.S t*d.roots i)^(m i-e i)) ∈
      module f n hn t v hv d (fun i => (m i:ℤ)) := by
  classical
  change (RootCoaction.weight f n hn t v hv d (fun i => (m i:ℤ)) : RootCoaction.T f n t v d)*
    RootCoaction.hom f n hn t v hv d _=RootCoaction.right f n t v d _
  simp only [RootCoaction.weight_eq,Units.coe_prod,zpow_natCast,Units.val_pow_eq_pow_val,map_prod]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hx := (sectionX f n hn t v hv d i).property
  have hy := (sectionY f n hn t v hv d i).property
  change (RootCoaction.weight f n hn t v hv d (Pi.single i 1) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (-d.roots i)=RootCoaction.right f n t v d (-d.roots i) at hx
  change (RootCoaction.weight f n hn t v hv d (Pi.single i 1) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (1+algebraMap B d.S t*d.roots i)=
        RootCoaction.right f n t v d (1+algebraMap B d.S t*d.roots i) at hy
  rw [weight_single] at hx hy
  simp only [map_mul,map_pow]
  rw [←hx,←hy,mul_pow,mul_pow]
  conv_lhs => lhs; rw [←Nat.add_sub_of_le (he i),pow_add]
  ring

def homogeneousSection (m e : Fin n → ℕ) (he : ∀ i,e i ≤ m i) :
    module f n hn t v hv d (fun i => (m i:ℤ)) :=
  ⟨∏ i,(-d.roots i)^(e i)*(1+algebraMap B d.S t*d.roots i)^(m i-e i),
    homogeneous_product_member f n hn t v hv d m e he⟩

def consecutiveSection (e : PowerIndex n) :
    module f n hn t v hv d (fun i => (powerWeight n i:ℤ)) :=
  ⟨binaryPower t n d.roots e,by
    rw [binaryPower_prod]
    exact homogeneous_product_member f n hn t v hv d _ _ (powerExponent_bound n e)⟩



theorem exists_consecutive_basis [Module.FaithfullyFlat A B] :
    ∃ b : Module.Basis (PowerIndex n) A
      (module f n hn t v hv d (fun i => (powerWeight n i:ℤ))),
      ∀ e,b e=consecutiveSection f n hn t v hv d e := by
  have ht := BinaryChange.normalized_top (f.map (algebraMap A B)) t v
    (le_trans (Polynomial.natDegree_map_le) hn) hv
  have hd : (BinaryChange.normalized (f.map (algebraMap A B)) n t v).natDegree≤n := by
    exact le_trans (Polynomial.natDegree_C_mul_le _ _)
      (BinaryChange.transform_degree _ _ _)
  obtain ⟨bb,hbb⟩ := d.exists_binary_basis hd ht t
  apply ModuleDescent.exists_basis_of_baseChange (consecutiveSection f n hn t v hv d)
    (tensorEquiv f n hn t v hv d _) bb
  intro e
  rw [tensorEquiv_one_tmul,hbb]
  rfl
end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarChartComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p15
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p12
lemma scalarChartEquiv_natural {s t : Finset (Fin (n+1))} (hst : s⊆t) (x : Ring I z hz s) :
    scalarChartEquiv I z hz t (restriction I z hz hst x)=
      ((FilteredCech.diagram I z hz 0).res hst).hom (scalarChartEquiv I z hz s x) := by
  have he : (∏ j∈s,z j)*(∏ j∈t\s,z j)=(∏ j∈t,z j) :=
    GradedChart.denominator_mul_sdiff z hst
  have hd : s.card+(t\s).card=t.card := by
    rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hst]
  have hr := Homogeneous.awayCongr_restrict (reesGrade I)
    (denominator_eq I z hz s) (denominator_eq I z hz (t\s)) (denominator_eq I z hz t)
    (denominator_mem I z hz (t\s)) (FilteredFraction.reesDenominator_mem I (product_mem I z hz (t\s)))
    (denominator_subsets I z hz hst)
    (FilteredFraction.reesDenominator_mul I (product_mem I z hz s) (product_mem I z hz t)
      (product_mem I z hz (t\s)) he hd).symm x
  change FilteredFraction.chartEquiv I (product_mem I z hz t)
    (chartRename I z hz t (restriction I z hz hst x))=_
  rw [show chartRename I z hz t (restriction I z hz hst x)=_ from hr,
    FilteredFraction.chartEquiv_restrict I (product_mem I z hz s) (product_mem I z hz t)
      (product_mem I z hz (t\s)) he hd]
  rfl

 

def scalarSectionEquiv (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    ScalarCechSection I z hz s ≃ₗ[R] FilteredCech.term I z 0 s where
  toFun x := scalarChartEquiv I z hz s (x ⟨hs⟩)
  invFun x _ := (scalarChartEquiv I z hz s).symm x
  left_inv x := by funext ht; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := LinearEquiv.apply_symm_apply _ _
  map_add' _ _ := map_add _ _ _
  map_smul' r x := by
    change scalarChartEquiv I z hz s (r • x ⟨hs⟩)=r • scalarChartEquiv I z hz s (x ⟨hs⟩)
    exact map_smul _ _ _

lemma scalarSectionEquiv_natural {s t : Finset (Fin (n+1))} (hst : s⊆t)
    (hs : s.Nonempty) (ht : t.Nonempty) (x : ScalarCechSection I z hz s) :
    scalarSectionEquiv I z hz t ht ((scalarCechRes I z hz hst).hom x)=
      ((FilteredCech.diagram I z hz 0).res hst).hom (scalarSectionEquiv I z hz s hs x) := by
  change scalarChartEquiv I z hz t ((scalarCechRes I z hz hst).hom x ⟨ht⟩)=_
  rw [scalarCechRes_apply I z hz hst hs ht]
  exact scalarChartEquiv_natural I z hz hst (x ⟨hs⟩)
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarCechComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
def scalarCechIso : FiniteModuleCech.positiveComplex (scalarCechDiagram I z hz) ≅
    FiniteModuleCech.positiveComplex (FilteredCech.diagram I z hz 0) :=
  FiniteModuleCech.positiveIsoOfNonempty (scalarSectionEquiv I z hz)
    (fun hst hs ht x => scalarSectionEquiv_natural I z hz hst hs ht x)
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionChartKernel
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ} (z : Fin h → R)
  (hz : Ideal.span (Set.range z)=I) (ell : TorsionLength I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

local instance torsionGradedKernelAdd (n : ℕ) : AddCommGroup (gradedMapR I z hz n).ker :=
  Submodule.addCommGroup (R:=R) (M:=sourceGrade I h n) (gradedMapR I z hz n).ker
local instance torsionGradedKernelModule (n : ℕ) : Module R (gradedMapR I z hz n).ker :=
  Submodule.module (R:=R) (M:=sourceGrade I h n) (gradedMapR I z hz n).ker
local instance degreeKernelAdd (n : ℕ) : AddCommGroup ((degreeMap I z hz n).restrictScalars R).ker :=
  Submodule.addCommGroup (R:=R) (M:=homogeneousSubmodule (Fin h) (R ⧸ I) n)
    ((degreeMap I z hz n).restrictScalars R).ker
local instance degreeKernelModule (n : ℕ) : Module R ((degreeMap I z hz n).restrictScalars R).ker :=
  Submodule.module (R:=R) (M:=homogeneousSubmodule (Fin h) (R ⧸ I) n)
    ((degreeMap I z hz n).restrictScalars R).ker

end Lech.SourceGraded

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarCechEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex FiniteModuleCech MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)

 
def scalarCechHomotopy : HomotopyEquiv (FilteredCech.shiftedPositive I z hz 0)
    (positiveZ (scalarCechDiagram I z hz)) :=
  (HomotopyEquiv.ofIso (FilteredCech.shiftOrdinaryIso I z hz 0)).trans
    ((CechNormalization.extendEquivalence (CechNormalization.homotopyEquiv
      (FilteredCech.diagram I z hz 0))).trans
      (HomotopyEquiv.ofIso ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
        (scalarCechIso I z hz).symm)))

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)
 
def scalarHomologyIso (i : ℤ) :
    (tensorCech F (scalarCechDiagram I z hz)).homology i ≅
      (((TensorTotal.Right.functor F).obj (FilteredCech.positive I z hz 0)).homology (i+1)) :=
  ((CechNormalization.tensorEquivalence F (scalarCechHomotopy I z hz)).toHomologyIso i).symm ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
      (CochainComplex.mapBifunctorShift₂Iso F (FilteredCech.positive I z hz 0)
        (curriedTensor (ModuleCat.{u} R)) 1) ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R) 1 i (i+1) (by omega)).app _

end Lech.ReesRoot

end

end OAI
end


