-- Prove2me | Definitions.Def_OAIQ032L020
-- name    : OAIQ032L020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:09:25.612827+00:00
-- url     : https://prove2.me/theorems/c316af4c-bb8a-4128-8176-3f1fc852332a
-- title:
--   Definitions bundle OAIQ032L020 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 97 declarations of OpenAI's Lean: 39 definitions, 2 instances and 56 theorems. The definitions and types are `OAI.Lech.FactorDescent.descended`, `OAI.Lech.FactorDescent.extend`, `OAI.Lech.FilteredFraction.chartEquiv`, `OAI.Lech.FilteredFraction.chartFraction`, `OAI.Lech.FilteredFraction.chartReduction`, `OAI.Lech.FilteredFraction.chartReductionAlg`, `OAI.Lech.FilteredFraction.exceptionalChartAlgebra`, `OAI.Lech.FilteredFraction.exceptionalChartEquiv`, `OAI.Lech.FilteredFraction.exceptionalRestrict`, `OAI.Lech.FilteredFraction.layerMap`, `OAI.Lech.FilteredFraction.reesChartAlgebra`, `OAI.Lech.FilteredFraction.reesRestrict`, `OAI.Lech.Homogeneous.zeroPieceEquiv`, `OAI.Lech.IdealFiltered.functor`, `OAI.Lech.IdealFiltered.quotientComplex`, `OAI.Lech.IdealFiltered.quotientMap`, `OAI.Lech.IdealFiltered.rowFunctor`, `OAI.Lech.IdealGraded.toRingR`, `OAI.Lech.ProductSourceCover.Ambient`, `OAI.Lech.RootCoaction.U`, `OAI.Lech.RootCoaction.counit`, `OAI.Lech.RootCoaction.delta`, `OAI.Lech.RootCoaction.denominator`, `OAI.Lech.RootCoaction.instAlgebraS_1`, `OAI.Lech.RootCoaction.instAlgebraS_2`, `OAI.Lech.RootCoaction.instAlgebraS_3`, `OAI.Lech.RootCoaction.liftLinear`, `OAI.Lech.RootCoaction.linear`, `OAI.Lech.RootCoaction.psi`, `OAI.Lech.RootCoaction.right₂`, `OAI.Lech.RootCoaction.weight`, `OAI.Lech.RootInvariants.algebraModuleEquiv`, `OAI.Lech.RootInvariants.algebraTensorEquiv`, `OAI.Lech.RootInvariants.instAlgebraS`, `OAI.Lech.RootInvariants.module`, `OAI.Lech.RootInvariants.tensorEquiv`, `OAI.Lech.RootTransport.denominator`, `OAI.Lech.RootTransport.linear`, `OAI.Lech.RootTransport.weight`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_AlternatingCechUnaugmentedComplex`, `Multiplicity_CechReduction`, `Multiplicity_FilteredFractionReesDenominator`, `Multiplicity_FilteredFractionReesDenominatorTheory`, `Multiplicity_FiniteModuleCech`, `Multiplicity_HomogeneousZeroPiece`, `Multiplicity_IdealFilteredComplex`, `Multiplicity_IdealFilteredQuotient`, `Multiplicity_IdealFilteredRows`, `Multiplicity_IdealGradedRing`, `Multiplicity_LechPiIso`, `Multiplicity_NativeDescentCanonicalAlg`, `Multiplicity_ProductSourceCoverRootSigned`, `Multiplicity_ReesExceptionalRing`, `Multiplicity_ReesRegular`, `Multiplicity_ReesRootBundle`, `Multiplicity_RootBundleChartsDenominator`, `Multiplicity_RootCoactionT`, `Multiplicity_RootInvariantsWeightZero`, `Multiplicity_ScalarChartComparison`, `Multiplicity_StandardFactorChartsL`.
--
--   **Imports.** It imports the bundles `OAIQ032L011`, `OAIQ032L012`, `OAIQ032L013` and `OAIQ032L014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L024`, `OAIQ032L025`, `OAIQ032L026` and `OAIQ032L027`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L011
import Definitions.Def_OAIQ032L012
import Definitions.Def_OAIQ032L013
import Definitions.Def_OAIQ032L014

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.IdealGraded.reesGradedAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.SourceGraded.target_graded _root_.OAI.Lech.extendScalars_additive
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

def toRingR (i : ℕ) : Piece I i →ₗ[R] Ring I :=
  (nextPower I i).liftQ ((quotientR I).comp (monomial I i)) (by
    intro x hx
    change Ideal.Quotient.mk (shifted I) (monomial I i x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((monomial_mem_shifted_iff I i x).mpr hx))

lemma toRingR_injective (i : ℕ) : Function.Injective (toRingR I i) := by
  rw [← LinearMap.ker_eq_bot, toRingR, Submodule.ker_liftQ_eq_bot]
  intro x hx
  change (x : R) ∈ I ^ (i + 1)
  apply (monomial_mem_shifted_iff I i x).mp
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

lemma toRingR_mem (i : ℕ) (x : Piece I i) : toRingR I i x ∈ grade I i := by
  obtain ⟨x, rfl⟩ := (nextPower I i).mkQ_surjective x
  exact ⟨monomial I i x, ⟨x, rfl⟩, rfl⟩

end Lech.IdealGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechPiIso
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.TwistedLocalization


open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]


variable (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f q c : A} {d e k : ℕ} (hf : f ∈ G d) (hc : c ∈ G k)
  (hfc : f*c=q) (hdeg : d+k=e)

variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

omit [GradedAlgebra G] [GradedAlgebra H] in
lemma ambientMap_naturality {f q : A} (hfq : f ∣ q) :
    (ambientMap G H g hg (f := q)).comp (ambientTo (R := R) hfq) =
      (ambientTo (R := R) (map_dvd g hfq)).comp (ambientMap G H g hg (f := f)) := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  ext a
  change ambientMap G H g hg (ambientTo hfq (algebraMap A _ a)) =
    ambientTo (map_dvd g hfq) (ambientMap G H g hg (algebraMap A _ a))
  simp only [ambientTo_algebraMap,ambientMap_algebraMap]

end Lech.TwistedLocalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominator
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.FilteredFraction


open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)


attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap quotientGraded
attribute [local instance] TwistedLocalization.kernelAdd TwistedLocalization.kernelModule

lemma quotientTwist_kernel_fraction (t : ℕ)
    (x : TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t)
    (hx : quotientTwist I hw t x=0) :
    ∃ (n : ℕ) (a : reesGrade I (n*d+t)), quotientGraded I (a:reesAlgebra I)=0 ∧
      TwistedLocalization.pieceFraction (reesGrade I) (f := reesDenominator I hw) t n a=x := by
  unfold quotientTwist at hx
  exact TwistedLocalization.kernel_fraction_eq (R := R) (A := reesAlgebra I) (B := IdealGraded.Ring I)
    (f := reesDenominator I hw) (d := d) (reesGrade I) (reesDenominator_mem I hw)
    (SourceGraded.targetGrade I) (quotientGraded I) (quotientGraded_smul I) t x hx

 
def layerMap (t : ℕ) :=
  (quotientTwist I hw t).comp (reesEquiv I hw t).symm.toLinearMap

lemma layerMap_kernel_le (t : ℕ) : (layerMap I hw t).ker ≤
    (piece I w d (t+1)).comap (piece I w d t).subtype := by
  intro x hx
  have hk : (reesEquiv I hw t).symm x ∈ (quotientTwist I hw t).ker := hx
  obtain ⟨n,a,hga,ha⟩ := quotientTwist_kernel_fraction I hw t ((reesEquiv I hw t).symm x) hk
  obtain ⟨b,hb⟩ := a.property
  have hae : a = ⟨monomial I _ b,⟨b,rfl⟩⟩ := Subtype.ext hb.symm
  have hbk : (b:R) ∈ I^(n*d+t+1) := by
    apply (monomial_mem_shifted_iff I (n*d+t) b).mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [hae] at hga
    simpa only [quotientGraded_apply] using hga
  have he : fraction I w d t n b=x.val := by
    have hh := congrArg (reesEquiv I hw t) ha
    rw [LinearEquiv.apply_symm_apply] at hh
    have hh' := congrArg Subtype.val hh
    change reesAmbient I hw (TwistedLocalization.fraction (reesGrade I) t n a)=x.val at hh'
    rw [hae,reesAmbient_fraction] at hh'
    exact hh'
  change x.val ∈ piece I w d (t+1)
  rw [←he]
  exact fraction_mem I w d (t+1) n ⟨b.val,by simpa only [Nat.add_assoc] using hbk⟩

lemma layerMap_kernel_ge (t : ℕ) :
    (piece I w d (t+1)).comap (piece I w d t).subtype ≤ (layerMap I hw t).ker := by
  intro x hx
  obtain ⟨n,b,hb⟩ := exists_fraction I w d hw (t+1) ⟨x.val,hx⟩
  let a : ↥(I^(n*d+t)) := ⟨b.val,Ideal.pow_le_pow_right (by omega) b.property⟩
  let y := TwistedLocalization.pieceFraction (reesGrade I)
    (f := reesDenominator I hw) t n ⟨monomial I _ a,⟨a,rfl⟩⟩
  have he : reesEquiv I hw t y=x := by
    apply Subtype.ext
    exact (reesAmbient_fraction I hw t n a).trans hb
  have hz : quotientGraded I (monomial I _ a)=0 := by
    unfold quotientGraded
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (monomial_mem_shifted_iff I (n*d+t) a).mpr
    simpa only [Nat.add_assoc] using b.property
  have hgz : TwistedLocalization.gradedMap (R := R) (A := reesAlgebra I) (B := IdealGraded.Ring I) (reesGrade I) (SourceGraded.targetGrade I)
      (quotientGraded I) (quotientGraded_smul I) (n*d+t) ⟨monomial I _ a,⟨a,rfl⟩⟩=0 :=
    by
      apply Subtype.ext
      simpa only [TwistedLocalization.gradedMap,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_zero] using hz
  change layerMap I hw t x=0
  rw [←he]
  change quotientTwist I hw t ((reesEquiv I hw t).symm (reesEquiv I hw t y))=0
  rw [LinearEquiv.symm_apply_apply]
  change TwistedLocalization.pieceMap _ _ _ _ _ t y=0
  rw [TwistedLocalization.pieceMap_fraction,hgz]
  exact (TwistedLocalization.pieceFraction (R := R) (A := IdealGraded.Ring I)
    (SourceGraded.targetGrade I) (f := quotientGraded I (reesDenominator I hw)) t n).map_zero

lemma layerMap_kernel (t : ℕ) : (layerMap I hw t).ker =
    (piece I w d (t+1)).comap (piece I w d t).subtype :=
  le_antisymm (layerMap_kernel_le I hw t) (layerMap_kernel_ge I hw t)


end Lech.FilteredFraction


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.FilteredFraction
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w ∈ I^d) (hv : v ∈ I^e) (hc : c ∈ I^k)
  (hwc : w*c=v) (hdeg : d+k=e)


def reesRestrict (t : ℕ) :=
  TwistedLocalization.pieceTo (R := R) (reesGrade I) (reesDenominator_mem I hw)
    (reesDenominator_mem I hc) (reesDenominator_mul I hw hv hc hwc hdeg) hdeg t

lemma reesEquiv_restrict (t : ℕ)
    (x : TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t) :
    reesEquiv I hv t (reesRestrict I hw hv hc hwc hdeg t x) =
      restrict I hw hc hwc hdeg t (reesEquiv I hw t x) := by
  apply Subtype.ext
  exact AlgHom.congr_fun (reesAmbient_naturality I hw hv hc hwc hdeg) x.val

attribute [local irreducible] TwistedLocalization.piece quotientGraded TwistedLocalization.ambientMap TwistedLocalization.ambientTo


def exceptionalRestrict (t : ℕ) :=
  TwistedLocalization.imagePieceTo (R := R) (A := reesAlgebra I) (B := IdealGraded.Ring I)
    (reesGrade I) (SourceGraded.targetGrade I) (quotientGraded I)
    (reesDenominator_mem I hw) (reesDenominator_mem I hc)
    (reesDenominator_mul I hw hv hc hwc hdeg) hdeg t

lemma quotientTwist_restrict (t : ℕ)
    (x : TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t) :
    quotientTwist I hv t (reesRestrict I hw hv hc hwc hdeg t x) =
      exceptionalRestrict I hw hv hc hwc hdeg t (quotientTwist I hw t x) := by
  apply Subtype.ext
  have hn := TwistedLocalization.ambientMap_naturality (R := R)
    (A := reesAlgebra I) (B := IdealGraded.Ring I)
    (reesGrade I) (SourceGraded.targetGrade I) (quotientGraded I) (quotientGraded_smul I)
    (f := reesDenominator I hw) (q := reesDenominator I hv)
    (show reesDenominator I hw ∣ reesDenominator I hv from
      ⟨reesDenominator I hc,(reesDenominator_mul I hw hv hc hwc hdeg).symm⟩)
  exact AlgHom.congr_fun hn x.val


lemma layerMap_naturality (t : ℕ) (x : piece I w d t) :
    layerMap I hv t (restrict I hw hc hwc hdeg t x) =
      exceptionalRestrict I hw hv hc hwc hdeg t (layerMap I hw t x) := by
  obtain ⟨y,rfl⟩ := (reesEquiv I hw t).surjective x
  rw [←reesEquiv_restrict I hw hv hc hwc hdeg]
  change quotientTwist I hv t ((reesEquiv I hv t).symm
    (reesEquiv I hv t (reesRestrict I hw hv hc hwc hdeg t y))) =
    exceptionalRestrict I hw hv hc hwc hdeg t
      (quotientTwist I hw t ((reesEquiv I hw t).symm (reesEquiv I hw t y)))
  rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
  exact quotientTwist_restrict I hw hv hc hwc hdeg t y
end Lech.FilteredFraction


open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechUnaugmentedComplex
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev Ambient := ProductLaurent.Ring R n


end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Set
open AlternatingCech
universe u
variable (R : Type u) [CommRing R] (ι : Type) [Fintype ι] [LinearOrder ι]



variable {R ι}
variable (D : Diagram R ι)

variable {D} {E : Diagram R ι}

namespace Map
variable (φ : Map D E)
omit [Fintype ι] in
lemma cochains_d (n : ℕ) (f : FiniteModuleCech.cochains D n) :
    cochains φ (n+1) (d D n f) = d E n (cochains φ n f) := by
  funext s
  change (φ.app s.val).hom (∑ i : Fin (n+1), (-1:ℤ)^i.val •
    (D.res (delete_subset s i)).hom (f (delete s i))) = _
  rw [map_sum]
  change (∑ i : Fin (n+1), (φ.app s.val).hom ((-1:ℤ)^i.val •
    (D.res (delete_subset s i)).hom (f (delete s i)))) =
    ∑ i : Fin (n+1), (-1:ℤ)^i.val •
      (E.res (delete_subset s i)).hom ((φ.app (delete s i).val).hom (f (delete s i)))
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  exact congrArg (fun ψ : D.obj (delete s i).val ⟶ E.obj s.val => ψ.hom (f (delete s i)))
    (φ.naturality (delete_subset s i))
end Map
end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverRootSigned
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]


instance scalarTower (U : Submonoid A) :
    IsScalarTower R (HomogeneousLocalization G U) (Localization U) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := HomogeneousLocalization G U)
    (A := Localization U) (by ext r; exact (val_algebraMap G U r).symm)

end Lech.Homogeneous


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootBundleChartsDenominator
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.RootTransport
open Polynomial Lech.RootGluing
universe u
variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable (f : B[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : f.eval t=(v:B)) (d : UniversalSplitting.Data B n (BinaryChange.normalized f n t v))
  (u : C) (w : Cˣ) (rs : Fin n → C)
  (hs : BinaryChange.normalized (f.map (algebraMap B C)) n u w=∏ i,(Polynomial.X-Polynomial.C (rs i)))

def denominator (i : Fin n) : Cˣ :=
  (denominator_unit f n hn t v hv u w rs hs i).unit

lemma denominator_val (i : Fin n) :
    (denominator f n hn t v hv u w rs hs i:C)=1+(u-algebraMap B C t)*rs i :=
  IsUnit.unit_spec _

def weight (ms : Fin n → ℤ) : Cˣ := ∏ i, denominator f n hn t v hv u w rs hs i ^ ms i

 
def linear (ms : Fin n → ℤ) : d.S →ₗ[B] C :=
  ((LinearEquiv.smulOfUnit (M := C) (weight f n hn t v hv u w rs hs ms)).restrictScalars B).toLinearMap.comp
    (hom f n hn t v hv d u w rs hs).toLinearMap

end Lech.RootTransport

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCoactionT
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.RootCoaction

section

section

section
open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootCoaction.instAlgebraS
def weight (ms : Fin n → ℤ) : (T f n t v d)ˣ :=
  RootTransport.weight (f.map (algebraMap A B)) n (natDegree_map_le.trans hn) t v hv
    (coord f n t v d) (unit f n t v d) (roots f n t v d) (factorization f n t v d) ms

def linear (ms : Fin n → ℤ) : d.S →ₗ[B] T f n t v d :=
  RootTransport.linear (f.map (algebraMap A B)) n (natDegree_map_le.trans hn) t v hv d
    (coord f n t v d) (unit f n t v d) (roots f n t v d) (factorization f n t v d) ms

attribute [local instance] OAI.Lech.RootCoaction.instIsScalarTowerS
lemma linear_apply (ms : Fin n → ℤ) (x : d.S) :
    linear f n hn t v hv d ms x=(weight f n hn t v hv d ms:T f n t v d)*hom f n hn t v hv d x := rfl

 
def counit : T f n t v d →ₐ[B] d.S :=
  Algebra.TensorProduct.lift (Algebra.ofId B d.S) (AlgHom.id A d.S) (fun _ _ => Commute.all _ _)

lemma counit_right (x : d.S) : counit f n t v d (right f n t v d x)=x := by
  simp [counit,right]

lemma counit_hom : (counit f n t v d).comp (hom f n hn t v hv d)=AlgHom.id B d.S := by
  apply d.hom_ext
  intro i
  rw [AlgHom.comp_apply,hom_root]
  change (counit f n t v d).toRingHom (rootShift _ _)=_
  rw [map_rootShift _ _ _ (denominator_unit f n hn t v hv d i)]
  change rootShift ((counit f n t v d) (coord f n t v d-algebraMap B (T f n t v d) t))
    ((counit f n t v d) (roots f n t v d i))=_
  simp only [map_sub,coord,roots,counit_right,AlgHom.commutes,sub_self,rootShift,zero_mul,
    add_zero,Ring.inverse_one,mul_one,AlgHom.id_apply]
end


open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance instAlgebraS_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance instIsScalarTowerS_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev U := B ⊗[A] T f n t v d

def right₂ : T f n t v d →ₐ[A] U f n t v d := Algebra.TensorProduct.includeRight

def delta : T f n t v d →ₐ[B] U f n t v d :=
  Algebra.TensorProduct.map (AlgHom.id B B) (right f n t v d)

def psi : T f n t v d →ₐ[B] U f n t v d :=
  Algebra.TensorProduct.map (AlgHom.id B B) ((hom f n hn t v hv d).restrictScalars A)

lemma delta_right (x : d.S) : delta f n t v d (right f n t v d x)=
    right₂ f n t v d (right f n t v d x) := by
  simp [delta,right,right₂]

lemma psi_right (x : d.S) : psi f n hn t v hv d (right f n t v d x)=
    right₂ f n t v d (hom f n hn t v hv d x) := by
  simp [psi,right,right₂]

lemma psi_coord : psi f n hn t v hv d (coord f n t v d)=
    right₂ f n t v d (algebraMap B (T f n t v d) t) := by
  rw [coord,psi_right,AlgHom.commutes]

lemma psi_roots (i : Fin n) : psi f n hn t v hv d (roots f n t v d i)=
    rootShift (right₂ f n t v d (coord f n t v d)-right₂ f n t v d (algebraMap B (T f n t v d) t))
      (right₂ f n t v d (roots f n t v d i)) := by
  rw [roots,psi_right,hom_root]
  change (right₂ f n t v d).toRingHom (rootShift _ _)=_
  rw [map_rootShift _ _ _ (denominator_unit f n hn t v hv d i)]
  rw [map_sub]
  rfl

lemma delta_hom : (delta f n t v d).comp (hom f n hn t v hv d)=
    (psi f n hn t v hv d).comp (hom f n hn t v hv d) := by
  apply d.hom_ext
  intro i
  simp only [AlgHom.comp_apply,hom_root]
  change (delta f n t v d).toRingHom (rootShift _ _) =
    (psi f n hn t v hv d).toRingHom (rootShift _ _)
  rw [map_rootShift _ _ _ (denominator_unit f n hn t v hv d i),
    map_rootShift _ _ _ (denominator_unit f n hn t v hv d i)]
  change rootShift ((delta f n t v d) (_-_)) ((delta f n t v d) (roots f n t v d i))=
    rootShift ((psi f n hn t v hv d) (_-_)) ((psi f n hn t v hv d) (roots f n t v d i))
  rw [map_sub,map_sub,AlgHom.commutes,AlgHom.commutes,psi_coord,psi_roots]
  have ha : IsUnit (1+(right₂ f n t v d (coord f n t v d)-
      right₂ f n t v d (algebraMap B (T f n t v d) t))*right₂ f n t v d (roots f n t v d i)) := by
    have h := (denominator_unit f n hn t v hv d i).map (right₂ f n t v d).toMonoidHom
    change IsUnit (right₂ f n t v d (1+_ * _)) at h
    simpa only [map_add,map_one,map_mul,map_sub] using h
  have hab : IsUnit (1+(right₂ f n t v d (coord f n t v d)-
      algebraMap B (U f n t v d) t)*right₂ f n t v d (roots f n t v d i)) := by
    have h := (denominator_unit f n hn t v hv d i).map (delta f n t v d).toMonoidHom
    change IsUnit (delta f n t v d (1+_ * _)) at h
    simpa only [map_add,map_one,map_mul,map_sub,coord,roots,delta_right,AlgHom.commutes] using h
  have he : right₂ f n t v d (coord f n t v d)-right₂ f n t v d (algebraMap B (T f n t v d) t) +
      (right₂ f n t v d (algebraMap B (T f n t v d) t)-algebraMap B (U f n t v d) t)=
      right₂ f n t v d (coord f n t v d)-algebraMap B (U f n t v d) t := by ring
  rw [rootShift_comp _ _ _ ha (by rw [he];exact hab),he]
  simp only [coord,roots,delta_right]

end


open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance instAlgebraS_2 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)

def denominator (i : Fin n) : (T f n t v d)ˣ :=
  RootTransport.denominator (f.map (algebraMap A B)) n (natDegree_map_le.trans hn) t v hv
    (coord f n t v d) (unit f n t v d) (roots f n t v d) (factorization f n t v d) i

local instance instIsScalarTowerS_2_r53f165_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma denominator_val (i : Fin n) : (denominator f n hn t v hv d i:T f n t v d)=
    1+(coord f n t v d-algebraMap B (T f n t v d) t)*roots f n t v d i :=
  RootTransport.denominator_val _ _ _ _ _ _ _ _ _ _ _

lemma weight_eq (ms : Fin n → ℤ) : weight f n hn t v hv d ms=∏ i,denominator f n hn t v hv d i ^ ms i := rfl

lemma counit_denominator (i : Fin n) :
    Units.map (counit f n t v d).toMonoidHom (denominator f n hn t v hv d i)=1 := by
  apply Units.ext
  change counit f n t v d (denominator f n hn t v hv d i:T f n t v d)=1
  rw [denominator_val,map_add,map_one,map_mul,map_sub,coord,roots,counit_right,counit_right,AlgHom.commutes]
  simp

lemma counit_weight (ms : Fin n → ℤ) :
    Units.map (counit f n t v d).toMonoidHom (weight f n hn t v hv d ms)=1 := by
  rw [weight_eq,map_prod]
  simp only [map_zpow,counit_denominator,one_zpow,Finset.prod_const_one]

lemma counit_linear (ms : Fin n → ℤ) :
    (counit f n t v d).toLinearMap.comp (linear f n hn t v hv d ms)=LinearMap.id := by
  ext x
  have h := congrArg (fun w : d.Sˣ => (w:d.S)) (counit_weight f n hn t v hv d ms)
  have hx := congrArg (fun φ : d.S →ₐ[B] d.S => φ x) (counit_hom f n hn t v hv d)
  change counit f n t v d (weight f n hn t v hv d ms:T f n t v d)=1 at h
  change counit f n t v d (hom f n hn t v hv d x)=x at hx
  change counit f n t v d (linear f n hn t v hv d ms x)=x
  rw [linear_apply,map_mul,h,hx,one_mul]

lemma psi_denominator (i : Fin n) :
    Units.map (psi f n hn t v hv d).toMonoidHom (denominator f n hn t v hv d i)=
      Units.map (delta f n t v d).toMonoidHom (denominator f n hn t v hv d i) *
      (Units.map (right₂ f n t v d).toMonoidHom (denominator f n hn t v hv d i))⁻¹ := by
  apply Units.ext
  let a := right₂ f n t v d (coord f n t v d)-right₂ f n t v d (algebraMap B (T f n t v d) t)
  let b := right₂ f n t v d (algebraMap B (T f n t v d) t)-algebraMap B (U f n t v d) t
  let r := right₂ f n t v d (roots f n t v d i)
  let e := Units.map (right₂ f n t v d).toMonoidHom (denominator f n hn t v hv d i)
  have he : (e:U f n t v d)=1+a*r := by
    change right₂ f n t v d (denominator f n hn t v hv d i:T f n t v d)=1+a*r
    rw [denominator_val,map_add,map_one,map_mul,map_sub]
  have heab : a+b=right₂ f n t v d (coord f n t v d)-algebraMap B (U f n t v d) t := by dsimp [a,b];ring
  change psi f n hn t v hv d (denominator f n hn t v hv d i:T f n t v d)=_
  rw [denominator_val,map_add,map_one,map_mul,map_sub,AlgHom.commutes,psi_coord,psi_roots]
  change 1+b*rootShift a r=delta f n t v d (denominator f n hn t v hv d i:T f n t v d)*(e⁻¹:Units (U f n t v d))
  rw [rootShift,← he,Ring.inverse_unit,denominator_comp a b r e he,heab]
  congr 1
  rw [denominator_val,map_add,map_one,map_mul,map_sub,AlgHom.commutes,coord,roots,delta_right,delta_right]
  rfl

lemma weight_coassoc (ms : Fin n → ℤ) :
    Units.map (right₂ f n t v d).toMonoidHom (weight f n hn t v hv d ms) *
      Units.map (psi f n hn t v hv d).toMonoidHom (weight f n hn t v hv d ms)=
    Units.map (delta f n t v d).toMonoidHom (weight f n hn t v hv d ms) := by
  simp only [weight_eq,map_prod,map_zpow,psi_denominator]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact unit_zpow_cancel _ _ _

end


open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance instAlgebraS_3 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance instIsScalarTowerS_3 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

def liftLinear (ms : Fin n → ℤ) : T f n t v d →ₗ[B] U f n t v d :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : B →ₗ[B] B)
    ((linear f n hn t v hv d ms).restrictScalars A)

lemma liftLinear_apply (ms : Fin n → ℤ) (z : T f n t v d) :
    liftLinear f n hn t v hv d ms z =
      right₂ f n t v d (weight f n hn t v hv d ms:T f n t v d)*psi f n hn t v hv d z := by
  induction z using OAI.tensorInductionOn with
  | tmul b x =>
    simp only [liftLinear,TensorProduct.AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,linear_apply,psi,Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply,AlgHom.restrictScalars_apply,right₂,Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  | add x y hx hy => rw [map_add,map_add,mul_add,hx,hy]

lemma linear_coassoc (ms : Fin n → ℤ) :
    (delta f n t v d).toLinearMap.comp (linear f n hn t v hv d ms)=
      (liftLinear f n hn t v hv d ms).comp (linear f n hn t v hv d ms) := by
  ext x
  have hw := congrArg (fun w : (U f n t v d)ˣ => (w:U f n t v d))
    (weight_coassoc f n hn t v hv d ms)
  change right₂ f n t v d (weight f n hn t v hv d ms:T f n t v d) *
    psi f n hn t v hv d (weight f n hn t v hv d ms:T f n t v d)=
    delta f n t v d (weight f n hn t v hv d ms:T f n t v d) at hw
  have hh := congrArg (fun φ : d.S →ₐ[B] U f n t v d => φ x) (delta_hom f n hn t v hv d)
  change delta f n t v d (hom f n hn t v hv d x)=psi f n hn t v hv d (hom f n hn t v hv d x) at hh
  change delta f n t v d (linear f n hn t v hv d ms x)=liftLinear f n hn t v hv d ms (linear f n hn t v hv d ms x)
  rw [liftLinear_apply,linear_apply,map_mul,map_mul,← mul_assoc,hw,hh]
end Lech.RootCoaction


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance instAlgebraS : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance instIsScalarTowerS : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl


def module (ms : Fin n → ℤ) : Submodule A d.S :=
  NativeDescent.invariants (RootCoaction.linear f n hn t v hv d ms)

lemma evaluation_eq : (NativeDescent.evaluation (A := A) (B := B) (M := d.S))=
    (RootCoaction.counit f n t v d).toLinearMap := by
  ext x
  change (1:B) • x=algebraMap B d.S 1*x
  rw [one_smul,map_one,one_mul]

lemma delta_eq : TensorProduct.AlgebraTensorModule.lTensor B B
    (NativeDescent.inclusion (A := A) (B := B) (M := d.S))=
      (RootCoaction.delta f n t v d).toLinearMap := by
  ext x
  rfl

 
def tensorEquiv [Module.Flat A B] (ms : Fin n → ℤ) :
    B ⊗[A] module f n hn t v hv d ms ≃ₗ[B] d.S :=
  NativeDescent.tensorEquiv (RootCoaction.linear f n hn t v hv d ms)
    (by rw [evaluation_eq];exact RootCoaction.counit_linear f n hn t v hv d ms)
    (by rw [delta_eq];exact RootCoaction.linear_coassoc f n hn t v hv d ms)

end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootInvariantsWeightZero
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

attribute [local instance] OAI.Lech.RootInvariants.weightZeroBaseAlgebra
lemma weight_zero : RootCoaction.weight f n hn t v hv d (0 : Fin n → ℤ)=1 := by
  rw [RootCoaction.weight_eq]
  simp

lemma linear_zero : RootCoaction.linear f n hn t v hv d (0 : Fin n → ℤ)=
    (RootCoaction.hom f n hn t v hv d).toLinearMap := by
  ext x
  rw [RootCoaction.linear_apply,weight_zero]
  simp


lemma algebra_toSubmodule : (algebra f n hn t v hv d).toSubmodule=
    module f n hn t v hv d (0 : Fin n → ℤ) := by
  ext x
  change (RootCoaction.hom f n hn t v hv d x=RootCoaction.right f n t v d x) ↔
    RootCoaction.linear f n hn t v hv d 0 x=(1:B) ⊗ₜ[A] x
  rw [linear_zero]
  rfl

def algebraModuleEquiv : algebra f n hn t v hv d ≃ₗ[A] module f n hn t v hv d (0 : Fin n → ℤ) :=
  LinearEquiv.ofEq _ _ (algebra_toSubmodule f n hn t v hv d)

attribute [local instance] OAI.Lech.RootInvariants.weightZeroBaseScalarTower
lemma algebraBaseMap_linear [Module.Flat A B] :
    (algebraBaseMap f n hn t v hv d).toLinearMap=
      (tensorEquiv f n hn t v hv d (0 : Fin n → ℤ)).toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
          (algebraModuleEquiv f n hn t v hv d)).toLinearMap := by
  ext x
  change algebraMap B d.S 1*(x:d.S)=(1:B) • (x:d.S)
  rw [map_one,one_mul,one_smul]


def algebraTensorEquiv [Module.Flat A B] :
    B ⊗[A] algebra f n hn t v hv d ≃ₐ[B] d.S :=
  AlgEquiv.ofBijective (algebraBaseMap f n hn t v hv d) (by
    change Function.Bijective (algebraBaseMap f n hn t v hv d).toLinearMap
    rw [algebraBaseMap_linear]
    exact (tensorEquiv f n hn t v hv d 0).bijective.comp
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
        (algebraModuleEquiv f n hn t v hv d)).bijective)
end


open Polynomial
open scoped TensorProduct
universe u

end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_StandardFactorChartsL
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.FactorNormalization

section
open Polynomial
universe u
variable {A : Type u} [CommRing A]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : A) (v w : Aˣ)
  (hv : f.eval t=(v:A)) (a b : Fin n → A)
  (hf : f.homogenize n=MvPolynomial.C (w:A)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

lemma normalized_factorization : BinaryChange.normalized f n t v=∏ i,(Polynomial.X-C (roots f n hn t v w hv a b hf i)) := by
  have ht : BinaryChange.transform f n t=C (w:A)*∏ i,
      (C (denominator f n hn t v w hv a b hf i:A)*(Polynomial.X-C (roots f n hn t v w hv a b hf i))) := by
    rw [BinaryChange.transform_eq_aeval,hf,map_mul,map_prod]
    simp only [MvPolynomial.aeval_C]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simpa using transform_factor f n hn t v w hv a b hf i
  have hu : (v⁻¹:Aˣ)*w*∏ i,denominator f n hn t v w hv a b hf i=1 := by
    rw [mul_assoc,unit_product,inv_mul_cancel]
  have hc := congrArg (fun u : Aˣ => (u:A)) hu
  simp only [Units.val_mul,Units.coe_prod,Units.val_one] at hc
  rw [BinaryChange.normalized,ht,Finset.prod_mul_distrib,← map_prod C,
    ← mul_assoc,← mul_assoc,← C_mul,← C_mul,hc,C_1,one_mul]

end


universe u

open Polynomial
end Lech.FactorNormalization


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NativeDescentCanonicalAlg
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.FactorDescent
open Polynomial
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.FactorDescent.instAlgebraS
variable (φ : d.S →ₐ[B] R (A := A) (B := B) (T := T))



def descended [Module.FaithfullyFlat A B]
    (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
    (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
    (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val) :
    RootInvariants.algebra f n hn t v hv d →ₐ[A] T :=
  (NativeDescent.canonicalAlgEquiv (A := A) B T).symm.toAlgHom.comp
    (invariantMap f n hn t v hv d φ a b μ hμ hφ)

lemma descended_include [Module.FaithfullyFlat A B]
    (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
    (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
    (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val)
    (x : RootInvariants.algebra f n hn t v hv d) :
    includeT (descended f n hn t v hv d φ a b μ hμ hφ x)=φ (x:d.S) := by
  have h := (NativeDescent.canonicalAlgEquiv (A := A) B T).apply_symm_apply
    (invariantMap f n hn t v hv d φ a b μ hμ hφ x)
  exact congrArg Subtype.val h
end Lech.FactorDescent


namespace Lech.FactorDescent
open Polynomial
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

lemma includeT_injective [Module.FaithfullyFlat A B] :
    Function.Injective (includeT (A := A) (B := B) (T := T)) := by
  intro x y h
  apply (NativeDescent.canonicalAlgUnit_bijective (A := A) B T).injective
  exact Subtype.ext h

 

local instance instAlgebraS_1_r53f165_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
def extend [Module.Flat A B] (g : RootInvariants.algebra f n hn t v hv d →ₐ[A] T) :
    d.S →ₐ[B] R (A := A) (B := B) (T := T) :=
  (Algebra.TensorProduct.map (AlgHom.id B B) g).comp
    (RootInvariants.algebraTensorEquiv f n hn t v hv d).symm.toAlgHom

lemma extend_subtype [Module.Flat A B] (g : RootInvariants.algebra f n hn t v hv d →ₐ[A] T)
    (x : RootInvariants.algebra f n hn t v hv d) :
    extend f n hn t v hv d g (x:d.S)=includeT (g x) := by
  have h : (RootInvariants.algebraTensorEquiv f n hn t v hv d).symm (x:d.S)=(1:B) ⊗ₜ[A] x := by
    apply (RootInvariants.algebraTensorEquiv f n hn t v hv d).injective
    rw [AlgEquiv.apply_symm_apply]
    change (x:d.S)=algebraMap B d.S 1*(x:d.S)
    rw [map_one,one_mul]
  simp only [extend,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,h,
    Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
  rfl

lemma extend_injective [Module.FaithfullyFlat A B] :
    Function.Injective (extend f n hn t v hv d (T := T)) := by
  intro g h H
  ext x
  apply includeT_injective (A := A) (B := B)
  have he := AlgHom.congr_fun H (x:d.S)
  simpa only [extend_subtype] using he

 
lemma point_ext [Module.FaithfullyFlat A B]
    (g h : RootInvariants.algebra f n hn t v hv d →ₐ[A] T)
    (H : ∀ i,extend f n hn t v hv d g (d.roots i)=extend f n hn t v hv d h (d.roots i)) : g=h :=
  extend_injective f n hn t v hv d (d.hom_ext _ _ H)

variable (φ : d.S →ₐ[B] R (A := A) (B := B) (T := T))
  (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
  (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
  (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val)

lemma extend_descended [Module.FaithfullyFlat A B] :
    extend f n hn t v hv d (descended f n hn t v hv d φ a b μ hμ hφ)=φ := by
  apply (AlgHom.cancel_right (RootInvariants.algebraTensorEquiv f n hn t v hv d).surjective).mp
  ext x
  have he : RootInvariants.algebraTensorEquiv f n hn t v hv d ((1:B) ⊗ₜ[A] x)=(x:d.S) := by
    change algebraMap B d.S 1*(x:d.S)=(x:d.S)
    rw [map_one,one_mul]
  change extend f n hn t v hv d (descended f n hn t v hv d φ a b μ hμ hφ)
    (RootInvariants.algebraTensorEquiv f n hn t v hv d ((1:B) ⊗ₜ[A] x))=
      φ (RootInvariants.algebraTensorEquiv f n hn t v hv d ((1:B) ⊗ₜ[A] x))
  rw [he,extend_subtype]
  exact descended_include f n hn t v hv d φ a b μ hμ hφ x

end Lech.FactorDescent


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootBundle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.HomogeneousEval
open HomogeneousLocalization
universe u v
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
lemma awayMap_algebraMap {f g x : A} {e : ℕ} (hg : g ∈ G e) (hx : x = f*g) (r : R) :
    awayMap G hg hx (algebraMap R (Away G f) r) = algebraMap R (Away G x) r := by
  apply HomogeneousLocalization.val_injective
  rw [val_awayMap,Homogeneous.val_algebraMap,Homogeneous.val_algebraMap]
  rw [IsScalarTower.algebraMap_apply R A (Localization.Away f),IsLocalization.Away.lift_eq,
    ←IsScalarTower.algebraMap_apply R A (Localization.Away x)]
end Lech.HomogeneousEval

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
variable (D : Diagram R ι) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)

variable (I : Ideal R)

lemma quotientPiEquiv_d (q : ℕ) (x : cochains D q) :
    TensorIdeal.quotientPiEquiv I (fun s : Set.powersetCard ι (q+1) => D.obj s.val)
      (Submodule.Quotient.mk (d D q x)) =
    d (reduction D I) q
      (TensorIdeal.quotientPiEquiv I (fun s : Set.powersetCard ι q => D.obj s.val)
        (Submodule.Quotient.mk x)) := by
  rw [TensorIdeal.quotientPiEquiv_mk,TensorIdeal.quotientPiEquiv_mk]
  funext s
  change (Submodule.mkQ (I • (⊤ : Submodule R (D.obj s.val))))
    (∑ j : Fin (q+1), (-1:ℤ)^j.val • (D.res (AlternatingCech.delete_subset s j)).hom
      (x (AlternatingCech.delete s j))) = _
  rw [map_sum]
  change (∑ j : Fin (q+1), (Submodule.mkQ (I • (⊤ : Submodule R (D.obj s.val))))
    ((-1:ℤ)^j.val • (D.res (AlternatingCech.delete_subset s j)).hom
      (x (AlternatingCech.delete s j)))) = _
  simp only [map_zsmul]
  rfl



end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_HomogeneousZeroPiece
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)
attribute [local instance] awayAddCommGroup

lemma toZeroPiece_surjective : Function.Surjective (toZeroPiece G hf) := by
  intro x
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction G hf 0 x
  refine ⟨Away.mk G hf n a (by simpa only [Nat.add_zero,nsmul_eq_mul,Nat.cast_id] using a.property),?_⟩
  apply Subtype.ext
  exact ha

def zeroPieceEquiv : Away G f ≃ₗ[R] TwistedLocalization.piece G (f:=f) (d:=d) 0 :=
  LinearEquiv.ofBijective (toZeroPiece G hf) ⟨toZeroPiece_injective G hf,toZeroPiece_surjective G hf⟩
end Lech.Homogeneous

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredComplex
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (Q : ModuleCat.{u} R)

lemma map_id (Q : ModuleCat.{u} R) : map I F h s hd (𝟙 Q) = 𝟙 (complex I F h s hd Q) := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (F.X p ◁ 𝟙 Q).hom x.val=x.val
  rw [whiskerLeft_id]
  rfl

lemma map_comp {Q Q' Q'' : ModuleCat.{u} R} (f : Q ⟶ Q') (g : Q' ⟶ Q'') :
    map I F h s hd (f ≫ g) = map I F h s hd f ≫ map I F h s hd g := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (F.X p ◁ (f ≫ g)).hom x.val=(F.X p ◁ g).hom ((F.X p ◁ f).hom x.val)
  rw [whiskerLeft_comp]
  rfl

 
def functor : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj := complex I F h s hd
  map := map I F h s hd
  map_id := map_id I F h s hd
  map_comp := map_comp I F h s hd

 
instance functor_additive : (functor I F h s hd).Additive where
  map_add := by
    intro Q Q' f g
    apply Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (F.X p ◁ (f+g)).hom x.val = (F.X p ◁ f).hom x.val+(F.X p ◁ g).hom x.val
    rw [show F.X p ◁ (f+g) = F.X p ◁ f + F.X p ◁ g from
      ((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).map_add]
    rfl

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredQuotient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))

abbrev quotientComplex (Q : ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  ModuleComplexQuotient.complex (tensorComplex F Q) (term I F h s Q) (term_d I F h s hd Q)

def quotientMap {Q Q' : ModuleCat.{u} R} (f : Q ⟶ Q') :
    quotientComplex I F h s hd Q ⟶ quotientComplex I F h s hd Q' :=
  ModuleComplexQuotient.map (tensorMap F f)
    (fun p => Submodule.smul_top_le_comap_smul_top (I^(order h s p)) ((tensorMap F f).f p).hom)

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredRows
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))

 
def rowFunctor (p : ℤ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  functor I F h s hd ⋙ HomologicalComplex.eval _ _ p

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRegular
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FilteredFraction
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)
attribute [local instance] Homogeneous.awayAddCommGroup

 
def chartFraction : Away (reesGrade I) (reesDenominator I hw) →ₗ[R] Localization.Away w :=
  (piece I w d 0).subtype.comp ((reesEquiv I hw 0).toLinearMap.comp
    (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).toLinearMap)
lemma chartFraction_injective : Function.Injective (chartFraction I hw) :=
  (piece I w d 0).injective_subtype.comp ((reesEquiv I hw 0).injective.comp
    (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).injective)

 

lemma chart_smul_injective (a : R) (ha : a ∣ w) :
    Function.Injective (fun x : Away (reesGrade I) (reesDenominator I hw) => a • x) := by
  have hu : IsUnit (algebraMap R (Localization.Away w) a) :=
    isUnit_of_dvd_unit (map_dvd _ ha) (IsLocalization.Away.algebraMap_isUnit w)
  intro x y hxy
  apply chartFraction_injective I hw
  have hh := congrArg (chartFraction I hw) hxy
  rw [map_smul,map_smul] at hh
  exact hu.mul_left_cancel (by simpa only [Algebra.smul_def] using hh)
end Lech.FilteredFraction

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesExceptionalRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.FilteredFraction
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)
attribute [local instance] Homogeneous.awayAddCommGroup
attribute [local irreducible] quotientGraded Homogeneous.awayMap TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap

attribute [local instance] OAI.Lech.FilteredFraction.reesChartCommRing
attribute [local instance] OAI.Lech.FilteredFraction.reesChartModule
def chartEquiv : ReesChart I hw ≃ₗ[R] piece I w d 0 :=
  (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).trans (reesEquiv I hw 0)

def exceptionalChartEquiv : ExceptionalChart I hw ≃ₗ[R] exceptionalPiece I hw 0 :=
  Homogeneous.zeroPieceEquiv (R:=R) (A:=IdealGraded.Ring I) (SourceGraded.targetGrade I)
    (quotientDenominator_mem I hw)

lemma exceptionalChartEquiv_symm_val (x : exceptionalPiece I hw 0) :
    ((exceptionalChartEquiv I hw).symm x).val=x.val :=
  congrArg Subtype.val ((exceptionalChartEquiv I hw).apply_symm_apply x)

 
def chartReduction : ReesChart I hw →ₗ[R] ExceptionalChart I hw :=
  (exceptionalChartEquiv I hw).symm.toLinearMap.comp
    ((quotientTwist I hw 0).comp
      (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).toLinearMap)

attribute [local irreducible] TwistedLocalization.ambientMap

lemma chartReduction_val (x : ReesChart I hw) :
    (chartReduction I hw x).val = chartAmbient I hw x.val := by
  change ((exceptionalChartEquiv I hw).symm
    (quotientTwist I hw 0 (Homogeneous.zeroPieceEquiv (reesGrade I)
      (reesDenominator_mem I hw) x))).val = _
  rw [exceptionalChartEquiv_symm_val]
  unfold quotientTwist TwistedLocalization.pieceMap chartAmbient
  rfl

lemma chartReduction_mk (j : ℕ) (a : reesAlgebra I) (ha : a ∈ reesGrade I (j • d)) :
    chartReduction I hw (Away.mk (reesGrade I) (reesDenominator_mem I hw) j a ha) =
      Away.mk (SourceGraded.targetGrade I) (quotientDenominator_mem I hw) j
        (quotientGraded I a) (Graded.map_mem (quotientGraded I) ha) := by
  apply HomogeneousLocalization.val_injective
  rw [chartReduction_val,Away.val_mk,Away.val_mk]
  let b : reesGrade I (j*d+0) := ⟨a,by simpa only [nsmul_eq_mul,Nat.cast_id,Nat.add_zero] using ha⟩
  change chartAmbient I hw (TwistedLocalization.fraction (reesGrade I) (f:=reesDenominator I hw) 0 j b)=_
  unfold chartAmbient
  rw [TwistedLocalization.ambientMap_fraction]
  unfold TwistedLocalization.gradedMap
  rfl

local instance reesChartAlgebra : Algebra R (ReesChart I hw) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (reesDenominator I hw))
local instance exceptionalChartAlgebra : Algebra R (ExceptionalChart I hw) :=
  Homogeneous.algebra (SourceGraded.targetGrade I)
    (Submonoid.powers (quotientGraded I (reesDenominator I hw)))

 
def chartReductionAlg : ReesChart I hw →ₐ[R] ExceptionalChart I hw where
  toFun := chartReduction I hw
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    apply HomogeneousLocalization.val_injective
    rw [chartReduction_val,HomogeneousLocalization.val_one,map_one,HomogeneousLocalization.val_one]
  map_mul' x y := by
    apply HomogeneousLocalization.val_injective
    rw [chartReduction_val,HomogeneousLocalization.val_mul,map_mul,
      HomogeneousLocalization.val_mul,chartReduction_val,chartReduction_val]
  commutes' r := by
    apply HomogeneousLocalization.val_injective
    rw [chartReduction_val,Homogeneous.val_algebraMap,
      AlgHom.commutes,Homogeneous.val_algebraMap]

end Lech.FilteredFraction

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarChartComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FilteredFraction
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w∈I^d) (hv : v∈I^e) (hc : c∈I^k)
  (he : w*c=v) (hd : d+k=e)
attribute [local instance] Homogeneous.awayAddCommGroup
lemma chartEquiv_restrict (x : ReesChart I hw) :
    chartEquiv I hv (HomogeneousLocalization.awayMap (reesGrade I)
      (reesDenominator_mem I hc) (reesDenominator_mul I hw hv hc he hd).symm x)=
    restrict I hw hc he hd 0 (chartEquiv I hw x) := by
  apply Subtype.ext
  change reesAmbient I hv ((HomogeneousLocalization.awayMap (reesGrade I)
    (reesDenominator_mem I hc) (reesDenominator_mul I hw hv hc he hd).symm x).val)=_
  rw [HomogeneousLocalization.val_awayMap]
  exact AlgHom.congr_fun (reesAmbient_naturality I hw hv hc he hd) x.val
end Lech.FilteredFraction

end

end OAI
end


