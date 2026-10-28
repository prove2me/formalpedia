-- Prove2me | Definitions.Def_OAIQ032L014
-- name    : OAIQ032L014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:51:13.044935+00:00
-- url     : https://prove2.me/theorems/10cb33c2-fcc7-49c0-8e5b-4843a1834d39
-- title:
--   Definitions bundle OAIQ032L014 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 29 definitions, 4 instances and 20 theorems. The definitions and types are `OAI.Lech.ImageCech.cochains`, `OAI.Lech.ImageCech.d`, `OAI.Lech.ImageCech.restrict`, `OAI.Lech.Koszul.coneSwapIso`, `OAI.Lech.Koszul.quotientAugmentationNat`, `OAI.Lech.Koszul.quotient_nullhomotopy`, `OAI.Lech.Koszul.quotient_scalar_zero`, `OAI.Lech.Koszul.restrictScalarsSingleTensorHomologyIso`, `OAI.Lech.Koszul.restrictScalarsTensorHomologyIso`, `OAI.Lech.Koszul.restrictScalarsTensorIso`, `OAI.Lech.Koszul.singleTensorHomologyZeroIso`, `OAI.Lech.Koszul.tensorConeIso`, `OAI.Lech.Koszul.tensorShiftIso`, `OAI.Lech.Koszul.tensorSingleHomologyIso`, `OAI.Lech.Koszul.tensorSplitting`, `OAI.Lech.Koszul.unit`, `OAI.Lech.Koszul.unitHomologyGenerator`, `OAI.Lech.Koszul.unitHomologyQuotient`, `OAI.Lech.ModuleComplexQuotient.inclusion`, `OAI.Lech.ModuleComplexQuotient.projection`, `OAI.Lech.ModuleComplexQuotient.shortComplex`, `OAI.Lech.MonomialSpanning.lift`, `OAI.Lech.PartialLaurent.denominator`, `OAI.Lech.PartialLaurent.polynomialEquiv`, `OAI.Lech.ProductLaurent.Ring`, `OAI.Lech.TensorIdeal.equiv`, `OAI.Lech.TensorIdeal.tensorReductionEquiv`, `OAI.Lech.TensorIdeal.tensorReductionIso`, `OAI.Lech.UnitSection.equiv`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_FrobeniusHomologyGrowth`, `Multiplicity_GradedChartCochains`, `Multiplicity_GradedLineBasisHasBasis`, `Multiplicity_KoszulConeFunctor`, `Multiplicity_KoszulHomologyMap`, `Multiplicity_KoszulQuotientFinite`, `Multiplicity_KoszulSwap`, `Multiplicity_KoszulTensorSingle`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechLevel`, `Multiplicity_LechNatTrans`, `Multiplicity_LechPiIso`, `Multiplicity_LechSignedUnit`, `Multiplicity_LechTorsionOf`, `Multiplicity_ModuleComplexQuotient`, `Multiplicity_PowerSeriesFlatVariables`, `Multiplicity_PrincipalCoverRegularRegularMap`, `Multiplicity_ReesRootUnfiltered`, `Multiplicity_SourceGradedThickeningNat`, `Multiplicity_TensorIdealRange`, `Multiplicity_TensorQuotientCommutation`.
--
--   **Imports.** It imports the bundles `OAIQ032L000`, `OAIQ032L001`, `OAIQ032L002`, `OAIQ032L003`, `OAIQ032L004`, `OAIQ032L005` and `OAIQ032L006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L020`, `OAIQ032L021` and `OAIQ032L023`; the statements `OAI.Lech.CharP.exists_length_with_module_limit`, `OAI.Lech.ReesRoot.sum_estimate`, `OAI.Lech.SourceGraded.acyclicity_finite_torsion`, `OAI.Lech.complex_estimate_allModule` and `OAI.Lech.ordinaryPower_stableImage_isoMod`; the proofs of `OAI.Lech.CharP.dutta_minimal_estimate`, `OAI.Lech.FrobeniusIntermediate.frobenius_homology_order_transfer`, `OAI.Lech.Koszul.length_quotient_tensor_le_sum`, `OAI.Lech.PrimeFiltration.Factors.euler_self`, `OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero`, `OAI.Lech.SourceGraded.acyclicity_finite_torsion`, `OAI.Lech.complex_estimate_allModule`, `OAI.Lech.cyclicDuttaSequence_small`, `OAI.Lech.cyclicDuttaSequence_tendsto`, `OAI.Lech.finiteHomology_extendScalars`, `OAI.Lech.frobenius_quotient_homology_bound`, `OAI.Lech.frobenius_quotient_homology_finiteLength`, `OAI.Lech.frobenius_quotient_homology_tendsto_zero`, `OAI.Lech.frobenius_shortComplex_homology_finiteLength` and `OAI.Lech.ordinaryPower_stableImage_isoMod`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L001
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L003
import Definitions.Def_OAIQ032L004
import Definitions.Def_OAIQ032L005
import Definitions.Def_OAIQ032L006

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLevel
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

noncomputable def lift (a n : ℕ) (e : Bounded h a n) :
    IdealFiltration.level (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n :=
  ⟨monic z (exponent e), (show Ideal.span (Set.range z) ^ n ≤ _ from le_sup_left)
      (monic_mem_power z (exponent_degree e))⟩

end MonomialSpanning
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))

def denominator : Poly R (h := h) := single (indicator s) 1


def polynomialEquiv : MvPolynomial (Fin h) R ≃ₐ[R] Poly R (h := h) :=
  AddMonoidAlgebra.domCongr R R
    (Finsupp.linearEquivFunOnFinite ℕ ℕ (Fin h)).toAddEquiv
end Lech.PartialLaurent

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechPiIso
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

section

section
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)


include hf

omit hf
variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)


lemma gradedMap_surjective (hs : Function.Surjective g) (j : ℕ) :
    Function.Surjective (gradedMap G H g hg j) := by
  intro b
  obtain ⟨a,ha⟩ := hs b
  refine ⟨DirectSum.decompose G a j, ?_⟩
  apply Subtype.ext
  change g (DirectSum.decompose G a j) = (b : B)
  rw [g.map_directSumDecompose,ha]
  exact DirectSum.decompose_of_mem_same H b.property

include hf

lemma pieceMap_surjective (hs : Function.Surjective g) (t : ℕ) :
    Function.Surjective (pieceMap G hf H g hg t) := by
  intro x
  obtain ⟨n,b,hb⟩ := exists_fraction H (map_mem g hf) t x
  obtain ⟨a,ha⟩ := gradedMap_surjective G H g hg hs (n*d+t) b
  refine ⟨pieceFraction G (f := f) t n a, ?_⟩
  rw [pieceMap_fraction,ha]
  exact Subtype.ext hb

open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] pieceMap gradedMap kernelFraction

end


open SetLike Graded
universe u

end


open SetLike Graded
universe u

end Lech.TwistedLocalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedChartCochains
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.ImageCech
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)


def restrict {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ) :
    term G H g y s t →ₗ[R] term G H g y v t :=
  TwistedLocalization.pieceTo H (map_mem g (GradedChart.denominator_mem G y hy s))
    (map_mem g (GradedChart.denominator_mem G y hy (v\s)))
    (by rw [←map_mul,GradedChart.denominator_mul_sdiff y hsv])
    (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t


abbrev cochains (n t : ℕ) :=
  (a : Fin n → Fin h) → term G H g y (ActualCech.intersection a) t

def d (n t : ℕ) : cochains G H g y n t →ₗ[R] cochains G H g y (n+1) t where
  toFun f a := ∑ i : Fin (n+1), (-1 : R)^i.val •
    restrict G H g y hy (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))
  map_add' f k := by
    funext a
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext a
    simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

include hy in
lemma mapTerm_surjective (hsurj : Function.Surjective g) (s : Finset (Fin h)) (t : ℕ) :
    Function.Surjective (mapTerm G H g hg y hy s t) :=
  TwistedLocalization.pieceMap_surjective _ _ _ _ _ hsurj t

end Lech.ImageCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrincipalCoverRegularRegularMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
abbrev Ring := AddMonoidAlgebra R (Exponent n)

end Lech.ProductLaurent


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.UnitSection
open scoped TensorProduct
universe u v w
variable {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

def equiv (m : M) (e : S ⊗[R] M ≃ₗ[S] S) (u : Sˣ)
    (he : e (1 ⊗ₜ[R] m)=(u:S)) : R ≃ₗ[R] M := by
  apply LinearEquiv.ofBijective (map m)
  apply FFTensorMaps.bijective (R := R) (M := R) (N := M) (Q := S) S
    (map m) ((TensorProduct.AlgebraTensorModule.rid R S S) ≪≫ₗ LinearEquiv.smulOfUnit u) e
  exact compat S m e u he
end Lech.UnitSection


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedLineBasisHasBasis
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.LineBasisExtension
open scoped TensorProduct
universe u v w x y
variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable (C : Type x) [CommRing C] [Algebra R C] [Algebra L C] [IsScalarTower R L C]
variable {S : Type y} [CommRing S] [Algebra R S]

lemma value_extend (f : M →ₗ[R] S) (e : L ≃ₗ[L] L ⊗[R] M) :
    f.baseChange C (extend C e 1)=coefficients C (f.baseChange L (e 1)) := by
  change f.baseChange C (TensorProduct.AlgebraTensorModule.cancelBaseChange R L C C M (1 ⊗ₜ[L] e 1))=_
  generalize e 1=z
  induction z using OAI.tensorInductionOn with
  | tmul l m =>
    simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,LinearMap.baseChange_tmul,
      coefficients_tmul,Algebra.smul_def,mul_one]
  | add z w hz hw => simpa only [TensorProduct.tmul_add,map_add] using congrArg₂ (·+·) hz hw

end Lech.LineBasisExtension


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechSignedUnit
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.LineBasisExtension
open scoped TensorProduct
universe u v w x
variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable (C : Type x) [CommRing C] [Algebra R C] [Algebra L C] [IsScalarTower R L C]
lemma included_smul (l : L) (z : L ⊗[R] M) :
    included C (l • z)=algebraMap L C l • included C z := by
  induction z using OAI.tensorInductionOn with
  | tmul a m => simp only [TensorProduct.smul_tmul',smul_eq_mul,included_tmul,map_mul]
  | add z w hz hw => simp only [smul_add,map_add,hz,hw]
lemma extend_one (e : L ≃ₗ[L] L ⊗[R] M) : extend C e 1=included C (e 1) := by
  change TensorProduct.AlgebraTensorModule.cancelBaseChange R L C C M (1 ⊗ₜ[L] e 1)=_
  generalize e 1=z
  induction z using OAI.tensorInductionOn with
  | tmul l m =>
    simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,included_tmul,Algebra.smul_def,mul_one]
  | add z w hz hw => simp only [TensorProduct.tmul_add,map_add,hz,hw]
 

lemma extend_coefficient (e : L ≃ₗ[L] L ⊗[R] M) (l : L) :
    extend C e (algebraMap L C l)=included C (e l) := by
  conv_rhs => rw [show l=l • (1:L) by simp]
  rw [e.map_smul,included_smul,←extend_one,←(extend C e).map_smul]
  simp
end Lech.LineBasisExtension


namespace Lech.LocalizationImageCover
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {C : Type w} [CommRing C] [Algebra R C]
variable {ι : Type*} [Fintype ι] (q : ι → R)


theorem globalImage_iff (hq : Ideal.span (Set.range q)=⊤)
    (φ : ∀ i,Localization.Away (q i) →ₐ[R] C) (x : C ⊗[R] M) :
    (∃ m : M,1 ⊗ₜ[R] m=x) ↔ ∀ i,∃ z,localMap q i (φ i) z=x := by
  constructor
  · rintro ⟨m,rfl⟩ i;exact ⟨1 ⊗ₜ[R] m,localMap_from q i (φ i) m⟩
  · intro hx
    choose z hz using hx
    choose e a ha using fun i => localMap_clear q i (φ i) (z i)
    have hax (i : ι) : 1 ⊗ₜ[R] a i=q i^e i • x := by rw [ha i,hz i]
    let N := Finset.univ.sup e
    have he (i : ι) : e i≤N := Finset.le_sup (Finset.mem_univ i)
    let b (i : ι) : M := q i^(N-e i) • a i
    have hb (i : ι) : 1 ⊗ₜ[R] b i=q i^N • x := by
      rw [show b i=q i^(N-e i) • a i from rfl,TensorProduct.tmul_smul,hax,smul_smul,←pow_add,Nat.sub_add_cancel (he i)]
    obtain ⟨c,hc⟩ := FiniteCoverCech.partition R q hq N
    refine ⟨∑ i,c i • b i,?_⟩
    rw [TensorProduct.tmul_sum]
    simp only [TensorProduct.tmul_smul,hb,smul_smul,←Finset.sum_smul,hc,one_smul]
end Lech.LocalizationImageCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedThickeningNat
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.coneFunctor_linear _root_.OAI.Lech.Koszul.instAdditiveCochainComplexIntConeFunctor_1 _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex

open CochainComplex CochainComplex.HomComplex
namespace Lech.Koszul

variable {R : Type*} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]
variable {F G : CochainComplex C ℤ}

lemma tensor_entry_nullhomotopic (zs : List R) (F : CochainComplex C ℤ)
    (a : R) (ha : a ∈ zs) : Nonempty (Homotopy (a • 𝟙 (tensor zs F)) 0) := by
  induction zs with
  | nil => simp at ha
  | cons b zs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨coneEntryHomotopy a (tensor zs F)⟩
    · obtain ⟨h⟩ := ih ha
      exact ⟨coneScalarHomotopy a b h⟩


instance instAdditiveCochainComplexIntTensorFunctor (zs : List R) : (tensorFunctor (C := C) zs).Additive := by
  induction zs with
  | nil => exact inferInstanceAs (𝟭 (CochainComplex C ℤ)).Additive
  | cons a zs ih =>
    change (tensorFunctor zs ⋙ coneFunctor a).Additive
    infer_instance

 

noncomputable def tensorSplitting (zs : List R) (S : ShortComplex (CochainComplex C ℤ))
    (hs : ∀ i, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting)
    (i : ℤ) :
    ((S.map (tensorFunctor zs)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting := by
  induction zs generalizing i with
  | nil => exact hs i
  | cons a zs ih =>
    exact coneSplitting a (S.map (tensorFunctor zs)) ih i


noncomputable def tensorShiftIso (zs : List R) (F : CochainComplex C ℤ) (n : ℤ) :
    (tensor zs F)⟦n⟧ ≅ tensor zs (F⟦n⟧) := by
  induction zs with
  | nil => exact Iso.refl _
  | cons a zs ih =>
    refine mappingCone.shiftIso (a • 𝟙 (tensor zs F)) n ≪≫ ?_ ≪≫
      (coneFunctor a).mapIso ih
    apply eqToIso
    congr 1

end Lech.Koszul
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulHomologyMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

lemma scalar_annihilates_homology (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (a : R) (ha : Homotopy (a • 𝟙 F) 0) (i : ℤ) :
    a ∈ Module.annihilator R (F.homology i) := by
  rw [Module.mem_annihilator]
  have h : a • 𝟙 (F.homology i) = 0 := by simpa using ha.homologyMap_eq i
  intro m
  exact congrArg (fun f : F.homology i ⟶ F.homology i => f m) h

lemma tensor_homology_annihilator (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    entryIdeal zs ≤ Module.annihilator R ((tensor zs F).homology i) := by
  apply Ideal.span_le.mpr
  intro a ha
  obtain ⟨h⟩ := tensor_entry_nullhomotopic zs F a ha
  exact scalar_annihilates_homology _ _ h _

variable {C : Type*} [Category C] [Abelian C] [CategoryTheory.Linear R C]

noncomputable def unit (zs : List R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  tensor zs ((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))

variable {F G : CochainComplex C ℤ}



noncomputable def unitHomologyGenerator (zs : List R) :
    ModuleCat.of R R ⟶ (unit zs).homology 0 := by
  induction zs with
  | nil => exact (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv
  | cons a zs ih => exact ih ≫ homologyMap (mappingCone.inr (a • 𝟙 (unit zs))) 0

noncomputable def unitHomologyQuotient (zs : List R) :
    ModuleCat.of R (R ⧸ entryIdeal zs) ⟶ (unit zs).homology 0 :=
  ModuleCat.ofHom ((entryIdeal zs).liftQ (unitHomologyGenerator zs).hom (by
    intro x hx
    change unitHomologyGenerator zs x = 0
    rw [show x = x • (1 : R) by simp, map_smul]
    exact Module.mem_annihilator.mp (tensor_homology_annihilator zs _ 0 hx) _))

end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechNatTrans
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex HomologicalComplex
universe u v
variable {R : Type u} [CommRing R]

noncomputable def quotientAugmentationNat (zs : List R) :
    (tensorFunctor zs : CochainComplex (ModuleCat.{v} R) ℤ ⥤ _) ⟶
      complexQuotient (entryIdeal zs) (.up ℤ) where
  app F := quotientAugmentation F zs
  naturality {F G} f := by
    change (tensorFunctor zs).map f ≫ augmentation _ zs _ =
      augmentation _ zs _ ≫ _
    let HF := fun r hr => complexQuotient_annihilated (entryIdeal zs) r
      (Ideal.subset_span hr) F
    let HG := fun r hr => complexQuotient_annihilated (entryIdeal zs) r
      (Ideal.subset_span hr) G
    exact (augmentation_naturality_source f (complexQuotientπ (entryIdeal zs) G)
      zs HG).trans ((congrArg (fun k => augmentation k zs HG)
        (complexQuotientπ_naturality (entryIdeal zs) f)).trans
        (augmentation_naturality_target (complexQuotientπ (entryIdeal zs) F)
          ((complexQuotient (entryIdeal zs) (.up ℤ)).map f) zs HF HG).symm)



lemma projectionTerm_surjective (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) (zs : List R) : Function.Surjective (projectionTerm F n zs).hom := by
  intro x
  refine ⟨((inclusion F zs).f n).hom x, ?_⟩
  exact congrArg (fun f => f.hom x) (inclusion_projectionTerm F n zs)



lemma projectionTerm_boundary_range
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (zs : List R) :
    LinearMap.range (((tensor zs F).d (n-1) n ≫ projectionTerm F n zs).hom) =
      entryIdeal zs • (⊤ : Submodule R (F.X n)) ⊔
        LinearMap.range (F.d (n-1) n).hom := by
  induction zs with
  | nil => simp [projectionTerm, entryIdeal]; rfl
  | cons r zs ih =>
    change LinearMap.range (((mappingCone (r • 𝟙 (tensor zs F))).d (n-1) n ≫
      (mappingCone.snd _).v n n _ ≫ projectionTerm F n zs).hom) = _
    rw [← Category.assoc, ModuleCat.hom_comp, LinearMap.range_comp,
      ModuleCat.hom_comp, scalarCone_boundary_range, Submodule.map_sup,
      scalar_range_eq_ideal_smul, Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (projectionTerm_surjective F n zs)]
    rw [← LinearMap.range_comp, ← ModuleCat.hom_comp, ih, entryIdeal_cons_for_top,
      Submodule.sup_smul, sup_assoc]

lemma projectionTerm_isIso_at_top
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (zs : List R)
    (hF : ∀ j, n < j → IsZero (F.X j)) : IsIso (projectionTerm F n zs) := by
  have := inclusion_isIso_at_top F zs n hF
  have : IsIso ((inclusion F zs).f n ≫ projectionTerm F n zs) := by
    rw [inclusion_projectionTerm]
    infer_instance
  exact IsIso.of_isIso_comp_left ((inclusion F zs).f n) _



lemma quotientAugmentation_homology_top
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (zs : List R)
    (hF : ∀ j, n < j → IsZero (F.X j)) (hd : F.d (n-1) n = 0) :
    IsIso (homologyMap (quotientAugmentation F zs) n) := by
  let K := tensor zs F
  let G := (complexQuotient (entryIdeal zs) (.up ℤ)).obj F
  let f := quotientAugmentation F zs
  let p := projectionTerm F n zs
  have hp : IsIso p := projectionTerm_isIso_at_top F n zs hF
  have hpf : f.f n = p ≫ (moduleQuotientπ (entryIdeal zs)).app (F.X n) :=
    augmentation_f_at_top _ zs _ n hF
  have hepi : Epi (f.f n) := by
    rw [hpf]
    exact epi_comp' (inferInstanceAs (Epi p))
      (inferInstanceAs (Epi ((moduleQuotientπ (entryIdeal zs)).app (F.X n))))
  have hGf : G.d (n-1) n = 0 := by
    change (moduleQuotient (entryIdeal zs)).map (F.d (n-1) n) = 0
    rw [hd, Functor.map_zero]
  have hGg : G.d n (n+1) = 0 := by
    change (moduleQuotient (entryIdeal zs)).map (F.d n (n+1)) = 0
    rw [(hF (n+1) (by omega)).eq_zero_of_tgt (F.d n (n+1)), Functor.map_zero]
  have hKg : K.d n (n+1) = 0 :=
    (tensor_isZero_above F zs n hF (n+1) (by omega)).eq_zero_of_tgt _
  have : Epi ((shortComplexFunctor _ (.up ℤ) n).map f).τ₂ := hepi
  have hprev : (ComplexShape.up ℤ).prev n = n-1 :=
    (ComplexShape.up ℤ).prev_eq' (by change n-1+1=n; omega)
  have hnext : (ComplexShape.up ℤ).next n = n+1 :=
    (ComplexShape.up ℤ).next_eq' (by rfl)
  refine shortComplex_homologyMap_iso_of_augmentation
    ((shortComplexFunctor _ (.up ℤ) n).map f)
    (by change K.d n ((ComplexShape.up ℤ).next n) = 0; rw [hnext]; exact hKg)
    (by change G.d ((ComplexShape.up ℤ).prev n) n = 0; rw [hprev]; exact hGf)
    (by change G.d n ((ComplexShape.up ℤ).next n) = 0; rw [hnext]; exact hGg) ?_
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : p.hom x ∈ entryIdeal zs • (⊤ : Submodule R (F.X n)) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change ((moduleQuotientπ (entryIdeal zs)).app (F.X n)).hom (p.hom x) = 0
    change (f.f n).hom x = 0 at hx
    rw [hpf] at hx
    exact hx
  have hr := projectionTerm_boundary_range F n zs
  rw [hd, ModuleCat.hom_zero, LinearMap.range_zero, sup_bot_eq] at hr
  rw [← hr] at hx'
  obtain ⟨y,hy⟩ := hx'
  refine ⟨(K.XIsoOfEq hprev).inv.hom y, ?_⟩
  have hy' := (ModuleCat.mono_iff_injective p).mp inferInstance hy
  change (K.d ((ComplexShape.up ℤ).prev n) n).hom ((K.XIsoOfEq hprev).inv.hom y) = x
  have hc : (K.XIsoOfEq hprev).inv ≫ K.d ((ComplexShape.up ℤ).prev n) n = K.d (n-1) n := by simp
  change (((K.XIsoOfEq hprev).inv ≫ K.d ((ComplexShape.up ℤ).prev n) n).hom) y = x
  rw [hc]
  exact hy' 

end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulTensorSingle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech.Koszul
variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C]
  [CategoryTheory.Linear R C]

 
noncomputable def tensorSingleHomologyIso (zs : List R) (M : C) (j i : ℤ) :
    (tensor zs ((singleFunctor C j).obj M)).homology i ≅
      (tensor zs ((singleFunctor C 0).obj M)).homology (i - j) := by
  let e : ((singleFunctor C 0).obj M)⟦-j⟧ ≅ (singleFunctor C j).obj M :=
    ((CochainComplex.singleFunctors C).shiftIso (-j) j 0 (by omega)).app M
  have e' : tensor zs ((singleFunctor C j).obj M) ≅
      tensor zs (((singleFunctor C 0).obj M)⟦-j⟧) := by
    simpa only [tensorFunctor_obj] using (tensorFunctor zs).mapIso e.symm
  exact (homologyFunctor C (ComplexShape.up ℤ) i).mapIso
      (e' ≪≫ (tensorShiftIso zs ((singleFunctor C 0).obj M) (-j)).symm) ≪≫
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso (-j) i (i - j)
      (by omega)).app _

end Lech.Koszul


open scoped BigOperators


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open Koszul
universe u
variable {R : Type u} [CommRing R]

@[reassoc]
lemma complexQuotientMap_comp {I J K : Ideal R} (h : I ≤ J) (h' : J ≤ K)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (complexQuotientMap h (.up ℤ)).app F ≫ (complexQuotientMap h' (.up ℤ)).app F =
      (complexQuotientMap (h.trans h') (.up ℤ)).app F := by
  ext i : 1
  exact moduleQuotientMap_comp h h' (F.X i)



end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFlatVariables
attribute [-instance] _root_.OAI.Lech.Koszul.coneFunctor_linear _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace Lech.Koszul

variable {R : Type*} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]
variable {F G : CochainComplex C ℤ}

instance instAdditiveCochainComplexIntTensorFunctor_1 (zs : List R) : (tensorFunctor (C := C) zs).Additive := by
  induction zs with
  | nil => exact inferInstanceAs (𝟭 (CochainComplex C ℤ)).Additive
  | cons a zs ih =>
    change (tensorFunctor zs ⋙ coneFunctor a).Additive
    infer_instance

 

end Lech.Koszul

open scoped ENNReal ZeroObject

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex











open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian






















namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open RingTheory.Sequence
universe u v
variable {R : Type u} [CommRing R]

noncomputable def singleTensorHomologyZeroIso (M : ModuleCat.{v} R) (zs : List R) :
    (tensor zs (singleModule M)).homology 0 ≅
      ModuleCat.of R (M ⧸ (entryIdeal zs • (⊤ : Submodule R M))) := by
  let F := singleModule M
  have := quotientAugmentation_homology_top F 0 zs
    (fun j hj => isZero_single_obj_X (.up ℤ) 0 M j (by omega))
    (by apply (isZero_single_obj_X (.up ℤ) 0 M (-1) (by omega)).eq_zero_of_src)
  exact asIso (homologyMap (quotientAugmentation F zs) 0) ≪≫
    (homologyFunctor _ (.up ℤ) 0).mapIso
      ((singleMapHomologicalComplex (moduleQuotient (entryIdeal zs)) (.up ℤ) 0).app M) ≪≫
    singleObjHomologySelfIso (.up ℤ) 0 _

end Lech.Koszul
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulConeFunctor
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C]
  [CategoryTheory.Linear R C]

instance tensorFunctor_linear (zs : List R) : Functor.Linear R (tensorFunctor (C := C) zs) := by
  induction zs with
  | nil => exact inferInstanceAs (Functor.Linear R (𝟭 (CochainComplex C ℤ)))
  | cons a zs ih =>
    change Functor.Linear R (tensorFunctor zs ⋙ coneFunctor a)
    infer_instance

end Lech.Koszul


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R S : Type u} [CommRing R] [CommRing S]



noncomputable def restrictScalarsTensorIso (f : R →+* S) (zs : List R)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj (tensor (zs.map f) F) ≅
      tensor zs (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj F) := by
  induction zs with
  | nil => exact Iso.refl _
  | cons a zs ih =>
    change ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      (mappingCone (f a • 𝟙 (tensor (zs.map f) F))) ≅ _
    refine mappingCone.mapHomologicalComplexIso _ (ModuleCat.restrictScalars f) ≪≫ ?_
    rw [restrictScalars_map_scalar]
    exact (coneFunctor a).mapIso ih


noncomputable def restrictScalarsTensorHomologyIso (f : R →+* S) (zs : List R)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    (ModuleCat.restrictScalars f).obj ((tensor (zs.map f) F).homology i) ≅
      (tensor zs (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj F)).homology i :=
  (restrictScalarsHomologyIso f _ i).symm ≪≫
    (homologyFunctor _ _ i).mapIso (restrictScalarsTensorIso f zs F)

noncomputable def restrictScalarsSingleTensorHomologyIso (f : R →+* S) (zs : List R)
    (M : ModuleCat.{u} S) (i : ℤ) :
    (ModuleCat.restrictScalars f).obj
      ((tensor (zs.map f) ((single (ModuleCat S) (.up ℤ) 0).obj M)).homology i) ≅
      (tensor zs ((single (ModuleCat R) (.up ℤ) 0).obj
        ((ModuleCat.restrictScalars f).obj M))).homology i :=
  restrictScalarsTensorHomologyIso f zs _ i ≪≫
    (homologyFunctor _ _ i).mapIso
      ((tensorFunctor zs).mapIso
        ((singleMapHomologicalComplex (ModuleCat.restrictScalars f) (.up ℤ) 0).app M))
end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulSwap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.coneFunctor_linear _root_.OAI.Lech.Koszul.instAdditiveCochainComplexIntConeFunctor_1 _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]

lemma coneSwapX_involutive (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    coneSwapX a b F i ≫ coneSwapX b a F i = 𝟙 _ := by
  apply homotopyCofiber.ext_from_X (a • 𝟙 (scalarCone b F)) (i+1) i rfl
  · apply homotopyCofiber.ext_from_X (b • 𝟙 F) (i+1+1) (i+1) rfl
    · change cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _ =
        cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _
      simp only [inll_coneSwapX_assoc,Preadditive.neg_comp,Category.assoc,inll_coneSwapX,
        neg_neg,Category.comp_id]
    · change cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _ =
        cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _
      simp only [inrl_coneSwapX_assoc,inlr_coneSwapX,Category.comp_id]
  · apply homotopyCofiber.ext_from_X (b • 𝟙 F) (i+1) i rfl
    · change cInl b F i ≫ cInr a (scalarCone b F) i ≫ _ =
        cInl b F i ≫ cInr a (scalarCone b F) i ≫ _
      simp only [inlr_coneSwapX_assoc,inrl_coneSwapX,Category.comp_id]
    · change cInr b F i ≫ cInr a (scalarCone b F) i ≫ _ =
        cInr b F i ≫ cInr a (scalarCone b F) i ≫ _
      simp only [inrr_coneSwapX_assoc,inrr_coneSwapX,Category.comp_id]

noncomputable def coneSwapIso (a b : R) (F : CochainComplex C ℤ) :
    scalarCone a (scalarCone b F) ≅ scalarCone b (scalarCone a F) where
  hom := coneSwap a b F
  inv := coneSwap b a F
  hom_inv_id := by ext i; exact coneSwapX_involutive a b F i
  inv_hom_id := by ext i; exact coneSwapX_involutive b a F i

 

noncomputable def tensorConeIso (zs : List R) (a : R) (F : CochainComplex C ℤ) :
    scalarCone a (tensor zs F) ≅ tensor zs (scalarCone a F) := by
  induction zs with
  | nil => exact Iso.refl _
  | cons b zs ih => exact coneSwapIso a b (tensor zs F) ≪≫ (coneFunctor b).mapIso ih

end Lech.Koszul

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

namespace Koszul
instance moduleQuotient_linear (I : Ideal R) : (moduleQuotient (R:=R) I).Linear R where
  map_smul {M N} f x := by
    ext m
    obtain ⟨m,rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective m
    rfl

def quotient_nullhomotopy (I : Ideal R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (x : R) (H : Homotopy (x • 𝟙 F) 0) :
    Homotopy (x • 𝟙 ((complexQuotient I (.up ℤ)).obj F)) 0 := by
  simp only [complexQuotient]
  have h := (moduleQuotient I).mapHomotopy H
  simp only [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at h
  exact h
end Koszul



end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

def quotient_scalar_zero (I : Ideal R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (x : R) (hx : x∈I) :
    Homotopy (x • 𝟙 ((complexQuotient I (.up ℤ)).obj F)) 0 :=
  Homotopy.ofEq (by
    ext i : 1
    exact moduleQuotient_annihilated I x hx (F.X i))

end Lech.Koszul

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ModuleComplexQuotient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ModuleComplexQuotient
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)
  (P : ∀ p,Submodule R (K.X p))
  (hP : ∀ p q,P p ≤ (P q).comap (K.d p q).hom)


def projection : K ⟶ complex K P hP where
  f p := ModuleCat.ofHom (P p).mkQ
  comm' _ _ _ := rfl

def inclusion : IdealFiltered.subcomplex K P hP ⟶ K where
  f p := ModuleCat.ofHom (P p).subtype
  comm' _ _ _ := rfl

lemma inclusion_projection : inclusion K P hP ≫ projection K P hP=0 := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Submodule.Quotient.mk_eq_zero (P p)).mpr x.property

def shortComplex : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c) :=
  ShortComplex.mk (inclusion K P hP) (projection K P hP) (inclusion_projection K P hP)

end Lech.ModuleComplexQuotient

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorIdealRange
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) (a : ℕ) (hf : f.range = I^a • (⊤ : Submodule R N))
  (Q : Type u) [AddCommGroup Q] [Module R Q]

include hf in
lemma range_lTensor : (f.lTensor Q).range = I^a • (⊤ : Submodule R (Q ⊗[R] N)) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
        change x ⊗ₜ[R] f y ∈ _
        have hy : f y ∈ I^a • (⊤ : Submodule R N) := hf ▸ LinearMap.mem_range_self f y
        refine Submodule.smul_induction_on hy (fun r hr y hy => ?_) (fun y z hy hz => ?_)
        · rw [TensorProduct.tmul_smul]
          exact Submodule.smul_mem_smul hr Submodule.mem_top
        · rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hy hz
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro r hr x _
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
        have hy : r • y ∈ f.range := hf ▸ Submodule.smul_mem_smul hr Submodule.mem_top
        obtain ⟨z,hz⟩ := hy
        refine ⟨x ⊗ₜ[R] z,?_⟩
        rw [LinearMap.lTensor_tmul,hz,TensorProduct.tmul_smul]
    | add x y hx hy => rw [smul_add]; exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)

 

def equiv [Module.Flat R Q] (hinj : Function.Injective f) :
    (Q ⊗[R] M) ≃ₗ[R] ↥(I^a • (⊤ : Submodule R (Q ⊗[R] N))) :=
  (LinearEquiv.ofInjective (f.lTensor Q)
    (Module.Flat.lTensor_preserves_injective_linearMap f hinj)).trans
      (LinearEquiv.ofEq _ _ (range_lTensor I f a hf Q))

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorQuotientCommutation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (P : ModuleCat.{u} R) (M : ModuleCat.{u} R)

 

def tensorReductionEquiv :
    (P ⊗[R] (M ⧸ (I • (⊤ : Submodule R M)))) ≃ₗ[R]
      ((P ⊗[R] M) ⧸ (I • (⊤ : Submodule R (P ⊗[R] M)))) :=
  (TensorProduct.tensorQuotientEquiv P (I • (⊤ : Submodule R M))).trans
    (Submodule.quotEquivOfEq _ _ (by
      change (((I • (⊤ : Submodule R M)).subtype).lTensor P).range = _
      simpa only [pow_one] using range_lTensor I (I • (⊤ : Submodule R M)).subtype 1
        (by simp only [Submodule.range_subtype,pow_one]) P))



def tensorReductionIso :
    quotientFunctor I ⋙ (curriedTensor (ModuleCat.{u} R)).obj P ≅
      (curriedTensor (ModuleCat.{u} R)).obj P ⋙ quotientFunctor I :=
  NatIso.ofComponents (fun M => (tensorReductionEquiv I P M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x y =>
        induction y using Submodule.Quotient.induction_on with
        | _ y => rfl)
end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootUnfiltered
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

lemma zero_term_top (Q : ModuleCat.{u} R) (p : ℤ) : term I F h 0 Q p=⊤ := by
  simp [term,order]

end Lech.IdealFiltered

end

end OAI
end


