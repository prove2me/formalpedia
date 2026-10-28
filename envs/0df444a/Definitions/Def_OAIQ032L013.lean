-- Prove2me | Definitions.Def_OAIQ032L013
-- name    : OAIQ032L013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:48:19.127254+00:00
-- url     : https://prove2.me/theorems/be4157b0-c9f3-4c8a-a016-0b4b33aab58e
-- title:
--   Definitions bundle OAIQ032L013 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 29 definitions, 1 inductive type or structure, 2 instances and 16 theorems. The definitions and types are `OAI.Lech.FiniteModuleCech.Map`, `OAI.Lech.FiniteModuleCech.Map.cochains`, `OAI.Lech.FiniteModuleCech.Map.coefficients`, `OAI.Lech.FiniteModuleCech.Map.neg`, `OAI.Lech.FiniteModuleCech.Map.prodDesc`, `OAI.Lech.FiniteModuleCech.Map.prodLift`, `OAI.Lech.FiniteModuleCech.cochainsShortComplex`, `OAI.Lech.FiniteModuleCech.coefficients`, `OAI.Lech.FiniteModuleCech.copiesDiagonal`, `OAI.Lech.FiniteModuleCech.copiesDiagram`, `OAI.Lech.FiniteModuleCech.copiesProjection`, `OAI.Lech.FiniteModuleCech.copiesReindex`, `OAI.Lech.FiniteModuleCech.copiesSuccEquiv`, `OAI.Lech.FiniteModuleCech.diagramShortComplex`, `OAI.Lech.FiniteModuleCech.prodDiagram`, `OAI.Lech.FiniteModuleCech.prodInl`, `OAI.Lech.FiniteModuleCech.prodSnd`, `OAI.Lech.FiniteModuleCech.reduction`, `OAI.Lech.GradedChart.cochains`, `OAI.Lech.GradedChart.d`, `OAI.Lech.Homogeneous.awayCongr`, `OAI.Lech.IdealFiltered.ambientInclusion`, `OAI.Lech.IdealFiltered.coefficientNullHomotopy`, `OAI.Lech.IdealFiltered.complex`, `OAI.Lech.IdealFiltered.map`, `OAI.Lech.IdealFiltered.subcomplexNullHomotopy`, `OAI.Lech.IdealFiltration.inclusion`, `OAI.Lech.TorsionLength.realValue`, `OAI.Lech.TwistedLocalization.imagePieceTo`, `OAI.Lech.finiteHomologyEuler`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_CechCopies`, `Multiplicity_CechExact`, `Multiplicity_CechProducts`, `Multiplicity_CechReduction`, `Multiplicity_FilteredFractionReesDenominator`, `Multiplicity_FilteredFractionReesDenominatorTheory`, `Multiplicity_FiniteModuleCech`, `Multiplicity_GradedChartCochains`, `Multiplicity_HomogeneousFunctor`, `Multiplicity_IdealFilteredComplex`, `Multiplicity_IdealFilteredHomotopy`, `Multiplicity_IdealGradedRing`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechLevel`, `Multiplicity_LechPiIso`, `Multiplicity_ScalarChartComparison`.
--
--   **Imports.** It imports the bundles `OAIQ032L000`, `OAIQ032L002`, `OAIQ032L003`, `OAIQ032L004` and `OAIQ032L005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L020`, `OAIQ032L021` and `OAIQ032L022`; the statement `OAI.Lech.ReesRoot.sum_estimate`; the proofs of `OAI.Lech.PrimeFiltration.Factors.euler_self`, `OAI.Lech.complex_estimate_allModule` and `OAI.Lech.short_rank_euler_zero`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L003
import Definitions.Def_OAIQ032L004
import Definitions.Def_OAIQ032L005

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLevel
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech
universe u
variable {R : Type u} [CommRing R]
namespace IdealFiltration

def inclusion (I J : Ideal R) (n : ℕ) : Piece I J n →ₗ[R] R ⧸ level I J (n + 1) :=
  (next I J n).liftQ (((level I J (n + 1)).mkQ).comp (level I J n).subtype) (by
    intro x hx
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, next, Submodule.mem_comap] using hx)

end IdealFiltration
end Lech

open CategoryTheory
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

lemma monomial_mem_shifted_iff (i : ℕ) (x : ↥(I ^ i)) :
    monomial I i x ∈ shifted I ↔ (x : R) ∈ I ^ (i + 1) := by
  constructor
  · intro hx
    have h := hx i
    simpa using h
  · intro hx j
    change (Polynomial.monomial i (x : R)).coeff j ∈ I ^ (j + 1)
    by_cases hij : i = j
    · subst j; simpa using hx
    · simp [Polynomial.coeff_monomial, hij]

end Lech.IdealGraded


namespace Lech.Grading
open SetLike MvPolynomial
variable {S B ι : Type*} [CommRing S] [CommRing B] [Algebra S B]
  (G : ℕ → Submodule S B) [GradedAlgebra G] (x : ι → B)

attribute [local instance] MvPolynomial.gradedAlgebra

lemma polynomialMap_surjective (hx : ∀ i, x i ∈ G 1)
    (hgen : Algebra.adjoin S (Set.range x) = ⊤) :
    Function.Surjective (polynomialMap G x hx) := by
  exact (AlgHom.range_eq_top (aeval x)).mp
    (by simpa only [MvPolynomial.aeval_range] using hgen)
end Lech.Grading


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechPiIso
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


include hf

omit [GradedAlgebra H] in
 

lemma kernel_fraction (t : ℕ) (x : LinearMap.ker (pieceMap G hf H g hg t)) :
    ∃ (n : ℕ) (a : LinearMap.ker (gradedMap G H g hg (n*d+t))),
      pieceFraction G (f := f) t n a = (x : piece G (f := f) (d := d) t) := by
  obtain ⟨n,a,ha⟩ := exists_fraction G hf t x
  have hz := congrArg Subtype.val x.property
  change ambientMap G H g hg ((x : piece G (f := f) (d := d) t) : Localization.Away f) = 0 at hz
  rw [←ha, ambientMap_fraction] at hz
  simp only [fraction, LinearMap.coe_mk, AddHom.coe_mk, Localization.mk_eq_mk'] at hz
  obtain ⟨⟨v,hv⟩,he⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hz
  obtain ⟨k,rfl⟩ := hv
  change (g f)^k * g (a : A) = 0 at he
  have hm : f^k*(a : A) ∈ G ((k+n)*d+t) := by
    rw [add_mul, add_assoc]
    exact mul_mem_graded (by simpa only [nsmul_eq_mul, Nat.cast_id] using
      (pow_mem_graded k hf)) a.property
  have hk : gradedMap G H g hg ((k+n)*d+t) ⟨f^k*(a : A),hm⟩ = 0 := by
    apply Subtype.ext
    change g (f^k*(a : A)) = 0
    simpa only [map_mul,map_pow] using he
  refine ⟨k+n,⟨⟨f^k*(a : A),hm⟩,hk⟩,?_⟩
  apply Subtype.ext
  rw [←ha]
  change Localization.mk _ _ = Localization.mk _ _
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one,one_mul,pow_add]
  ring

omit [GradedAlgebra H] in
 

lemma kernel_fraction_eq (t : ℕ) (x : piece G (f := f) (d := d) t)
    (hx : pieceMap G hf H g hg t x=0) :
    ∃ (n : ℕ) (a : G (n*d+t)), g (a:A)=0 ∧ pieceFraction G (f := f) t n a=x := by
  obtain ⟨n,a,ha⟩ := kernel_fraction G hf H g hg t ⟨x,hx⟩
  refine ⟨n,a.val,?_,ha⟩
  exact congrArg Subtype.val a.property


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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.GradedChart
open SetLike Graded
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)

 
abbrev cochains (n t : ℕ) := (a : Fin n → Fin h) → term G y (ActualCech.intersection a) t

 
def d (n t : ℕ) : cochains G y n t →ₗ[R] cochains G y (n+1) t where
  toFun f a := ∑ i : Fin (n+1), (-1 : R)^i.val •
    restrict G y hy (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))
  map_add' f g := by
    funext a
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext a
    simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
end Lech.GradedChart


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominator
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a)=r • g a)
  {f q c : A} {d e k : ℕ} (hf : f ∈ G d) (hc : c ∈ G k)
  (hfc : f*c=q) (hdeg : d+k=e)

 
def imagePieceTo (t : ℕ) : piece H (f := g f) (d := d) t →ₗ[R]
    piece H (f := g q) (d := e) t :=
  pieceTo H (map_mem g hf) (map_mem g hc) (by rw [←map_mul,hfc]) hdeg t

end Lech.TwistedLocalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech

section

section
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}
namespace TorsionLength
variable (ℓ : TorsionLength I)

noncomputable def realValue (M : ModuleCat.{u} R) : ℝ := (ℓ.value M).toReal

end TorsionLength

end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ℓ : TorsionLength I)
 

def finiteHomologyEuler (K : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N+1),(-1:ℝ)^i*ℓ.realValue (K.homology (m+i))
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
 
structure Map (D E : Diagram R ι) where
  app : ∀ s, D.obj s ⟶ E.obj s
  naturality : ∀ {s t : Finset ι} (hst : s ⊆ t), D.res hst ≫ app t = app s ≫ E.res hst

namespace Map
variable (φ : Map D E)
def cochains (n : ℕ) : FiniteModuleCech.cochains D n →ₗ[R] FiniteModuleCech.cochains E n where
  toFun f s := (φ.app s.val).hom (f s)
  map_add' _ _ := by funext s; exact map_add _ _ _
  map_smul' _ _ := by funext s; exact map_smul _ _ _
end Map
end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.LocalLine
open scoped TensorProduct
universe u v w z
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]
variable (L : Type z) [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
attribute [local instance] OAI.Lech.LocalLine.instAlgebraTensorProduct_solutions
local instance instIsScalarTowerTensorProduct_solutions : IsScalarTower R S (L ⊗[R] S) := Algebra.TensorProduct.right_isScalarTower


end Lech.LocalLine


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

def coefficients : Diagram R ι where
  obj s := F.obj (D.obj s)
  res h := F.map (D.res h)
  res_self s := by rw [D.res_self,F.map_id]
  res_comp h h' := by rw [←F.map_comp,D.res_comp]

def Map.coefficients {E : Diagram R ι} (φ : Map D E) :
    Map (coefficients D F) (coefficients E F) where
  app s := F.map (φ.app s)
  naturality h := by
    change F.map (D.res h) ≫ F.map (φ.app _) = F.map (φ.app _) ≫ F.map (E.res h)
    rw [←F.map_comp,←F.map_comp,φ.naturality]

variable (I : Ideal R)
abbrev reduction := coefficients D (TensorIdeal.quotientFunctor I)

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechExact
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type}
variable {D E G : Diagram R ι} (φ : Map D E) (ψ : Map E G)
  (hzero : ∀ s,φ.app s ≫ ψ.app s=0)

include hzero in
lemma Map.cochains_comp_zero (q : ℕ) : ψ.cochains q ∘ₗ φ.cochains q=0 := by
  apply LinearMap.ext
  intro x
  funext s
  exact congrArg (fun f : D.obj s.val ⟶ G.obj s.val => f.hom (x s)) (hzero s.val)

def diagramShortComplex (s : Finset ι) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (φ.app s) (ψ.app s) (hzero s)

def cochainsShortComplex (q : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (φ.cochains q)) (ModuleCat.ofHom (ψ.cochains q))
    (ModuleCat.hom_ext (Map.cochains_comp_zero φ ψ hzero q))

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechProducts
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type}
variable (D E : Diagram R ι)

def prodDiagram : Diagram R ι where
  obj s := ModuleCat.of R (D.obj s × E.obj s)
  res {s t} hst := ModuleCat.ofHom ((D.res hst).hom.prodMap (E.res hst).hom)
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((D.res _).hom x.1,(E.res _).hom x.2)=x
    rw [D.res_self,E.res_self]
    rfl
  res_comp {s t v} hst htv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((D.res htv).hom ((D.res hst).hom x.1),(E.res htv).hom ((E.res hst).hom x.2))=_
    exact Prod.ext (congrArg (fun f : D.obj s ⟶ D.obj v => f.hom x.1) (D.res_comp hst htv))
      (congrArg (fun f : E.obj s ⟶ E.obj v => f.hom x.2) (E.res_comp hst htv))

variable {D E} {G : Diagram R ι}
def Map.prodLift (φ : Map G D) (ψ : Map G E) : Map G (prodDiagram D E) where
  app s := ModuleCat.ofHom ((φ.app s).hom.prod (ψ.app s).hom)
  naturality {s t} hst := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (congrArg (fun f : G.obj s ⟶ D.obj t => f.hom x) (φ.naturality hst))
      (congrArg (fun f : G.obj s ⟶ E.obj t => f.hom x) (ψ.naturality hst))

def Map.prodDesc (φ : Map D G) (ψ : Map E G) : Map (prodDiagram D E) G where
  app s := ModuleCat.ofHom ((φ.app s).hom.coprod (ψ.app s).hom)
  naturality {s t} hst := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (φ.app t).hom ((D.res hst).hom x.1)+(ψ.app t).hom ((E.res hst).hom x.2)=
      (G.res hst).hom ((φ.app s).hom x.1+(ψ.app s).hom x.2)
    rw [map_add]
    exact congrArg₂ (·+·) (congrArg (fun f : D.obj s ⟶ G.obj t => f.hom x.1) (φ.naturality hst))
      (congrArg (fun f : E.obj s ⟶ G.obj t => f.hom x.2) (ψ.naturality hst))

def Map.neg (φ : Map D E) : Map D E where
  app s := -(φ.app s)
  naturality {s t} hst := by rw [Preadditive.comp_neg,Preadditive.neg_comp,φ.naturality hst]

variable (D E)
def prodInl : Map D (prodDiagram D E) where
  app s := ModuleCat.ofHom (LinearMap.inl R (D.obj s) (E.obj s))
  naturality {s t} hst := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((D.res hst).hom x,0)=((D.res hst).hom x,(E.res hst).hom 0)
    rw [map_zero]
def prodSnd : Map (prodDiagram D E) E where
  app s := ModuleCat.ofHom (LinearMap.snd R (D.obj s) (E.obj s))
  naturality := by intros; rfl
lemma prod_comp_zero (s : Finset ι) : (prodInl D E).app s ≫ (prodSnd D E).app s=0 := rfl
end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredComplex
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

section Linear
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) (s : ℕ) (hf : f.range ≤ I^s • (⊤ : Submodule R N))

variable (Q : Type u) [AddCommGroup Q] [Module R Q]
include hf in
lemma tensor_range_le :
    (f.rTensor Q).range ≤ I^s • (⊤ : Submodule R (N ⊗[R] Q)) := by
  rintro _ ⟨x,rfl⟩
  induction x using OAI.tensorInductionOn with
  | tmul x y =>
      change f x ⊗ₜ[R] y ∈ _
      have hx := hf (LinearMap.mem_range_self f x)
      refine Submodule.smul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
      · rw [←TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      · rw [TensorProduct.add_tmul]
        exact Submodule.add_mem _ hx hy
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
end Linear



variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (Q : ModuleCat.{u} R)

include hd in
lemma term_d (p q : ℤ) :
    term I F h s Q p ≤ (term I F h s Q q).comap ((tensorComplex F Q).d p q).hom := by
  by_cases hpq : q=p+1
  · subst q
    rw [←Submodule.map_le_iff_le_comap]
    have hr := tensor_range_le I (F.d p (p+1)).hom s (hd p) Q
    have hh := map_power_le I ((F.d p (p+1)).hom.rTensor Q) s hr (order h s p)
    exact hh.trans (Submodule.smul_mono_left (Ideal.pow_le_pow_right (order_step h s p)))
  · have he : ¬(ComplexShape.up ℤ).Rel p q := by simpa only [ComplexShape.up_Rel,eq_comm] using hpq
    rw [(tensorComplex F Q).shape p q he]
    intro x hx
    exact (term I F h s Q q).zero_mem

 

def complex : CochainComplex (ModuleCat.{u} R) ℤ :=
  subcomplex (tensorComplex F Q) (term I F h s Q) (term_d I F h s hd Q)

 

def ambientInclusion : complex I F h s hd Q ⟶ tensorComplex F Q where
  f p := ModuleCat.ofHom (term I F h s Q p).subtype
  comm' _ _ _ := rfl

instance ambientInclusion_mono (p : ℤ) : Mono ((ambientInclusion I F h s hd Q).f p) :=
  (ModuleCat.mono_iff_injective _).mpr (term I F h s Q p).injective_subtype



def map {Q Q' : ModuleCat.{u} R} (f : Q ⟶ Q') :
    complex I F h s hd Q ⟶ complex I F h s hd Q' :=
  subcomplexMap (tensorComplex F Q) (tensorComplex F Q')
    (term I F h s Q) (term I F h s Q')
    (term_d I F h s hd Q) (term_d I F h s hd Q') (tensorMap F f)
    (fun p => Submodule.smul_top_le_comap_smul_top (I^(order h s p)) ((tensorMap F f).f p).hom)

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredHomotopy
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

 
def subcomplexNullHomotopy {ι : Type*} {c : ComplexShape ι}
    (K L : HomologicalComplex (ModuleCat.{u} R) c)
    (P : ∀ p, Submodule R (K.X p)) (T : ∀ p, Submodule R (L.X p))
    (hP : ∀ p q, P p ≤ (P q).comap (K.d p q).hom)
    (hT : ∀ p q, T p ≤ (T q).comap (L.d p q).hom)
    (f : K ⟶ L) (hf : ∀ p, P p ≤ (T p).comap (f.f p).hom)
    (H : Homotopy f 0) (hH : ∀ p q, P p ≤ (T q).comap (H.hom p q).hom) :
    Homotopy (subcomplexMap K L P T hP hT f hf) 0 where
  hom p q := ModuleCat.ofHom (((H.hom p q).hom.comp (P p).subtype).codRestrict (T q)
    (fun x => hH p q x.property))
  zero p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (H.hom p q).hom x.val=0
    rw [H.zero p q hpq]
    rfl
  comm p := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun g : K.X p ⟶ L.X p => g.hom x.val) (H.comm p)

lemma order_mono (h s : ℕ) : Monotone (order h s) := by
  intro p q hpq
  unfold order
  apply Nat.mul_le_mul_right
  exact Int.toNat_le_toNat (by omega)

variable (I : Ideal R)

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  {Q Q' : ModuleCat.{u} R} (inc : Q ⟶ Q')

 

def coefficientNullHomotopy (H : Homotopy (tensorMap F inc) 0) :
    Homotopy (map I F h s hd inc) 0 :=
  subcomplexNullHomotopy (tensorComplex F Q) (tensorComplex F Q')
    (term I F h s Q) (term I F h s Q')
    (term_d I F h s hd Q) (term_d I F h s hd Q') (tensorMap F inc)
    (fun p => Submodule.smul_top_le_comap_smul_top (I^(order h s p)) ((tensorMap F inc).f p).hom)
    H (by
      intro p q
      by_cases hpq : (ComplexShape.up ℤ).Rel q p
      · apply linear_decreases
        apply order_mono
        change q+1=p at hpq
        omega
      · rw [H.zero p q hpq]
        intro x hx
        exact (term I F h s Q' q).zero_mem)

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_HomogeneousFunctor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A),g (r • a)=r • g a)
attribute [local instance] awayAddCommGroup

instance awayAlgebra (element : A) : Algebra R (Away G element) :=
  Algebra.ofModule
    (fun scalar left right => by
      apply val_injective (Submonoid.powers element)
      simp only [val_mul, val_smul, smul_mul_assoc])
    (fun scalar left right => by
      apply val_injective (Submonoid.powers element)
      simp only [val_mul, val_smul, mul_smul_comm])

lemma awayMap_one (f : A) : awayMap G H g hg f 1 = 1 :=
  map_one (Away.map g f)
lemma awayMap_mul (f : A) (a b : Away G f) :
    awayMap G H g hg f (a*b) = awayMap G H g hg f a * awayMap G H g hg f b :=
  map_mul (Away.map g f) a b
lemma awayMap_mk {f : A} {d : ℕ} (hf : f∈G d) (j : ℕ) (a : A) (ha : a∈G (j • d)) :
    awayMap G H g hg f (Away.mk G hf j a ha) =
      Away.mk H (Graded.map_mem g hf) j (g a) (Graded.map_mem g ha) :=
  Away.map_mk g f hf j a ha

 

def awayCongr {f q : A} (e : f=q) : Away G f ≃ₐ[R] Away G q := by
  subst q
  exact AlgEquiv.refl
lemma awayCongr_mk {f q : A} (e : f=q) {d : ℕ} (hf : f∈G d) (hq : q∈G d)
    (j : ℕ) (a : A) (ha : a∈G (j • d)) :
    awayCongr G e (Away.mk G hf j a ha)=Away.mk G hq j a ha := by
  subst q
  rfl

lemma awayCongr_symm_mk {f q : A} (e : f=q) {d : ℕ} (hf : f∈G d) (hq : q∈G d)
    (j : ℕ) (a : A) (ha : a∈G (j • d)) :
    (awayCongr G e).symm (Away.mk G hq j a ha)=Away.mk G hf j a ha := by
  subst q
  rfl
end Lech.Homogeneous

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCopies
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
  (D : Diagram R ι)

def copiesDiagram (κ : Type) : Diagram R ι where
  obj s := ModuleCat.of R (κ → D.obj s)
  res hst := ModuleCat.ofHom (LinearMap.pi fun k => (D.res hst).hom.comp (LinearMap.proj k))
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext k
    change (D.res (Finset.Subset.refl s)).hom (x k)=x k
    rw [D.res_self]
    rfl
  res_comp hst htv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext k
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (D.res_comp hst htv)) (x k)

def copiesDiagonal (κ : Type) : Map D (copiesDiagram D κ) where
  app s := ModuleCat.ofHom (LinearMap.pi fun _ => LinearMap.id)
  naturality _ := by rfl

def copiesProjection {κ : Type} (k : κ) : Map (copiesDiagram D κ) D where
  app s := ModuleCat.ofHom (LinearMap.proj k)
  naturality _ := by rfl

variable {I : Ideal R} (ell : TorsionLength I)

def copiesReindex {κ η : Type} (e : κ ≃ η) (s : Finset ι) :
    (copiesDiagram D κ).obj s ≃ₗ[R] (copiesDiagram D η).obj s where
  toFun x k := x (e.symm k)
  invFun x k := x (e k)
  left_inv x := by funext k; simp only [Equiv.symm_apply_apply]
  right_inv x := by funext k; simp only [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def copiesSuccEquiv (a : ℕ) (s : Finset ι) :
    (copiesDiagram D (Fin (a+1))).obj s ≃ₗ[R] (prodDiagram D (copiesDiagram D (Fin a))).obj s where
  toFun x := (x 0,fun k => x k.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext k; exact Fin.cases rfl (fun _ => rfl) k
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarChartComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
attribute [local instance] awayAddCommGroup
lemma awayCongr_restrict {f f' c c' q q' : A} {k : ℕ}
    (hf : f=f') (hc : c=c') (hq : q=q') (hg : c∈G k) (hg' : c'∈G k)
    (he : q=f*c) (he' : q'=f'*c') (x : Away G f) :
    awayCongr G hq (HomogeneousLocalization.awayMap G hg he x)=
      HomogeneousLocalization.awayMap G hg' he' (awayCongr G hf x) := by
  subst f'; subst c'; subst q'; rfl
end Lech.Homogeneous

end

end OAI
end


