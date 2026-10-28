-- Prove2me | Definitions.Def_OAIQ032L039
-- name    : OAIQ032L039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:29:28.326096+00:00
-- url     : https://prove2.me/theorems/84b61961-bf59-46e1-95e8-810306f7ce75
-- title:
--   Definitions bundle OAIQ032L039 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 16 definitions and 8 theorems. The definitions and types are `OAI.Lech.ReesRoot.cechNatTensorHomotopy`, `OAI.Lech.ReesRoot.cechZTensorHomotopy`, `OAI.Lech.ReesRoot.enlargedLayerShortComplex`, `OAI.Lech.ReesRoot.enlargedPath`, `OAI.Lech.ReesRoot.enlargedRowHomotopy`, `OAI.Lech.ReesRoot.enlargedRowIso`, `OAI.Lech.ReesRoot.enlargedRowNatIso`, `OAI.Lech.ReesRoot.enlargedStep`, `OAI.Lech.ReesRoot.intersectionCechHomotopy`, `OAI.Lech.ReesRoot.layerAtRowHomologyBasisIso`, `OAI.Lech.ReesRoot.layerAtRowIso`, `OAI.Lech.ReesRoot.permuteCechEquiv`, `OAI.Lech.ReesRoot.permuteCechIso`, `OAI.Lech.ReesRoot.permuteSections`, `OAI.Lech.ReesRoot.thickeningShortComplex`, `OAI.Lech.ReesRoot.ulrichCechIso`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ReesRootGLayer`, `Multiplicity_ReesRootGLayerCohomology`, `Multiplicity_ReesRootLayerCech`, `Multiplicity_ReesRootNilpotence`, `Multiplicity_ReesRootPermutation`, `Multiplicity_ReesRootPowerPath`, `Multiplicity_ReesRootRows`, `Multiplicity_ReesRootThickeningEuler`, `Multiplicity_ReesUlrichCech`, `Multiplicity_RootUlrichNaturality`.
--
--   **Imports.** It imports the bundles `OAIQ032L037` and `OAIQ032L038` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.Lech.ReesRoot.uniform_unit_nilpotence`; the proofs of `OAI.Lech.ReesRoot.enlargedAtTotal_finite`, `OAI.Lech.ReesRoot.layerAtTotal_finite`, `OAI.Lech.ReesRoot.rootLayerAtTotal_negative`, `OAI.Lech.ReesRoot.rootLayerAtTotal_nonnegative`, `OAI.Lech.ReesRoot.rootTotal_pure`, `OAI.Lech.ReesRoot.thickeningZ_euler`, `OAI.Lech.ReesRoot.thickeningZ_finite`, `OAI.Lech.ReesRoot.unfilteredEuler_diagonal`, `OAI.Lech.ReesRoot.unfilteredEuler_rank` and `OAI.Lech.ReesRoot.uniform_unit_nilpotence`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L037
import Definitions.Def_OAIQ032L038

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootNilpotence
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.cechInclusionIter_mono _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℕ)
  (H : ∀ k, Homotopy (z k^a • 𝟙 F) 0)



attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p10
attribute [local instance] OAI.Lech.ReesRoot.sectionBaseModule_p5
def intersectionCechHomotopy (t : Finset (Fin (n+1))) (m : Fin n → ℤ) :
    Homotopy (termTensorMap F (cechObj I z hz (raise m a) t)
      (cechInclusionIterApp I z hz m a t)) 0 := by
  classical
  letI : Fintype (PLift t.Nonempty) := Fintype.ofFinite _
  let Q : PLift t.Nonempty → ModuleCat.{u} R := fun ht =>
    ModuleCat.of R (Sections I z hz t ht.down (raise m a))
  let Q' : PLift t.Nonempty → ModuleCat.{u} R := fun ht =>
    ModuleCat.of R (Sections I z hz t ht.down m)
  exact TensorPi.homotopy (Q := Q) (Q' := Q') F
    (fun ht => ModuleCat.ofHom (inclusionIter I z hz t ht.down m a))
    (fun ht => intersectionTensorHomotopy I z hz F a H t ht.down m)

 

def cechNatTensorHomotopy (m : Fin n → ℤ) (q : ℕ) :
    Homotopy (termTensorMap F ((cech I z hz (raise m a)).X q)
      ((cechInclusionIter I z hz m a).f q)) 0 := by
  classical
  let Q : Set.powersetCard (Fin (n+1)) (q+1) → ModuleCat.{u} R := fun t =>
    cechObj I z hz (raise m a) t.val
  let Q' : Set.powersetCard (Fin (n+1)) (q+1) → ModuleCat.{u} R := fun t =>
    cechObj I z hz m t.val
  exact TensorPi.homotopy (Q := Q) (Q' := Q') F
    (fun t => cechInclusionIterApp I z hz m a t.val)
    (fun t => intersectionCechHomotopy I z hz F a H t.val m)

def cechZTensorHomotopy (m : Fin n → ℤ) (q : ℤ) :
    Homotopy (termTensorMap F ((cechZ I z hz (raise m a)).X q)
      ((cechInclusionZ I z hz m a).f q)) 0 := by
  by_cases hq : q < 0
  · apply Homotopy.ofEq
    have hzQ := cechZ_negative I z hz (raise m a) q hq
    have he : (cechInclusionZ I z hz m a).f q=0 := hzQ.eq_of_src _ _
    rw [he,termTensorMap_zero]
  · have heq : (q.toNat:ℤ)=q := by omega
    let e := (cech I z hz (raise m a)).extendXIso ComplexShape.embeddingUpNat heq
    let e' := (cech I z hz m).extendXIso ComplexShape.embeddingUpNat heq
    apply coefficientHomotopyOfIso F e e' _ _ _ (cechNatTensorHomotopy I z hz F a H m q.toNat)
    change e.hom ≫ (cechInclusionIter I z hz m a).f q.toNat =
      (extendMap (cechInclusionIter I z hz m a) ComplexShape.embeddingUpNat).f q ≫ e'.hom
    rw [extendMap_f _ _ heq]
    dsimp only [e,e']
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

variable (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))



def enlargedRowHomotopy (m : Fin n → ℤ) :
    TotalGhost.RowHomotopy (enlargedMap I z hz F h s hd (cechInclusionZ I z hz m a)) :=
  TotalGhost.RowHomotopy.ofRows (fun q =>
    IdealFiltered.coefficientNullHomotopy I F h s hd ((cechInclusionZ I z hz m a).f q)
      (cechZTensorHomotopy I z hz F a H m q))


def enlargedStep (m : Fin n → ℤ) (a N : ℕ) :
    enlargedAt I z hz F h s hd (twistSequence m a (N+1)) ⟶
      enlargedAt I z hz F h s hd (twistSequence m a N) :=
  enlargedMap I z hz F h s hd (cechInclusionZ I z hz (twistSequence m a N) a)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootRows
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ) (hgen : Ideal.span (Set.range z)=I)
  (p : ℤ) [Module.Flat R (F.X p)]

 
def enlargedRowNatIso :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℕ)).obj
      (cech I z hz (raise m (IdealFiltered.order h s p))) ≅
    ((IdealFiltered.rowFunctor I F h s hd p).mapHomologicalComplex (.up ℕ)).obj
      (cech I z hz m) :=
  IdealFiltered.rowIso I F h s hd _ _ p
    (cechInclusionIter I z hz m (IdealFiltered.order h s p))
    (cechInclusionIter_range I z hz m hgen (IdealFiltered.order h s p))
    (cechInclusionIter_injective I z hz m (IdealFiltered.order h s p))

 

def enlargedRowIso :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).obj
      (cechZ I z hz (raise m (IdealFiltered.order h s p))) ≅
      (enlargedAt I z hz F h s hd m).X p :=
  ComplexExtension.mapExtendIso ((curriedTensor (ModuleCat.{u} R)).obj (F.X p))
      (cech I z hz (raise m (IdealFiltered.order h s p))) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
      (enlargedRowNatIso I z hz F h s hd m hgen p) ≪≫
    (ComplexExtension.mapExtendIso (IdealFiltered.rowFunctor I F h s hd p)
      (cech I z hz m)).symm
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootGLayer
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)


variable (hgen : Ideal.span (Set.range z)=I)
include hgen in
lemma enlarged_first_range (p q : ℤ) :
    (((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1)).f p).f q).hom.range =
      I • (⊤ : Submodule R (((enlargedAt I z hz F h s hd m).X p).X q)) := by
  exact IdealFiltered.rowMap_range I F h s hd p ((cechInclusionZ I z hz m 1).f q)
    (by simpa only [pow_one] using cechInclusionZ_range I z hz m hgen 1 q)

include hgen in
lemma layerAt_zero :
    enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1) ≫
      layerAtProjection I z hz F h s hd m=0 := by
  apply Hom.ext
  funext p
  apply Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f,HomologicalComplex.zero_f,layerAtProjection_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Submodule.Quotient.mk
    ((((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1)).f p).f q).hom x)=0
  rw [Submodule.Quotient.mk_eq_zero,←enlarged_first_range I z hz F h s hd m hgen p q]
  exact LinearMap.mem_range_self _ _

 
def enlargedLayerShortComplex : ShortComplex (TotalGhost.Bic (R:=R)) :=
  ShortComplex.mk (enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1))
    (layerAtProjection I z hz F h s hd m) (layerAt_zero I z hz F h s hd m hgen)



def layerAtRowIso (p : ℤ) [Module.Flat R (F.X p)] :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).obj
      ((FiniteModuleCech.positiveComplex
        (exceptionalDiagram I z hz (raise m (IdealFiltered.order h s p)))).extend
          ComplexShape.embeddingUpNat) ≅ (layerAt I z hz F h s hd m).X p :=
  (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).mapIso
      (exceptionalCechZIso I z hz (raise m (IdealFiltered.order h s p))).symm ≪≫
    (NatIso.mapHomologicalComplex (TensorIdeal.tensorReductionIso I (F.X p)) (.up ℤ)).app
      (cechZ I z hz (raise m (IdealFiltered.order h s p))) ≪≫
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℤ)).mapIso
      (enlargedRowIso I z hz F h s hd m hgen p)
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootGLayerCohomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (p : ℤ) [Module.Flat R (F.X p)] (b : ℕ) (B : Module.Basis (Fin b) R (F.X p))

omit [LinearOrder (Chart n)] in
def layerAtRowHomologyBasisIso (q : ℤ) :
    ((layerAt I z hz F h s hd m).X p).homology q ≅
      ModuleCat.of R (Fin b → (exceptionalZ I z hz (raise m (IdealFiltered.order h s p))).homology q) :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso (layerAtRowIso I z hz F h s hd m hgen p).symm ≪≫
    TensorIdeal.tensorHomologyBasisIso (F.X p) b B _ q

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayerCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
variable (m : Fin n → ℤ)

variable (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p9
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p7
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p9
private local instance projectiveModule_r959813_1 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p6
attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p8
private local instance sectionBaseModule_r959813_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule
attribute [local instance] OAI.Lech.ReesRoot.nonemptyFinite
include hgen in
lemma layerDiagram_zero (s : Finset (Fin (n+1))) :
    (cechInclusionDiagram I z hz m).app s ≫ (layerProjection I z hz m).app s=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Submodule.Quotient.mk ((cechInclusionApp I z hz m s).hom x)=0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (TensorIdeal.mem_smul_pi_iff I
    (fun hs : PLift s.Nonempty => Sections I z hz s hs.down m) _).mpr
  intro hs
  change inclusion I z hz s hs.down m (x hs) ∈ _
  rw [←inclusion_range I z hz s hs.down m hgen]
  exact LinearMap.mem_range_self _ _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichNaturality
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.ReesRoot
open UniversalSplitting ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p14
private local instance baseAlgebra_r959813_1 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) := inferInstance
attribute [local instance] OAI.Lech.ReesRoot.sectionModule_p7
lemma powerSectionBasis_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (e : PowerIndex n) :
    sectionsRestriction I z hz hs ht (fun i => (powerWeight n i:ℤ)) hst
      (powerSectionBasis I z hz s hs e)=powerSectionBasis I z hz t ht e := by
  simp only [powerSectionBasis,Module.Basis.baseChange_apply,sectionsRestriction_tmul,map_one,
    ProjectiveRoot.powerSectionBasis_natural]

lemma powerSectionCoordinates_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (x : Sections I z hz s hs (fun i => (powerWeight n i:ℤ))) :
    (powerSectionBasis I z hz t ht).equivFun
      (sectionsRestriction I z hz hs ht (fun i => (powerWeight n i:ℤ)) hst x)=
        fun e => restriction I z hz hst ((powerSectionBasis I z hz s hs).equivFun x e) :=
  basis_coordinates_semilinear (A := Ring I z hz s) (B := Ring I z hz t)
    (M := Sections I z hz s hs (fun i => (powerWeight n i:ℤ)))
    (N := Sections I z hz t ht (fun i => (powerWeight n i:ℤ)))
    (powerSectionBasis I z hz s hs) (powerSectionBasis I z hz t ht)
    (restriction I z hz hst) (sectionsRestrictionRing I z hz hs ht _ hst)
    (powerSectionBasis_natural I z hz hs ht hst) x
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesUlrichCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits UniversalSplitting
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p13
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p13
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p11
lemma ulrichCechEquiv_natural {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (x : cechObj I z hz (fun i => (powerWeight n i:ℤ)) s) :
    ulrichCechEquiv I z hz t ((cechRes I z hz _ hst).hom x)=
      ((powerScalarDiagram I z hz).res hst).hom (ulrichCechEquiv I z hz s x) := by
  classical
  funext e ht
  by_cases hs : s.Nonempty
  · change (powerSectionBasis I z hz t ht.down).equivFun ((cechRes I z hz _ hst).hom x ht) e=
      (scalarCechRes I z hz hst).hom (fun hs => (powerSectionBasis I z hz s hs.down).equivFun (x hs) e) ht
    rw [scalarCechRes_apply I z hz hst hs ht.down,cechRes_apply I z hz _ hst hs ht.down,
      powerSectionCoordinates_natural]
  · change (powerSectionBasis I z hz t ht.down).equivFun
      (if hs : s.Nonempty then _ else 0) e=if hs : s.Nonempty then _ else 0
    rw [dite_eq_right hs]
    simp only [map_zero,Pi.zero_apply,dite_eq_right hs]

def ulrichCechIso :
    FiniteModuleCech.positiveComplex (cechDiagram I z hz (fun i => (powerWeight n i:ℤ))) ≅
      FiniteModuleCech.positiveComplex (powerScalarDiagram I z hz) :=
  FiniteModuleCech.positiveIso (ulrichCechEquiv I z hz) (fun _ => ulrichCechEquiv_natural I z hz _)
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootPermutation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.cechInclusionIter_mono _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits ProductSourceCover
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup


attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p12
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p12
attribute [local instance] OAI.Lech.ReesRoot.sectionChartModule_p6
def permuteSections (σ : Equiv.Perm (Fin n)) (s : Finset (Fin (n+1)))
    (hs : s.Nonempty) (m : Fin n → ℤ) :
    Sections I z hz s hs m ≃ₗ[Ring I z hz s] Sections I z hz s hs (permuteWeight n σ m) :=
  LinearEquiv.baseChange (ProjectiveRoot.Ring R n s) (Ring I z hz s) _ _
    (ProjectiveRoot.permuteSections R n σ s hs m)

lemma permuteSections_natural (σ : Equiv.Perm (Fin n))
    {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (m : Fin n → ℤ) (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz hs ht (permuteWeight n σ m) hst (permuteSections I z hz σ s hs m x)=
      permuteSections I z hz σ t ht m (sectionsRestriction I z hz hs ht m hst x) := by
  induction x using OAI.tensorInductionOn with
  | tmul a x =>
      change sectionsRestriction I z hz hs ht _ hst
        (a ⊗ₜ[ProjectiveRoot.Ring R n s] ProjectiveRoot.permuteSections R n σ s hs m x)=_
      rw [sectionsRestriction_tmul,ProjectiveRoot.permuteSections_natural,sectionsRestriction_tmul]
      rfl
  | add x y hx hy => simp only [map_add,hx,hy]

attribute [local instance] OAI.Lech.ReesRoot.baseModule_p10
attribute [local instance] OAI.Lech.ReesRoot.projectiveModule_p9
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p9
attribute [local instance] OAI.Lech.ReesRoot.sectionModule_p5
def permuteCechEquiv (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ) (s : Finset (Fin (n+1))) :
    cechObj I z hz m s ≃ₗ[R] cechObj I z hz (permuteWeight n σ m) s where
  toFun x hs := permuteSections I z hz σ s hs.down m (x hs)
  invFun x hs := (permuteSections I z hz σ s hs.down m).symm (x hs)
  left_inv x := by funext hs; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := by funext hs; exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by funext hs; exact map_add _ _ _
  map_smul' r x := by
    funext hs
    exact map_smul ((permuteSections I z hz σ s hs.down m).restrictScalars R) r (x hs)

lemma permuteCechEquiv_natural (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ)
    {s t : Finset (Fin (n+1))} (hst : s ⊆ t) (x : cechObj I z hz m s) :
    permuteCechEquiv I z hz σ m t ((cechRes I z hz m hst).hom x)=
      (cechRes I z hz (permuteWeight n σ m) hst).hom (permuteCechEquiv I z hz σ m s x) := by
  funext ht
  by_cases hs : s.Nonempty
  · change permuteSections I z hz σ t ht.down m ((cechRes I z hz m hst).hom x ht)=
      (cechRes I z hz _ hst).hom (fun hs => permuteSections I z hz σ s hs.down m (x hs)) ht
    rw [cechRes_apply I z hz m hst hs ht.down,cechRes_apply I z hz _ hst hs ht.down,
      permuteSections_natural]
  · change permuteSections I z hz σ t ht.down m (if hs : s.Nonempty then _ else 0)=
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,map_zero]

 

def permuteCechIso (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ) :
    cech I z hz m ≅ cech I z hz (permuteWeight n σ m) :=
  FiniteModuleCech.positiveIso (permuteCechEquiv I z hz σ m)
    (fun _ => permuteCechEquiv_natural I z hz σ m _)
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootPowerPath
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ) (hgen : Ideal.span (Set.range z)=I)

abbrev enlargedPath (a N : ℕ) :=
  TotalGhost.towerPath (X:=fun N => enlargedAt I z hz F h s hd (twistSequence m a N))
    (enlargedStep I z hz F h s hd m a) N

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootThickeningEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)

variable (hgen : Ideal.span (Set.range z)=I)
def thickeningShortComplex (N : ℕ) :=
  CartierQuotient.shortComplex I (cechInclusionZ I z hz m 1)
    (fun q => by simpa only [pow_one] using cechInclusionZ_range I z hz m hgen 1 q) N

end Lech.ReesRoot

end

end OAI
end


