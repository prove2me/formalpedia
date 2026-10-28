-- Prove2me | Definitions.Def_OAIQ032L018
-- name    : OAIQ032L018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:53:36.403248+00:00
-- url     : https://prove2.me/theorems/709dc5e6-58f4-45e3-a44e-8ec68e056d6a
-- title:
--   Definitions bundle OAIQ032L018 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 15 definitions, 3 instances and 3 theorems. The definitions and types are `OAI.Lech.TwistedLocalization.gradedKernelEquiv`, `OAI.Lech.baseChangeHomEquiv`, `OAI.Lech.baseChange_nullhomotopy`, `OAI.Lech.cyclicDuttaContribution`, `OAI.Lech.cyclicDuttaSequence`, `OAI.Lech.extendScalars_nullhomotopy`, `OAI.Lech.flatExtensionHomologyIso`, `OAI.Lech.frobeniusBaseChangeIso`, `OAI.Lech.frobeniusComplexAddIso`, `OAI.Lech.frobenius_nullhomotopy`, `OAI.Lech.ordinaryLength`, `OAI.Lech.scalarExtensionZeroHomologyIso`, `OAI.Lech.tensorModuleFunctor`, `OAI.Lech.tensorModuleUnitIso`, `OAI.Lech.tensorScalarExtensionIso`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ComplexTensorComparison`, `Multiplicity_CyclicDutta`, `Multiplicity_DuttaBaseChange`, `Multiplicity_DuttaFrobeniusShift`, `Multiplicity_FrobeniusComplexStage`, `Multiplicity_IdealGradedLengthPiece`, `Multiplicity_KoszulTensorSingle`, `Multiplicity_ScalarExtensionComplexCompare`, `Multiplicity_ScalarExtensionDepth`, `Multiplicity_ScalarExtensionHomotopy`, `Multiplicity_TensorTotalHomologyProperty`, `Multiplicity_TorsionThickening`, `Multiplicity_TotalGhostRowHom`, `Multiplicity_ZeroHomologyScalarExtension`.
--
--   **Imports.** It imports the published bundle `Def_DuttaDomain`; the bundles `OAIQ032L000`, `OAIQ032L003`, `OAIQ032L004`, `OAIQ032L005`, `OAIQ032L008` and `OAIQ032L009` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Lech.PrimeFiltration.Factors.euler_self`, `OAI.Lech.cyclicDuttaSequence_small` and `OAI.Lech.cyclicDuttaSequence_tendsto`; the proofs of `OAI.Lech.CharP.dutta_limit_from_perfection`, `OAI.Lech.CharP.dutta_minimal_estimate`, `OAI.Lech.CharP.perfection_complex_value`, `OAI.Lech.FilteredCech.positive_homology_powerTorsion`, `OAI.Lech.Koszul.length_quotient_tensor_le_sum`, `OAI.Lech.PerfectDomainStages.normalizedLength_stage_homology`, `OAI.Lech.PerfectDomainStages.normalizedLength_stage_scalar_quotient_homology`, `OAI.Lech.PowerSeries.maximal_power_colength`, `OAI.Lech.PrimeFiltration.Factors.euler_self`, `OAI.Lech.ReesRoot.scalarHomology_value`, `OAI.Lech.ReesRoot.uniform_unit_nilpotence`, `OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology`, `OAI.Lech.SourceGraded.acyclicity_finite_torsion`, `OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage`, `OAI.Lech.SourceGraded.finiteThickening_homology_zeroClass`, `OAI.Lech.cyclicDuttaSequence_small`, `OAI.Lech.cyclicDuttaSequence_tendsto`, `OAI.Lech.dutta_algClosed`, `OAI.Lech.dutta_domain`, `OAI.Lech.exists_scalar_extension_homology_bound`, `OAI.Lech.finiteHomology_extendScalars`, `OAI.Lech.frobenius_quotient_homology_bound`, `OAI.Lech.frobenius_quotient_homology_finiteLength`, `OAI.Lech.frobenius_shortComplex_homology_finiteLength`, `OAI.Lech.ordinaryPower_stableImage_isoMod` and `OAI.Lech.short_rank_euler_zero`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L003
import Definitions.Def_OAIQ032L004
import Definitions.Def_OAIQ032L005
import Definitions.Def_OAIQ032L008
import Definitions.Def_OAIQ032L009

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorTotalHomologyProperty
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech
universe u v
variable {R : Type u} [CommRing R]


instance complexQuotient_additive (I : Ideal R) {ι : Type*} (c : ComplexShape ι) :
    (complexQuotient I c : HomologicalComplex (ModuleCat.{v} R) c ⥤ _).Additive :=
  inferInstanceAs ((moduleQuotient I).mapHomologicalComplex c).Additive

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalGhostRowHom
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]


noncomputable def baseChangeHomEquiv (M N : ModuleCat.{u} R) :
    (S ⊗[R] M →ₗ[S] S ⊗[R] N) ≃ₗ[R]
      ((baseChangeFunctor R S).obj M ⟶ (baseChangeFunctor R S).obj N) where
  toFun f := ModuleCat.ofHom f
  invFun f := f.hom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (IsScalarTower.algebraMap_smul S r (f x)).symm

instance baseChangeFunctor_linear : (baseChangeFunctor R S).Linear R where
  map_smul {M N} f r := by
    change baseChangeHomEquiv R S M N ((r • f.hom).baseChange S) = _
    rw [LinearMap.baseChange_smul, map_smul]
    rfl

end Lech

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulTensorSingle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

open scoped BigOperators


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open Koszul
universe u v
variable {R : Type u} [CommRing R]

lemma entryIdeal_power_antitone (zs : List R) {a b : ℕ} (h : a ≤ b) :
    entryIdeal (zs.map (· ^ b)) ≤ entryIdeal (zs.map (· ^ a)) := by
  apply Ideal.span_le.mpr
  intro x hx
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
  have he : r^b = r^(b-a) * r^a := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [he]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (List.mem_map.mpr ⟨r,hr,rfl⟩))


end Lech


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
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

open CategoryTheory

namespace Lech
universe u
variable {R : Type u} [CommRing R]
noncomputable def ordinaryLength (I : Ideal R) : TorsionLength I where
  value M := (Module.length R M).toENNReal
  zero h := by
    have := ModuleCat.isZero_iff_subsingleton.mp h
    simp
  additive {S} h _ := by
    rw [Module.length_eq_add_of_exact S.f.hom S.g.hom
      h.moduleCat_injective_f h.moduleCat_surjective_g
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact),
      ENat.toENNReal_add]
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarExtensionHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped TensorProduct ChangeOfRings
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma extendScalars_complex_smul (φ : R →+* S)
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (f : F ⟶ G) (x : R) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map (x • f) =
      φ x • ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map f := by
  ext i : 1
  exact extendScalars_map_smul φ (f.f i) x

def extendScalars_nullhomotopy (φ : R →+* S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (x : R)
    (H : Homotopy (x • 𝟙 F) 0) :
    Homotopy (φ x • 𝟙 (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F)) 0 := by
  have H' := (ModuleCat.extendScalars φ).mapHomotopy H
  rw [extendScalars_complex_smul,CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_zero] at H'
  exact H' 

def frobenius_nullhomotopy (p : ℕ) [Fact p.Prime] [CharP R p]
    (n a : ℕ) (F : CochainComplex (ModuleCat.{u} R) ℤ) (x : R)
    (H : Homotopy (x^a • 𝟙 F) 0) :
    Homotopy (x^(a*(p^n)) • 𝟙 (frobeniusComplex R p n F)) 0 := by
  simp only [frobeniusComplex]
  have h := extendScalars_nullhomotopy (iterateFrobenius R p n) F (x^a) H
  have he : iterateFrobenius R p n (x^a) = x^(a*(p^n)) := by
    rw [iterateFrobenius_def, pow_mul]
  rw [he] at h
  exact h
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusComplexStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal

namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def flatExtensionHomologyIso (f : R →+* S) (hf : f.Flat)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj F).homology i ≅
      (ModuleCat.extendScalars f).obj (F.homology i) := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (F.sc i).mapHomologyIso (ModuleCat.extendScalars f)
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ComplexTensorComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R]

def tensorModuleFunctor (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj M := (TensorTotal.termTensor M).obj F
  map f := TensorTotal.termTensorMap F _ f
  map_id M := by
    ext i : 1
    exact whiskerLeft_id (F.X i) M
  map_comp f g := TensorTotal.termTensorMap_comp F f g

instance tensorModuleFunctor_additive (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorModuleFunctor F).Additive where
  map_add := by
    intros M N f g
    ext i : 1
    exact Functor.map_add ((curriedTensor (ModuleCat R)).obj (F.X i))

def tensorModuleUnitIso (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorModuleFunctor F).obj (ModuleCat.of R R) ≅ F :=
  Hom.isoOfComponents (fun i => (TensorProduct.rid R (F.X i)).toModuleIso) (by
    intro i j _
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x
    change F.d i j ((1:R) • x) = (1:R) • F.d i j x
    exact map_smul _ _ _)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ZeroHomologyScalarExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def scalarExtensionZeroHomologyIso (φ : R →+* S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hzero : F.d 0 1 = 0) :
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F).homology 0 ≅
      (ModuleCat.extendScalars φ).obj (F.homology 0) := by
  let E := ModuleCat.extendScalars φ
  let G := (E.mapHomologicalComplex (.up ℤ)).obj F
  have hz : G.d 0 1 = 0 := by
    change E.map (F.d 0 1) = 0
    rw [hzero,CategoryTheory.Functor.map_zero]
  exact zeroHomologyCokernelIso G hz ≪≫ (PreservesCokernel.iso E (F.d (-1) 0)).symm ≪≫
    E.mapIso (zeroHomologyCokernelIso F hzero).symm

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarExtensionComplexCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

def tensorScalarExtensionIso (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorModuleFunctor F).obj (ModuleCat.of R S) ≅
      ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
        (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F) :=
  Hom.isoOfComponents (fun i => tensorScalarExtensionObjIso (F.X i)) (by
    intro i j _
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaFrobeniusShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p]

def frobeniusComplexAddIso (F : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℕ) :
    frobeniusComplex R p m (frobeniusComplex R p n F) ≅ frobeniusComplex R p (n+m) F := by
  have he : (iterateFrobenius R p m).comp (iterateFrobenius R p n) =
      iterateFrobenius R p (n+m) := by
    ext x
    change (x^(p^n))^(p^m) = x^(p^(n+m))
    rw [← pow_mul,← pow_add]
  have e := ((NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp (iterateFrobenius R p n) (iterateFrobenius R p m))
      (.up ℤ)).app F).symm
  rw [he] at e
  exact e

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaBaseChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex IsLocalRing
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def frobeniusBaseChangeIso (p : ℕ) [Fact p.Prime] [CharP R p] [CharP S p]
    (φ : R →+* S) (F : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
      (frobeniusComplex R p n F)) ≅
      frobeniusComplex S p n (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F) := by
  have he : φ.comp (iterateFrobenius R p n)=(iterateFrobenius S p n).comp φ := by
    ext x
    change φ (x^(p^n))=(φ x)^(p^n)
    exact map_pow φ x _
  have e := ((NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp (iterateFrobenius R p n) φ) (.up ℤ)).app F).symm
  rw [he] at e
  exact e ≪≫ (NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp φ (iterateFrobenius S p n)) (.up ℤ)).app F

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionThickening
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TwistedLocalization
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)

variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A),g (r • a)=r • g a)
  (I : Ideal R) (ell : TorsionLength I)
def gradedKernelEquiv (n : ℕ) :
    (gradedMap G H g hg n).ker ≃ₗ[R] (Homogeneous.gradedMap G H g hg n).ker where
  toFun x := ⟨x.val,by exact x.property⟩
  invFun x := ⟨x.val,by exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

attribute [local instance] kernelAdd kernelModule
attribute [local irreducible] pieceMap gradedMap kernelFraction
end Lech.TwistedLocalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarExtensionDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma baseChange_map_smul [Algebra R S] {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (x : R) :
    (baseChangeFunctor R S).map (x • f) =
      algebraMap R S x • (baseChangeFunctor R S).map f := by
  apply ModuleCat.hom_ext
  change (x • f.hom).baseChange S = algebraMap R S x • f.hom.baseChange S
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext
  ext s m
  change s ⊗ₜ[R] (x • f m) = algebraMap R S x • (s ⊗ₜ[R] f m)
  rw [TensorProduct.tmul_smul,TensorProduct.smul_tmul',Algebra.smul_def]
  rfl

def baseChange_nullhomotopy [Algebra R S]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (x : R)
    (H : Homotopy (x • 𝟙 F) 0) :
    Homotopy (algebraMap R S x • 𝟙 (((baseChangeFunctor R S).mapHomologicalComplex _).obj F)) 0 := by
  have H' := (baseChangeFunctor R S).mapHomotopy H
  have he : ((baseChangeFunctor R S).mapHomologicalComplex (.up ℤ)).map (x • 𝟙 F) =
      algebraMap R S x • 𝟙 (((baseChangeFunctor R S).mapHomologicalComplex _).obj F) := by
    ext i : 1
    change (baseChangeFunctor R S).map (x • 𝟙 (F.X i)) =
      algebraMap R S x • 𝟙 ((baseChangeFunctor R S).obj (F.X i))
    rw [baseChange_map_smul,CategoryTheory.Functor.map_id]
  rw [he,Functor.map_zero] at H'
  exact H'

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CyclicDutta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
attribute [local instance] quotient_local quotient_localHom

def cyclicDuttaSequence (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (P : Ideal R) (n : ℕ) : ℝ :=
  (p:ℝ)^(-(n*dimension R:ℤ)) *
    shortEuler R ((tensorModuleFunctor (frobeniusComplex R p n F)).obj (ModuleCat.of R (R ⧸ P)))

attribute [local instance] OAI.Lech.duttaQuotientCharP
def cyclicDuttaContribution (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (P : Ideal R) : ℝ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    if dimension (R ⧸ P)=dimension R then
      duttaMultiplicity (R ⧸ P) p
        (((ModuleCat.extendScalars (Ideal.Quotient.mk P)).mapHomologicalComplex (.up ℤ)).obj F)
    else 0
  else 0

end Lech

end

end OAI
end


