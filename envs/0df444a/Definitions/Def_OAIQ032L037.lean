-- Prove2me | Definitions.Def_OAIQ032L037
-- name    : OAIQ032L037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:20:02.829755+00:00
-- url     : https://prove2.me/theorems/7c3e4afa-70ed-4df2-bd17-78dde024a529
-- title:
--   Definitions bundle OAIQ032L037 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 16 definitions, 1 instance and 22 theorems. The definitions and types are `OAI.Lech.ProjectiveRoot.permuteSections`, `OAI.Lech.ProjectiveRoot.reducedHomologyEquiv`, `OAI.Lech.ProjectiveRoot.reducedHomologyIso`, `OAI.Lech.ReesRoot.cechInclusionApp`, `OAI.Lech.ReesRoot.cechInclusionDiagram`, `OAI.Lech.ReesRoot.cechInclusionIter`, `OAI.Lech.ReesRoot.cechInclusionIterApp`, `OAI.Lech.ReesRoot.cechInclusionIterDiagram`, `OAI.Lech.ReesRoot.cechInclusionZ`, `OAI.Lech.ReesRoot.downEquiv`, `OAI.Lech.ReesRoot.downIter`, `OAI.Lech.ReesRoot.inclusion`, `OAI.Lech.ReesRoot.inclusionIter`, `OAI.Lech.ReesRoot.intersectionTensorHomotopy`, `OAI.Lech.ReesRoot.localInclusion`, `OAI.Lech.ReesRoot.thickeningZ`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_CechCartierRange`, `Multiplicity_CechCartierZRange`, `Multiplicity_ReducedRootCohomology`, `Multiplicity_ReesRootInclusion`, `Multiplicity_ReesRootIteration`, `Multiplicity_ReesRootLayers`, `Multiplicity_ReesRootNilpotence`, `Multiplicity_ReesRootThickeningEuler`, `Multiplicity_RootChartUlrich`, `Multiplicity_RootPermutation`, `Multiplicity_RootUlrichNaturality`.
--
--   **Imports.** It imports the bundles `OAIQ032L034` and `OAIQ032L035` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ032L039`; the statements `OAI.Lech.ReesRoot.thickeningZ_euler` and `OAI.Lech.ReesRoot.thickeningZ_finite`; the proofs of `OAI.Lech.ReesRoot.ambientStrip_euler`, `OAI.Lech.ReesRoot.exceptionalZ_finite`, `OAI.Lech.ReesRoot.quotientAtTotal_euler` and `OAI.Lech.ReesRoot.quotientAtTotal_finite`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L034
import Definitions.Def_OAIQ032L035

set_option maxHeartbeats 1000000

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open ProductSourceCover
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

variable (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ)

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p7
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p7
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p5
attribute [local instance] OAI.Lech.ReesRoot.projectiveModule_p4
attribute [local instance] OAI.Lech.ReesRoot.sectionChartModule_p1
attribute [local instance] OAI.Lech.ReesRoot.sectionBaseModule_p1
def downEquiv (k : Fin (n+1)) (hk : k ∈ s) :
    Sections I z hz s hs (fun i => m i+1) ≃ₗ[Ring I z hz s] Sections I z hz s hs m :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Ring I z hz s) _)
    (ProjectiveRoot.downEquiv R n s hs m k hk)

 

def localInclusion (k : Fin (n+1)) (hk : k ∈ s) :
    Sections I z hz s hs (fun i => m i+1) →ₗ[Ring I z hz s] Sections I z hz s hs m :=
  (algebraMap R (Ring I z hz s) (z k)) • (downEquiv I z hz s hs m k hk).toLinearMap

lemma localInclusion_tmul (k : Fin (n+1)) (hk : k ∈ s)
    (b : Ring I z hz s) (x : ProjectiveRoot.Sections R n s hs (fun i => m i+1)) :
    localInclusion I z hz s hs m k hk (b ⊗ₜ x) =
      (algebraMap R (Ring I z hz s) (z k)*b) ⊗ₜ ProjectiveRoot.downEquiv R n s hs m k hk x := by
  change (algebraMap R (Ring I z hz s) (z k)) • (b ⊗ₜ[ProjectiveRoot.Ring R n s] ProjectiveRoot.downEquiv R n s hs m k hk x) = _
  rw [TensorProduct.smul_tmul']
  rfl

 

lemma localInclusion_independent (k j : Fin (n+1)) (hk : k ∈ s) (hj : j ∈ s)
    (x : Sections I z hz s hs (fun i => m i+1)) :
    localInclusion I z hz s hs m k hk x = localInclusion I z hz s hs m j hj x := by
  induction x using OAI.tensorInductionOn with
  | tmul b x =>
      rw [localInclusion_tmul,localInclusion_tmul,ProjectiveRoot.downEquiv_change R n s hs m k j hk hj,
        ←TensorProduct.smul_tmul (R := ProjectiveRoot.Ring R n s)
          (ProjectiveRoot.ratio R n s k j hk)
          (algebraMap R (Ring I z hz s) (z k)*b)
          (ProjectiveRoot.downEquiv R n s hs m j hj x)]
      congr 1
      change map I z hz s (ProjectiveRoot.ratio R n s k j hk) *
        (algebraMap R (Ring I z hz s) (z k)*b) = algebraMap R (Ring I z hz s) (z j)*b
      rw [←mul_assoc,mul_comm _ (algebraMap R (Ring I z hz s) (z k)),ratio_relation]
  | add x y hx hy => simp only [map_add,hx,hy]

lemma localInclusion_restriction {t : Finset (Fin (n+1))} (ht : t.Nonempty) (hst : s ⊆ t)
    (k : Fin (n+1)) (hk : k ∈ s) (x : Sections I z hz s hs (fun i => m i+1)) :
    sectionsRestriction I z hz hs ht m hst (localInclusion I z hz s hs m k hk x) =
      localInclusion I z hz t ht m k (hst hk) (sectionsRestriction I z hz hs ht _ hst x) := by
  induction x using OAI.tensorInductionOn with
  | tmul b x =>
      rw [localInclusion_tmul,sectionsRestriction_tmul,sectionsRestriction_tmul,localInclusion_tmul,
        map_mul,ProjectiveRoot.downEquiv_restriction]
      congr 2
      exact (restrictionAlg I z hz hst).commutes (z k)
  | add x y hx hy => simp only [map_add,hx,hy]

 

attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p4
def inclusion : Sections I z hz s hs (fun i => m i+1) →ₗ[R] Sections I z hz s hs m :=
  (localInclusion I z hz s hs m hs.choose hs.choose_spec).restrictScalars R

lemma inclusion_eq (k : Fin (n+1)) (hk : k ∈ s) (x : Sections I z hz s hs (fun i => m i+1)) :
    inclusion I z hz s hs m x = localInclusion I z hz s hs m k hk x :=
  localInclusion_independent I z hz s hs m hs.choose k hs.choose_spec hk x

lemma inclusion_restriction {t : Finset (Fin (n+1))} (ht : t.Nonempty) (hst : s ⊆ t)
    (x : Sections I z hz s hs (fun i => m i+1)) :
    sectionsRestriction I z hz hs ht m hst (inclusion I z hz s hs m x) =
      inclusion I z hz t ht m (sectionsRestriction I z hz hs ht _ hst x) := by
  rw [inclusion_eq I z hz s hs m hs.choose hs.choose_spec,
    inclusion_eq I z hz t ht m hs.choose (hst hs.choose_spec)]
  exact localInclusion_restriction I z hz s hs m ht hst hs.choose hs.choose_spec x

 

private local instance sectionGroup_r0922db_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
lemma localInclusion_injective (k : Fin (n+1)) (hk : k ∈ s) :
    Function.Injective (localInclusion I z hz s hs m k hk) := by
  let : Module.Projective (Ring I z hz s) (Sections I z hz s hs m) :=
    (sections_properties I z hz hs m).2.1
  let : Module.Flat (Ring I z hz s) (Sections I z hz s hs m) := Module.Flat.of_projective
  have hr : IsRegular (algebraMap R (Ring I z hz s) (z k)) := by
    apply (Commute.isRegular_iff (fun b => mul_comm _ b)).2
    simpa only [IsLeftRegular, Algebra.smul_def] using coordinate_smul_injective I z hz s k hk
  have hinj := Module.Flat.isSMulRegular_of_isRegular (M := Sections I z hz s hs m) hr
  exact hinj.comp (downEquiv I z hz s hs m k hk).injective

lemma inclusion_injective : Function.Injective (inclusion I z hz s hs m) :=
  localInclusion_injective I z hz s hs m hs.choose hs.choose_spec

open CategoryTheory CategoryTheory.Limits
 
def cechInclusionApp (s : Finset (Fin (n+1))) :
    cechObj I z hz (fun i => m i+1) s ⟶ cechObj I z hz m s :=
  ModuleCat.ofHom {
    toFun x hs := inclusion I z hz s hs.down m (x hs)
    map_add' x y := by funext hs; exact map_add _ _ _
    map_smul' r x := by funext hs; exact map_smul (inclusion I z hz s hs.down m) r (x hs) }

lemma cechInclusion_natural {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    cechRes I z hz (fun i => m i+1) hst ≫ cechInclusionApp I z hz m t =
      cechInclusionApp I z hz m s ≫ cechRes I z hz m hst := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext ht
  by_cases hs : s.Nonempty
  · change inclusion I z hz t ht.down m
      ((cechRes I z hz (fun i => m i+1) hst).hom x ht) =
        (cechRes I z hz m hst).hom ((cechInclusionApp I z hz m s).hom x) ht
    rw [cechRes_apply I z hz (fun i => m i+1) hst hs ht.down,
      cechRes_apply I z hz m hst hs ht.down]
    exact (inclusion_restriction I z hz s hs m ht.down hst (x ⟨hs⟩)).symm
  · change inclusion I z hz t ht.down m (if hs : s.Nonempty then _ else 0) =
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,map_zero]

 
def cechInclusionDiagram : FiniteModuleCech.Map
    (cechDiagram I z hz (fun i => m i+1)) (cechDiagram I z hz m) where
  app := cechInclusionApp I z hz m
  naturality := cechInclusion_natural I z hz m


end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayers
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

variable (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ)

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p10
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p10
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p8
private local instance projectiveModule_r0922db_1 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p7
attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p9
attribute [local instance] OAI.Lech.ReesRoot.sectionChartModule_p4
attribute [local instance] OAI.Lech.ReesRoot.sectionBaseModule_p4
lemma inclusion_range (hgen : Ideal.span (Set.range z)=I) :
    (inclusion I z hz s hs m).range = I • (⊤ : Submodule R (Sections I z hz s hs m)) := by
  classical
  let k := hs.choose
  have hk : k ∈ s := hs.choose_spec
  rw [LocalPrincipal.smul_top_eq_range I z hgen k
    (fun j => map I z hz s (ProjectiveRoot.ratio R n s k j hk)) (ratio_relation I z hz s k · hk)]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨downEquiv I z hz s hs m k hk y,?_⟩
    rw [inclusion_eq I z hz s hs m k hk]
    change z k • (downEquiv I z hz s hs m k hk) y =
      algebraMap R (Ring I z hz s) (z k) • (downEquiv I z hz s hs m k hk) y
    exact (IsScalarTower.algebraMap_smul (Ring I z hz s) (z k) _).symm
  · rintro ⟨y,rfl⟩
    refine ⟨(downEquiv I z hz s hs m k hk).symm y,?_⟩
    rw [inclusion_eq I z hz s hs m k hk]
    change algebraMap R (Ring I z hz s) (z k) •
      (downEquiv I z hz s hs m k hk) ((downEquiv I z hz s hs m k hk).symm y) = z k • y
    rw [LinearEquiv.apply_symm_apply,IsScalarTower.algebraMap_smul]



def inclusionIter (m : Fin n → ℤ) (N : ℕ) :
    Sections I z hz s hs (raise m N) →ₗ[R] Sections I z hz s hs m :=
  match N with
  | 0 => LinearMap.id
  | N+1 => (inclusion I z hz s hs m).comp (inclusionIter (fun i => m i+1) N)

lemma inclusionIter_injective (N : ℕ) :
    Function.Injective (inclusionIter I z hz s hs m N) := by
  induction N generalizing m with
  | zero => exact Function.injective_id
  | succ N ih => exact (inclusion_injective I z hz s hs m).comp (ih _)

 

lemma inclusionIter_range (hgen : Ideal.span (Set.range z)=I) (N : ℕ) :
    (inclusionIter I z hz s hs m N).range = I^N • (⊤ : Submodule R (Sections I z hz s hs m)) := by
  induction N generalizing m with
  | zero =>
      change (LinearMap.id : Sections I z hz s hs m →ₗ[R] Sections I z hz s hs m).range = _
      simp only [LinearMap.range_id,pow_zero,Ideal.one_eq_top,Submodule.top_smul]
  | succ N ih =>
      change ((inclusion I z hz s hs m).comp
        (inclusionIter I z hz s hs (fun i => m i+1) N)).range = _
      rw [LinearMap.range_comp,ih,Submodule.map_smul'',Submodule.map_top,
        inclusion_range I z hz s hs m hgen,
        ←Submodule.mul_smul,pow_succ]

lemma inclusionIter_restriction {t : Finset (Fin (n+1))} (ht : t.Nonempty) (hst : s ⊆ t)
    (N : ℕ) (x : Sections I z hz s hs (raise m N)) :
    sectionsRestriction I z hz hs ht m hst (inclusionIter I z hz s hs m N x) =
      inclusionIter I z hz t ht m N (sectionsRestriction I z hz hs ht (raise m N) hst x) := by
  induction N generalizing m with
  | zero => rfl
  | succ N ih =>
      change Sections I z hz s hs (raise (fun i => m i+1) N) at x
      change sectionsRestriction I z hz hs ht m hst
        (inclusion I z hz s hs m (inclusionIter I z hz s hs (fun i => m i+1) N x)) = _
      refine (inclusion_restriction I z hz s hs m ht hst _).trans ?_
      exact congrArg (inclusion I z hz t ht m) (ih (fun i => m i+1) x)



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootIteration
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

variable (t : Finset (Fin (n+1))) (ht : t.Nonempty) (k : Fin (n+1)) (hk : k ∈ t)

 
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p8
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p8
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p6
private local instance projectiveModule_r0922db_2 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
attribute [local instance] OAI.Lech.ReesRoot.sectionChartModule_p2
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p5
private local instance sectionBaseModule_r0922db_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule
def downIter (m : Fin n → ℤ) (N : ℕ) :
    Sections I z hz t ht (raise m N) ≃ₗ[Ring I z hz t] Sections I z hz t ht m :=
  match N with
  | 0 => LinearEquiv.refl _ _
  | N+1 => (downIter (fun j => m j+1) N).trans (downEquiv I z hz t ht m k hk)

attribute [local instance] OAI.Lech.ReesRoot.sectionTower_p0
lemma inclusionIter_coordinate (m : Fin n → ℤ) (N : ℕ)
    (x : Sections I z hz t ht (raise m N)) :
    inclusionIter I z hz t ht m N x = z k^N • downIter I z hz t ht k hk m N x := by
  induction N generalizing m with
  | zero => simp only [inclusionIter,downIter,pow_zero,one_smul]; rfl
  | succ N ih =>
      change Sections I z hz t ht (raise (fun j => m j+1) N) at x
      change inclusion I z hz t ht m (inclusionIter I z hz t ht (fun j => m j+1) N x) = _
      rw [inclusion_eq I z hz t ht m k hk,ih]
      change algebraMap R (Ring I z hz t) (z k) •
        downEquiv I z hz t ht m k hk (z k^N • downIter I z hz t ht k hk (fun j => m j+1) N x) = _
      rw [IsScalarTower.algebraMap_smul]
      rw [←IsScalarTower.algebraMap_smul (Ring I z hz t) (z k^N),map_smul,
        IsScalarTower.algebraMap_smul,smul_smul,pow_succ']
      rfl

open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable (m : Fin n → ℤ)

 

private local instance sectionGroup_r0922db_2 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
def cechInclusionIterApp (N : ℕ) (s : Finset (Fin (n+1))) :
    cechObj I z hz (raise m N) s ⟶ cechObj I z hz m s :=
  ModuleCat.ofHom {
    toFun x hs := inclusionIter I z hz s hs.down m N (x hs)
    map_add' x y := by funext hs; exact map_add _ _ _
    map_smul' r x := by funext hs; exact map_smul (inclusionIter I z hz s hs.down m N) r (x hs) }

lemma cechInclusionIter_natural (N : ℕ) {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    cechRes I z hz (raise m N) hst ≫ cechInclusionIterApp I z hz m N t =
      cechInclusionIterApp I z hz m N s ≫ cechRes I z hz m hst := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext ht
  by_cases hs : s.Nonempty
  · change inclusionIter I z hz t ht.down m N
      ((cechRes I z hz (raise m N) hst).hom x ht) =
        (cechRes I z hz m hst).hom ((cechInclusionIterApp I z hz m N s).hom x) ht
    rw [cechRes_apply I z hz (raise m N) hst hs ht.down,
      cechRes_apply I z hz m hst hs ht.down]
    exact (inclusionIter_restriction I z hz s hs m ht.down hst N (x ⟨hs⟩)).symm
  · change inclusionIter I z hz t ht.down m N (if hs : s.Nonempty then _ else 0) =
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,map_zero]

def cechInclusionIterDiagram (N : ℕ) : FiniteModuleCech.Map
    (cechDiagram I z hz (raise m N)) (cechDiagram I z hz m) where
  app := cechInclusionIterApp I z hz m N
  naturality := cechInclusionIter_natural I z hz m N

 
def cechInclusionIter (N : ℕ) : cech I z hz (raise m N) ⟶ cech I z hz m :=
  (cechInclusionIterDiagram I z hz m N).positiveComplex

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCartierRange
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p0
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p0
attribute [local instance] OAI.Lech.ReesRoot.projectiveModule_p0
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p0
attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p0
attribute [local instance] OAI.Lech.ReesRoot.sectionModule_p0
attribute [local instance] OAI.Lech.ReesRoot.proofFinite
lemma cechInclusionIterApp_range (hgen : Ideal.span (Set.range z)=I)
    (a : ℕ) (t : Finset (Fin (n+1))) :
    (cechInclusionIterApp I z hz m a t).hom.range =
      I^a • (⊤ : Submodule R (cechObj I z hz m t)) :=
  TensorIdeal.piMap_range (I^a)
    (fun ht : PLift t.Nonempty => Sections I z hz t ht.down (raise m a))
    (fun ht : PLift t.Nonempty => Sections I z hz t ht.down m)
    (fun ht => inclusionIter I z hz t ht.down m a)
    (fun ht => inclusionIter_range I z hz t ht.down m hgen a)

attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p0
lemma cechInclusionIter_range (hgen : Ideal.span (Set.range z)=I) (a q : ℕ) :
    ((cechInclusionIter I z hz m a).f q).hom.range =
      I^a • (⊤ : Submodule R ((cech I z hz m).X q)) :=
  TensorIdeal.piMap_range (I^a)
    (fun t : Set.powersetCard (Fin (n+1)) (q+1) => cechObj I z hz (raise m a) t.val)
    (fun t : Set.powersetCard (Fin (n+1)) (q+1) => cechObj I z hz m t.val)
    (fun t => (cechInclusionIterApp I z hz m a t.val).hom)
    (fun t => cechInclusionIterApp_range I z hz m hgen a t.val)

lemma cechInclusionIter_injective (a q : ℕ) :
    Function.Injective ((cechInclusionIter I z hz m a).f q).hom := by
  intro x y hxy
  funext t ht
  exact inclusionIter_injective I z hz t.val ht.down m a (congrFun (congrFun hxy t) ht)

instance cechInclusionIter_mono (a : ℕ) : Mono (cechInclusionIter I z hz m a) :=
  mono_of_mono_f _ (fun q => (ModuleCat.mono_iff_injective _).mpr
    (cechInclusionIter_injective I z hz m a q))
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootNilpotence
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.cechInclusionIter_mono _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p11
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p11
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p9
private local instance projectiveModule_r0922db_3 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p8
attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p10
private local instance sectionChartModule_r0922db_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := TensorProduct.leftModule
attribute [local instance] OAI.Lech.ReesRoot.sectionBaseModule_p5
attribute [local instance] OAI.Lech.ReesRoot.sectionTower_p1
def intersectionTensorHomotopy (t : Finset (Fin (n+1))) (ht : t.Nonempty)
    (m : Fin n → ℤ) :
    Homotopy (termTensorMap F (ModuleCat.of R (Sections I z hz t ht (raise m a)))
      (ModuleCat.ofHom (inclusionIter I z hz t ht m a))) 0 := by
  let k := ht.choose
  have hk : k ∈ t := ht.choose_spec
  apply tensorDivisionHomotopy F (z k^a)
    (ModuleCat.ofHom ((downIter I z hz t ht k hk m a).toLinearMap.restrictScalars R)) _ _ (H k)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (inclusionIter_coordinate I z hz t ht k hk m a x).symm



def cechInclusionZ (m : Fin n → ℤ) (a : ℕ) :
    cechZ I z hz (raise m a) ⟶ cechZ I z hz m :=
  extendMap (cechInclusionIter I z hz m a) ComplexShape.embeddingUpNat

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCartierZRange
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)

lemma cechInclusionZ_square (a q : ℕ) :
    (cechInclusionZ I z hz m a).f (q:ℤ) ≫
        ((cech I z hz m).extendXIso ComplexShape.embeddingUpNat (i:=q) rfl).hom =
      ((cech I z hz (raise m a)).extendXIso ComplexShape.embeddingUpNat (i:=q) rfl).hom ≫
        (cechInclusionIter I z hz m a).f q := by
  let e := (cech I z hz (raise m a)).extendXIso ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)
  let e' := (cech I z hz m).extendXIso ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)
  have he := extendMap_f (cechInclusionIter I z hz m a) ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)
  exact (congrArg (fun f => f ≫ e'.hom) he).trans (by
    change (e.hom ≫ (cechInclusionIter I z hz m a).f q ≫ e'.inv) ≫ e'.hom =
      e.hom ≫ (cechInclusionIter I z hz m a).f q
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

lemma cechInclusionZ_range (hgen : Ideal.span (Set.range z)=I) (a : ℕ) (q : ℤ) :
    ((cechInclusionZ I z hz m a).f q).hom.range =
      I^a • (⊤ : Submodule R ((cechZ I z hz m).X q)) := by
  cases q with
  | ofNat q =>
      exact TensorIdeal.range_of_square (I^a) _ _ _ _ (cechInclusionZ_square I z hz m a q)
        (cechInclusionIter_range I z hz m hgen a q)
  | negSucc q =>
      have hzq := cechZ_negative I z hz m (Int.negSucc q) (by omega)
      have : Subsingleton ((cechZ I z hz m).X (Int.negSucc q)) :=
        ModuleCat.isZero_iff_subsingleton.mp hzq
      exact Subsingleton.elim _ _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReducedRootCohomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (I : Ideal R)

def reducedHomologyIso (q : ℕ) :
    (reducedCech R n m I).homology q ≅
      (coefficientCech R n m (TensorIdeal.quotientFunctor I)).homology (q:ℤ) :=
  ((reducedCech R n m I).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) rfl).symm ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (q:ℤ)).mapIso (integerReductionIso R n m I).symm

def reducedHomologyEquiv :
    (reducedCech R n m I).homology (negativeCount m+1) ≃ₗ[R]
      (Fin (signedRank m) → R ⧸ I) :=
  (reducedHomologyIso R n m I (negativeCount m+1)).toLinearEquiv ≪≫ₗ
    (coefficientHomologySelfIso R n m (TensorIdeal.quotientFunctor I)).toLinearEquiv ≪≫ₗ
      (TensorProduct.tensorQuotEquivQuotSMul
        ((integerCech R n m).homology (negativeCount m+1)) I).symm ≪≫ₗ
        TensorProduct.equivFinsuppOfBasisLeft (integerHomologyBasis R n m) ≪≫ₗ
          Finsupp.linearEquivFunOnFinite R (R ⧸ I) _

end Lech.ProjectiveRoot

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

abbrev thickeningZ (N : ℕ) := CartierQuotient.quotient (I^N) (cechZ I z hz m)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootChartUlrich
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.ProjectiveRoot
open ProductSourceCover UniversalSplitting
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)


lemma powerSectionBasis_val (s : Finset (Fin (n+1))) (hs : s.Nonempty) (e : PowerIndex n) :
    (powerSectionBasis R n s hs e : GridAmbient R n)=powerSection R n e :=
  (exists_powerSection_basis R n s hs).choose_spec e
end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootPermutation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProjectiveRoot
open ProductSourceCover HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Equiv.Perm (Fin n))
attribute [local instance] MvPolynomial.gradedAlgebra



def permuteSections (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Sections R n s hs m ≃ₗ[Ring R n s] Sections R n s hs (permuteWeight n σ m) where
  toFun x := ⟨permuteGrid R n σ x.val,permute_grid R n σ m s x.val x.property⟩
  invFun x := ⟨(permuteGrid R n σ).symm x.val,by
    rw [permuteGrid_symm]
    have hh := permute_grid R n σ.symm (permuteWeight n σ m) s x.val x.property
    have hw : permuteWeight n σ.symm (permuteWeight n σ m)=m := by
      funext i
      simp [permuteWeight]
    rw [hw] at hh
    exact hh⟩
  left_inv x := Subtype.ext ((permuteGrid R n σ).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((permuteGrid R n σ).apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (by
    change permuteGrid R n σ (scalarMap R n s a*x.val)=scalarMap R n s a*permuteGrid R n σ x.val
    rw [map_mul,permute_scalarMap])

lemma permuteSections_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (m : Fin n → ℤ) (x : Sections R n s hs m) :
    sectionsRestriction R n hs ht (permuteWeight n σ m) hst (permuteSections R n σ s hs m x)=
      permuteSections R n σ t ht m (sectionsRestriction R n hs ht m hst x) := rfl
end Lech.ProjectiveRoot

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

namespace Lech.ProjectiveRoot
open ProductSourceCover UniversalSplitting
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
lemma powerSectionBasis_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (e : PowerIndex n) :
    sectionsRestriction R n hs ht (fun i => (powerWeight n i:ℤ)) hst
      (powerSectionBasis R n s hs e)=powerSectionBasis R n t ht e := by
  apply Subtype.ext
  change (powerSectionBasis R n s hs e : GridAmbient R n)=
    (powerSectionBasis R n t ht e : GridAmbient R n)
  rw [powerSectionBasis_val,powerSectionBasis_val]
end Lech.ProjectiveRoot

end

end OAI
end


