-- Prove2me | Definitions.Def_OAIQ032L035
-- name    : OAIQ032L035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T22:24:42.130575+00:00
-- url     : https://prove2.me/theorems/cb9a3b43-1f71-4279-9f44-2d1e0390eb43
-- title:
--   Definitions bundle OAIQ032L035 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 72 declarations of OpenAI's Lean: 56 definitions and 16 theorems. The definitions and types are `OAI.Lech.ProjectiveRoot.reducedPositive`, `OAI.Lech.ProjectiveRoot.reducedPositiveHomologyIso`, `OAI.Lech.ReesRoot.CechSection`, `OAI.Lech.ReesRoot.ExceptionalSections`, `OAI.Lech.ReesRoot.RootFibreSections`, `OAI.Lech.ReesRoot.Sections`, `OAI.Lech.ReesRoot.ambientInclusion`, `OAI.Lech.ReesRoot.bundleSectionBaseModule`, `OAI.Lech.ReesRoot.bundleSectionGroup`, `OAI.Lech.ReesRoot.cech`, `OAI.Lech.ReesRoot.cechDiagram`, `OAI.Lech.ReesRoot.cechObj`, `OAI.Lech.ReesRoot.cechRes`, `OAI.Lech.ReesRoot.cechZ`, `OAI.Lech.ReesRoot.coordinateCechHom`, `OAI.Lech.ReesRoot.coordinateMul`, `OAI.Lech.ReesRoot.enlargedAt`, `OAI.Lech.ReesRoot.enlargedMap`, `OAI.Lech.ReesRoot.eulerLeft`, `OAI.Lech.ReesRoot.eulerRight`, `OAI.Lech.ReesRoot.exceptionalCech`, `OAI.Lech.ReesRoot.exceptionalCechZIso`, `OAI.Lech.ReesRoot.exceptionalDiagram`, `OAI.Lech.ReesRoot.exceptionalZ`, `OAI.Lech.ReesRoot.fibreCechMap`, `OAI.Lech.ReesRoot.firstZ`, `OAI.Lech.ReesRoot.firstZIso`, `OAI.Lech.ReesRoot.layerAt`, `OAI.Lech.ReesRoot.layerAtProjection`, `OAI.Lech.ReesRoot.layerProjection`, `OAI.Lech.ReesRoot.quotientAt`, `OAI.Lech.ReesRoot.quotientProjection`, `OAI.Lech.ReesRoot.rootReductionDiagram`, `OAI.Lech.ReesRoot.sectionBaseModule`, `OAI.Lech.ReesRoot.sectionBaseModule`, `OAI.Lech.ReesRoot.sectionBaseModule`, `OAI.Lech.ReesRoot.sectionBaseModule`, `OAI.Lech.ReesRoot.sectionChartModule`, `OAI.Lech.ReesRoot.sectionChartModule`, `OAI.Lech.ReesRoot.sectionChartModule` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_CechCartierRange`, `Multiplicity_ExceptionalFibre`, `Multiplicity_ExceptionalRootCohomology`, `Multiplicity_ReesRootBundle`, `Multiplicity_ReesRootCech`, `Multiplicity_ReesRootEuler`, `Multiplicity_ReesRootG`, `Multiplicity_ReesRootGLayer`, `Multiplicity_ReesRootGLayerCohomology`, `Multiplicity_ReesRootInclusion`, `Multiplicity_ReesRootIteration`, `Multiplicity_ReesRootLayerCech`, `Multiplicity_ReesRootLayers`, `Multiplicity_ReesRootNilpotence`, `Multiplicity_ReesRootQuotient`, `Multiplicity_ReesRootThickeningEuler`, `Multiplicity_ReesRootUnfiltered`, `Multiplicity_RootFibreCech`, `Multiplicity_RootRestriction`.
--
--   **Imports.** It imports the bundle `OAIQ032L032` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L037` and `OAIQ032L038`; the statements `OAI.Lech.ReesRoot.ambientStrip_euler`, `OAI.Lech.ReesRoot.ambient_euler_additive`, `OAI.Lech.ReesRoot.enlargedAtTotal_finite`, `OAI.Lech.ReesRoot.exceptionalZ_finite`, `OAI.Lech.ReesRoot.fibreCech_homology`, `OAI.Lech.ReesRoot.layerAtTotal_finite`, `OAI.Lech.ReesRoot.quotientAtTotal_euler`, `OAI.Lech.ReesRoot.quotientAtTotal_finite`, `OAI.Lech.ReesRoot.rootTotal_pure` and `OAI.Lech.ReesRoot.unfilteredTotal_finite`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L032

set_option maxHeartbeats 1000000

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootRestriction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

variable {s t v : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty) (hv : v.Nonempty)
variable (m : Fin n → ℤ)



lemma sectionsRestriction_comp (hst : s ⊆ t) (htv : t ⊆ v) (x : Sections R n s hs m) :
    sectionsRestriction R n ht hv m htv (sectionsRestriction R n hs ht m hst x) =
      sectionsRestriction R n hs hv m (hst.trans htv) x := rfl

lemma sectionsRestriction_self (x : Sections R n s hs m) :
    sectionsRestriction R n hs hs m (Finset.Subset.refl s) x = x := rfl

 
theorem sections_properties :
    Module.FinitePresentation (Ring R n s) (Sections R n s hs m) ∧
    Module.Projective (Ring R n s) (Sections R n s hs m) ∧
    ∀ p : PrimeSpectrum (Ring R n s),
      Module.rankAtStalk (Sections R n s hs m) p = n.factorial := by
  have hs' := hs
  obtain ⟨k,hk⟩ := hs'
  let : Fact (k ∈ s) := ⟨hk⟩
  exact Sections_properties R n k s hs m

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootBundle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup


abbrev Sections (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :=
  Ring I z hz s ⊗[ProjectiveRoot.Ring R n s] ProjectiveRoot.Sections R n s hs m

attribute [local instance] OAI.Lech.ReesRoot.bundleBaseAlgebra
attribute [local instance] OAI.Lech.ReesRoot.bundleBaseModule
attribute [local instance] OAI.Lech.ReesRoot.bundleProjectiveModule
local instance bundleSectionGroup (support : Finset (Fin (n+1)))
    (h_support : support.Nonempty) (weight : Fin n → ℤ) :
    AddCommGroup (Sections I z hz support h_support weight) := TensorProduct.addCommGroup
attribute [local instance] OAI.Lech.ReesRoot.bundleScalarComm
local instance bundleSectionBaseModule (support : Finset (Fin (n+1)))
    (h_support : support.Nonempty) (weight : Fin n → ℤ) :
    Module R (Sections I z hz support h_support weight) := TensorProduct.leftModule

variable {s t v : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
  (hv : v.Nonempty) (m : Fin n → ℤ)

def sectionsRestrictionSemi (hst : s ⊆ t) :
    Sections I z hz s hs m →ₛₗ[ProjectiveRoot.ringRestriction R n hst] Sections I z hz t ht m :=
  TensorProduct.map (coefficientRestriction I z hz hst)
    (ProjectiveRoot.sectionsRestriction R n hs ht m hst)


attribute [local instance] OAI.Lech.ReesRoot.bundleConcreteRing
def sectionsRestriction (hst : s ⊆ t) : Sections I z hz s hs m →ₗ[R] Sections I z hz t ht m where
  toFun := sectionsRestrictionSemi I z hz hs ht m hst
  map_add' := map_add _
  map_smul' r x := by
    change sectionsRestrictionSemi I z hz hs ht m hst (r • x) =
      r • sectionsRestrictionSemi I z hz hs ht m hst x
    induction x using OAI.tensorInductionOn with
    | tmul coefficient element =>
        change (restrictionAlg I z hz hst).toLinearMap (r • coefficient) ⊗ₜ
            ProjectiveRoot.sectionsRestriction R n hs ht m hst element =
          (r • (restrictionAlg I z hz hst).toLinearMap coefficient) ⊗ₜ
            ProjectiveRoot.sectionsRestriction R n hs ht m hst element
        rw [(restrictionAlg I z hz hst).toLinearMap.map_smul r coefficient]
    | add first second hfirst hsecond =>
        rw [smul_add,map_add,map_add,hfirst,hsecond,smul_add]

lemma sectionsRestriction_tmul (hst : s ⊆ t) (b : Ring I z hz s)
    (x : ProjectiveRoot.Sections R n s hs m) :
    sectionsRestriction I z hz hs ht m hst (b ⊗ₜ x) =
      restriction I z hz hst b ⊗ₜ ProjectiveRoot.sectionsRestriction R n hs ht m hst x := rfl

lemma sectionsRestriction_self (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz hs hs m (Finset.Subset.refl s) x = x := by
  induction x using OAI.tensorInductionOn with
  | tmul b x => rw [sectionsRestriction_tmul,restriction_self,ProjectiveRoot.sectionsRestriction_self]
  | add x y hx hy => rw [map_add,hx,hy]

lemma sectionsRestriction_comp (hst : s ⊆ t) (htv : t ⊆ v) (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz ht hv m htv (sectionsRestriction I z hz hs ht m hst x) =
      sectionsRestriction I z hz hs hv m (hst.trans htv) x := by
  induction x using OAI.tensorInductionOn with
  | tmul b x =>
      rw [sectionsRestriction_tmul,sectionsRestriction_tmul,sectionsRestriction_tmul,
        restriction_comp,ProjectiveRoot.sectionsRestriction_comp]
  | add x y hx hy => simp only [map_add,hx,hy]


theorem sections_properties :
    Module.FinitePresentation (Ring I z hz s) (Sections I z hz s hs m) ∧
    Module.Projective (Ring I z hz s) (Sections I z hz s hs m) ∧
    ∀ p : PrimeSpectrum (Ring I z hz s),
      Module.rankAtStalk (Sections I z hz s hs m) p = n.factorial := by
  obtain ⟨hfp,hpr,hr⟩ := ProjectiveRoot.sections_properties R n hs m
  let := hfp
  let := hpr
  refine ⟨inferInstance,inferInstance,?_⟩
  intro p
  rw [Module.rankAtStalk_baseChange]
  exact hr _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I) (m : Fin n → ℤ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p4
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p2
attribute [local instance] OAI.Lech.ReesRoot.projectiveModule_p1
local instance sectionGroup_p3 (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p1
local instance sectionModule_p3 (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

 

abbrev CechSection (s : Finset (Fin (n+1))) :=
  (hs : PLift s.Nonempty) → Sections I z hz s hs.down m

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p4
abbrev cechObj (s : Finset (Fin (n+1))) : ModuleCat.{u} R :=
  ModuleCat.of R (CechSection I z hz m s)

def cechRes {s t : Finset (Fin (n+1))} (hst : s ⊆ t) : cechObj I z hz m s ⟶ cechObj I z hz m t :=
  ModuleCat.ofHom {
    toFun x ht := if hs : s.Nonempty then sectionsRestriction I z hz hs ht.down m hst (x ⟨hs⟩) else 0
    map_add' x y := by
      funext ht
      split_ifs <;> simp only [Pi.add_apply,map_add,add_zero]
    map_smul' r x := by
      funext ht
      split_ifs <;> simp only [Pi.smul_apply,map_smul,RingHom.id_apply,smul_zero] }

lemma cechRes_apply {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (x : CechSection I z hz m s) :
    (cechRes I z hz m hst).hom x ⟨ht⟩ = sectionsRestriction I z hz hs ht m hst (x ⟨hs⟩) := by
  change (if hs : s.Nonempty then _ else _) = _
  rw [dite_eq_left hs]

lemma cechRes_self (s : Finset (Fin (n+1))) :
    cechRes I z hz m (Finset.Subset.refl s) = 𝟙 (cechObj I z hz m s) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hs
  exact (cechRes_apply I z hz m _ hs.down hs.down x).trans (sectionsRestriction_self I z hz hs.down m (x hs))

lemma cechRes_comp {s t v : Finset (Fin (n+1))} (hst : s ⊆ t) (htv : t ⊆ v) :
    cechRes I z hz m hst ≫ cechRes I z hz m htv = cechRes I z hz m (hst.trans htv) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hv
  obtain ⟨hv⟩ := hv
  by_cases hs : s.Nonempty
  · have ht : t.Nonempty := hs.mono hst
    change (cechRes I z hz m htv).hom ((cechRes I z hz m hst).hom x) ⟨hv⟩ = _
    rw [cechRes_apply I z hz m htv ht hv,cechRes_apply I z hz m hst hs ht,
      cechRes_apply I z hz m (hst.trans htv) hs hv]
    exact sectionsRestriction_comp I z hz hs ht hv m hst htv (x ⟨hs⟩)
  · change (if ht : t.Nonempty then
      sectionsRestriction I z hz ht hv m htv (if hs : s.Nonempty then _ else 0) else 0) =
        if hs : s.Nonempty then _ else 0
    rw [dite_eq_right hs]
    split_ifs <;> simp only [map_zero]

 
def cechDiagram : FiniteModuleCech.Diagram R (Fin (n+1)) where
  obj := cechObj I z hz m
  res := cechRes I z hz m
  res_self := cechRes_self I z hz m
  res_comp := cechRes_comp I z hz m

 
def cech : CochainComplex (ModuleCat.{u} R) ℕ :=
  FiniteModuleCech.positiveComplex (cechDiagram I z hz m)

end Lech.ReesRoot

end

end OAI
end

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
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p7
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p7
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p5
attribute [local instance] OAI.Lech.ReesRoot.projectiveModule_p4
local instance sectionChartModule_p1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := TensorProduct.leftModule
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p4
local instance sectionBaseModule_p1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

open CategoryTheory CategoryTheory.Limits

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
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p10
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p8
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p10
private local instance projectiveModule_r581b7f_1 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
local instance sectionGroup_p9 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
local instance sectionChartModule_p4 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := TensorProduct.leftModule
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p7
local instance sectionBaseModule_p4 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

variable (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ)


abbrev ExceptionalSections :=
  Sections I z hz s hs m ⧸ (I • (⊤ : Submodule R (Sections I z hz s hs m)))


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
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p8
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p8
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p6
private local instance projectiveModule_r581b7f_2 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
local instance sectionChartModule_p2 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := TensorProduct.leftModule

attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p5
local instance sectionTower_p0 (t : Finset (Fin (n+1))) (ht : t.Nonempty) (m : Fin n → ℤ) :
    IsScalarTower R (Ring I z hz t) (Sections I z hz t ht m) := TensorProduct.isScalarTower_left

open CategoryTheory CategoryTheory.Limits HomologicalComplex

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
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p0
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p0
attribute [local instance] OAI.Lech.ReesRoot.projectiveModule_p0
local instance sectionGroup_p0 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p0
local instance sectionModule_p0 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalFibre
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory IdealGraded HomogeneousLocalization
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
attribute [local instance] OAI.Lech.ReesRoot.reesModule_p0
attribute [local instance] OAI.Lech.ReesRoot.reesBaseAlgebra_p0
attribute [local instance] OAI.Lech.ReesRoot.reesPModule_p0
local instance sectionGroup_p1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup

abbrev RootFibreSections (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :=
  ProjectiveRoot.Sections R n s hs m ⧸ (I • (⊤ : Submodule R (ProjectiveRoot.Sections R n s hs m)))



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootFibreCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
attribute [local instance] OAI.Lech.ReesRoot.reesRing_p2
attribute [local instance] OAI.Lech.ReesRoot.reesModule_p2
attribute [local instance] OAI.Lech.ReesRoot.reesBaseAlgebra_p2
attribute [local instance] OAI.Lech.ReesRoot.reesPModule_p2
private local instance sectionGroup_r581b7f_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
attribute [local instance] OAI.Lech.ReesRoot.reesScalarComm_p2
private local instance sectionModule_r581b7f_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule
private local instance projectiveSectionModule_r581b7f_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (m : Fin n → ℤ) : Module R (ProjectiveRoot.Sections R n s hs m) :=
  (ProjectiveRoot.Sections R n s hs m).module'
def unitCech (s : Finset (Fin (n+1))) : ProjectiveRoot.cechObj R n m s ⟶ cechObj I z hz m s :=
  ModuleCat.ofHom (LinearMap.pi (fun hs : PLift s.Nonempty =>
    (TensorIdeal.unitMap (A:=ProjectiveRoot.Ring R n s) (B:=Ring I z hz s)
      (ProjectiveRoot.Sections R n s hs.down m)).comp (LinearMap.proj hs)))

lemma unitCech_natural {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    ProjectiveRoot.cechRes R n m hst ≫ unitCech I z hz m t =
      unitCech I z hz m s ≫ cechRes I z hz m hst := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext ht
  by_cases hs : s.Nonempty
  · change (1 ⊗ₜ[ProjectiveRoot.Ring R n t] ((ProjectiveRoot.cechRes R n m hst).hom x ht)) =
      (cechRes I z hz m hst).hom ((unitCech I z hz m s).hom x) ht
    rw [ProjectiveRoot.cechRes_apply R n m hst hs ht.down,
      cechRes_apply I z hz m hst hs ht.down]
    change _ = sectionsRestriction I z hz hs ht.down m hst
      (1 ⊗ₜ[ProjectiveRoot.Ring R n s] x ⟨hs⟩)
    rw [sectionsRestriction_tmul,map_one]
    rfl
  · change (1 ⊗ₜ[ProjectiveRoot.Ring R n t] (if hs : s.Nonempty then _ else 0)) =
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,TensorProduct.tmul_zero]

def unitCechMap : FiniteModuleCech.Map (ProjectiveRoot.cechDiagram R n m) (cechDiagram I z hz m) where
  app := unitCech I z hz m
  naturality := unitCech_natural I z hz m

abbrev rootReductionDiagram := FiniteModuleCech.reduction (ProjectiveRoot.cechDiagram R n m) I
abbrev exceptionalDiagram := FiniteModuleCech.reduction (cechDiagram I z hz m) I

def fibreCechMap : FiniteModuleCech.Map (rootReductionDiagram I m) (exceptionalDiagram I z hz m) :=
  FiniteModuleCech.Map.coefficients (ProjectiveRoot.cechDiagram R n m)
    (TensorIdeal.quotientFunctor I) (unitCechMap I z hz m)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalRootCohomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (I : Ideal R)

abbrev reducedPositive := FiniteModuleCech.positiveComplex
  (FiniteModuleCech.reduction (cechDiagram R n m) I)

def reducedPositiveHomologyIso (q : ℕ) :
    (reducedPositive R n m I).homology q ≅ (reducedCech R n m I).homology (q+1) :=
  FiniteModuleCech.positiveHomologyIso _
    ((TensorIdeal.quotientFunctor I).map_isZero (cech_empty_zero R n m)) q

end Lech.ProjectiveRoot

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

abbrev exceptionalCech := FiniteModuleCech.positiveComplex (exceptionalDiagram I z hz m)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEuler
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
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p5
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p5
local instance sectionChartModule_p0 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := inferInstance

attribute [local instance] OAI.Lech.ReesRoot.baseModule_p3
attribute [local instance] OAI.Lech.ReesRoot.projectiveModule_p2
local instance sectionGroup_p4 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p2
local instance sectionModule_p4 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

 

def coordinateMul (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    Sections I z hz s hs m →ₗ[Ring I z hz s] Sections I z hz s hs (Pi.single i 1+m) :=
  (ProjectiveRoot.coordinateMul R n s hs m i b).baseChange (Ring I z hz s)

def eulerLeft (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Sections I z hz s hs m →ₗ[Ring I z hz s]
      Sections I z hz s hs (Pi.single i 1+m) × Sections I z hz s hs (Pi.single i 1+m) :=
  (coordinateMul I z hz s hs m i false).prod (-coordinateMul I z hz s hs m i true)
def eulerRight (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Sections I z hz s hs (Pi.single i 1+m) × Sections I z hz s hs (Pi.single i 1+m) →ₗ[Ring I z hz s]
      Sections I z hz s hs (Pi.single i 1+(Pi.single i 1+m)) :=
  (coordinateMul I z hz s hs (Pi.single i 1+m) i true).coprod
    (coordinateMul I z hz s hs (Pi.single i 1+m) i false)

def coordinateCechHom (m : Fin n → ℤ) (i : Fin n) (b : Bool) (s : Finset (Fin (n+1))) :
    cechObj I z hz m s ⟶ cechObj I z hz (Pi.single i 1+m) s :=
  ModuleCat.ofHom {
    toFun x hs := coordinateMul I z hz s hs.down m i b (x hs)
    map_add' x y := by funext hs; exact map_add _ _ _
    map_smul' r x := by
      funext hs
      exact map_smul ((coordinateMul I z hz s hs.down m i b).restrictScalars R) r (x hs) }

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootG
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)



def cechZ : CochainComplex (ModuleCat.{u} R) ℤ :=
  (cech I z hz m).extend ComplexShape.embeddingUpNat

lemma cechZ_negative (q : ℤ) (hq : q < 0) : IsZero ((cechZ I z hz m).X q) := by
  apply (cech I z hz m).isZero_extend_X
  intro j hj
  change (j:ℤ)=q at hj
  omega



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootNilpotence
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
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p11
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p9
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p11
private local instance projectiveModule_r581b7f_3 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
local instance sectionGroup_p10 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p8
local instance sectionBaseModule_p5 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

local instance sectionTower_p1 (t : Finset (Fin (n+1))) (ht : t.Nonempty) (m : Fin n → ℤ) :
    IsScalarTower R (Ring I z hz t) (Sections I z hz t ht m) := TensorProduct.isScalarTower_left

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℕ)
  (H : ∀ k, Homotopy (z k^a • 𝟙 F) 0)

variable (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))

 

def enlargedAt (m : Fin n → ℤ) : TotalGhost.Bic (R:=R) :=
  HomologicalComplex₂.flip (((IdealFiltered.functor I F h s hd).mapHomologicalComplex (.up ℤ)).obj
    (cechZ I z hz m))

def enlargedMap {m m' : Fin n → ℤ} (f : cechZ I z hz m ⟶ cechZ I z hz m') :
    enlargedAt I z hz F h s hd m ⟶ enlargedAt I z hz F h s hd m' :=
  (HomologicalComplex₂.flipFunctor _ _ _).map
    (((IdealFiltered.functor I F h s hd).mapHomologicalComplex (.up ℤ)).map f)



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

 
def layerAt : TotalGhost.Bic (R:=R) :=
  (((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj
    (enlargedAt I z hz F h s hd m)

def layerAtProjection : enlargedAt I z hz F h s hd m ⟶ layerAt I z hz F h s hd m :=
  (TensorIdeal.bicomplexQuotientNat I (.up ℤ) (.up ℤ)).app (enlargedAt I z hz F h s hd m)

lemma layerAtProjection_f (p q : ℤ) :
    ((layerAtProjection I z hz F h s hd m).f p).f q =
      (TensorIdeal.quotientNat I).app (((enlargedAt I z hz F h s hd m).X p).X q) :=
  TensorIdeal.bicomplexQuotientNat_f I (.up ℤ) (.up ℤ) _ p q

variable (hgen : Ideal.span (Set.range z)=I)


def exceptionalCechZIso :
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℤ)).obj (cechZ I z hz m) ≅
      (FiniteModuleCech.positiveComplex (exceptionalDiagram I z hz m)).extend
        ComplexShape.embeddingUpNat :=
  ComplexExtension.mapExtendIso (TensorIdeal.quotientFunctor I) (cech I z hz m) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
      (FiniteModuleCech.reductionPositiveIso (cechDiagram I z hz m) I)



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

abbrev exceptionalZ := (exceptionalCech I z hz m).extend ComplexShape.embeddingUpNat

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
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p9
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p7
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p9
private local instance projectiveModule_r581b7f_4 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
local instance sectionGroup_p8 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p6
variable (m : Fin n → ℤ)

def layerProjection : FiniteModuleCech.Map (cechDiagram I z hz m)
    (FiniteModuleCech.reduction (cechDiagram I z hz m) I) where
  app s := (TensorIdeal.quotientNat I).app (cechObj I z hz m s)
  naturality hst := (TensorIdeal.quotientNat I).naturality (cechRes I z hz m hst)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootUnfiltered
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ) (m : Fin n → ℤ)

 
def unfilteredAt : TotalGhost.Bic (R:=R) :=
  (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F).obj
    (cechZ I z hz m)



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootQuotient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)

 
def quotientAt : TotalGhost.Bic (R:=R) :=
  flip (((IdealFiltered.quotientFunctor I F h s hd).mapHomologicalComplex (.up ℤ)).obj (cechZ I z hz m))

def ambientInclusion : enlargedAt I z hz F h s hd m ⟶ unfilteredAt I z hz F m where
  f p := { f q := (IdealFiltered.ambientInclusion I F h s hd ((cechZ I z hz m).X q)).f p
           comm' _ _ _ := rfl }
  comm' _ _ _ := by apply Hom.ext; funext q; rfl

def quotientProjection : unfilteredAt I z hz F m ⟶ quotientAt I z hz F h s hd m where
  f p := { f q := ModuleCat.ofHom (IdealFiltered.term I F h s ((cechZ I z hz m).X q) p).mkQ
           comm' _ _ _ := rfl }
  comm' _ _ _ := by apply Hom.ext; funext q; rfl

lemma ambient_quotient_zero : ambientInclusion I z hz F h s hd m ≫ quotientProjection I z hz F h s hd m=0 := by
  apply Hom.ext
  funext p
  apply Hom.ext
  funext q
  exact congrArg (fun f => f.f p) (ModuleComplexQuotient.inclusion_projection
    (IdealFiltered.tensorComplex F ((cechZ I z hz m).X q))
    (IdealFiltered.term I F h s ((cechZ I z hz m).X q))
    (IdealFiltered.term_d I F h s hd ((cechZ I z hz m).X q)))


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

abbrev firstZ := CartierQuotient.quotient I (cechZ I z hz m)

def firstZIso : firstZ I z hz m ≅ exceptionalZ I z hz m := exceptionalCechZIso I z hz m

end Lech.ReesRoot

end

end OAI
end


