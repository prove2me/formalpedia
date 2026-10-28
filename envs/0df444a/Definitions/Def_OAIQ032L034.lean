-- Prove2me | Definitions.Def_OAIQ032L034
-- name    : OAIQ032L034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T22:22:35.04166+00:00
-- url     : https://prove2.me/theorems/ebe70ed1-b057-4ef4-90fa-6ffe854d392c
-- title:
--   Definitions bundle OAIQ032L034 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 14 definitions and 14 theorems. The definitions and types are `OAI.Lech.ProjectiveRoot.chartEulerMiddle`, `OAI.Lech.ProjectiveRoot.coefficientHomologyIso`, `OAI.Lech.ProjectiveRoot.coefficientHomologySelfIso`, `OAI.Lech.ProjectiveRoot.downEquiv`, `OAI.Lech.ProjectiveRoot.eulerLeft`, `OAI.Lech.ProjectiveRoot.eulerRight`, `OAI.Lech.ProjectiveRoot.gridCechEquiv`, `OAI.Lech.ProjectiveRoot.gridComplexIso`, `OAI.Lech.ProjectiveRoot.gridSectionsEquiv`, `OAI.Lech.ProjectiveRoot.integerCechSplitting`, `OAI.Lech.ProjectiveRoot.integerReductionIso`, `OAI.Lech.ProjectiveRoot.powerSectionBasis`, `OAI.Lech.ProjectiveRoot.reductionCechIso`, `OAI.Lech.ProjectiveRoot.twistEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ReducedRootCohomology`, `Multiplicity_ReesRootInclusion`, `Multiplicity_RootBaseProjective`, `Multiplicity_RootCechCoefficients`, `Multiplicity_RootCechProjective`, `Multiplicity_RootChartUlrich`, `Multiplicity_RootPermutation`, `Multiplicity_RootProjectiveEuler`, `Multiplicity_RootSectionDiagram`, `Multiplicity_RootTwist`.
--
--   **Imports.** It imports the bundles `OAIQ032L032` and `OAIQ032L033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L037` and `OAIQ032L038`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L032
import Definitions.Def_OAIQ032L033

set_option maxHeartbeats 1000000

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTwist
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open MvPolynomial HomogeneousLocalization ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hk : k ∈ s) (hs : s.Nonempty)
variable (m l : Fin n → ℤ) (a : ℤ) (hml : ∀ j, l j = m j + a)



def twistEquiv : Sections R n s hs m ≃ₗ[Ring R n s] Sections R n s hs l where
  toFun x := ⟨_,twist_mem R n k s hk m l a hml x.val x.property⟩
  invFun x := ⟨_,twist_mem R n k s hk l m (-a) (by intro j; rw [hml]; ring) x.val x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (↑((targetUnit R n k)^(-a)) : GridAmbient R n) *
      ((↑((targetUnit R n k)^a) : GridAmbient R n) * x.val) = x.val
    rw [←mul_assoc,←Units.val_mul,←zpow_add,neg_add_cancel,zpow_zero,Units.val_one,one_mul]
  right_inv x := by
    apply Subtype.ext
    change (↑((targetUnit R n k)^a) : GridAmbient R n) *
      ((↑((targetUnit R n k)^(-a)) : GridAmbient R n) * x.val) = x.val
    rw [←mul_assoc,←Units.val_mul,←zpow_add,add_neg_cancel,zpow_zero,Units.val_one,one_mul]
  map_add' x y := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' b x := by
    apply Subtype.ext
    change (↑((targetUnit R n k)^a) : GridAmbient R n) *
      (scalarMap R n s b * x.val) = scalarMap R n s b * _
    exact mul_left_comm _ _ _

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootBaseProjective
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProjectiveRoot
open HomogeneousLocalization MvPolynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

lemma sections_base_projective (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module.Projective R (Sections R n s hs m) := by
  let := ring_base_free R n s
  obtain ⟨k,hk⟩ := hs
  let : Fact (k ∈ s) := ⟨hk⟩
  let := (Sections_properties R n k s ⟨k,hk⟩ m).2.1
  exact ProjectiveScalar.trans (R:=R) (S:=Ring R n s)
end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCechProjective
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def gridSectionsEquiv (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    grid R n m s ∅ ≃ₗ[R] Sections R n s hs m where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma grid_projective (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module.Projective R (grid R n m s ∅) := by
  let := sections_base_projective R n s hs m
  exact Module.Projective.of_equiv (gridSectionsEquiv R n s hs m).symm

lemma zeroAugGrid_projective (s : Finset (Fin (n+1))) (m : Fin n → ℤ) :
    Module.Projective R (AlternatingCech.zeroAugmentation R (GridAmbient R n)
      (fun t => grid R n m t ∅) s) := by
  classical
  by_cases hs : s=∅
  · have he : AlternatingCech.zeroAugmentation R (GridAmbient R n)
        (fun t => grid R n m t ∅) s = ⊥ := by simp [AlternatingCech.zeroAugmentation,hs]
    exact Module.Projective.of_equiv (LinearEquiv.ofEq _ _ he).symm
  · have he : AlternatingCech.zeroAugmentation R (GridAmbient R n)
        (fun t => grid R n m t ∅) s = grid R n m s ∅ := by
          simp [AlternatingCech.zeroAugmentation,hs]
    let := grid_projective R n s (Finset.nonempty_iff_ne_empty.mpr hs) m
    exact Module.Projective.of_equiv (LinearEquiv.ofEq _ _ he).symm

variable [LinearOrder (Chart n)]
omit [LinearOrder (Chart n)] in
lemma target_term_projective (m : Fin n → ℤ) (q : ℕ) :
    Projective ((targetCech R n m).X q) := by
  classical
  let (s : Set.powersetCard (Fin (n+1)) q) := zeroAugGrid_projective R n s.val m
  change Projective (ModuleCat.of R (AlternatingCech.sorted R (GridAmbient R n)
    (AlternatingCech.zeroAugmentation R (GridAmbient R n) (fun t => grid R n m t ∅)) q))
  let : Module.Projective R (AlternatingCech.sorted R (GridAmbient R n)
    (AlternatingCech.zeroAugmentation R (GridAmbient R n) (fun t => grid R n m t ∅)) q) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R:=R))
  exact ModuleCat.projective_of_categoryTheory_projective _

omit [LinearOrder (Chart n)] in
lemma integer_term_projective (m : Fin n → ℤ) (q : ℤ) :
    Projective ((integerCech R n m).X q) := by
  cases q with
  | ofNat q =>
    let := target_term_projective R n m q
    exact Projective.of_iso ((targetCech R n m).extendXIso ComplexShape.embeddingUpNat (i:=q) rfl).symm inferInstance
  | negSucc q =>
    exact (ComplexExtension.negative_zero (targetCech R n m) q).projective



def integerCechSplitting (m : Fin n → ℤ) :
    HomotopyEquiv ((single (ModuleCat.{u} R) (.up ℤ) (negativeCount m+1)).obj
      ((integerCech R n m).homology (negativeCount m+1))) (integerCech R n m) := by
  letI := integer_homology_projective R n m
  letI := integer_bounded R n m
  letI := integer_term_projective R n m
  exact PureProjective.homotopyEquiv (integerCech R n m) (negativeCount m+1) (n+1)
    (integer_pure R n m)
end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCechCoefficients
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]

def coefficientHomologyIso (q : ℤ) :
    (coefficientCech R n m F).homology q ≅
      ((single (ModuleCat.{u} R) (.up ℤ) (negativeCount m+1)).obj
        (F.obj ((integerCech R n m).homology (negativeCount m+1)))).homology q :=
  ((F.mapHomotopyEquiv (integerCechSplitting R n m)).toHomologyIso q).symm ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
      ((singleMapHomologicalComplex F (.up ℤ) (negativeCount m+1)).app _)

def coefficientHomologySelfIso :
    (coefficientCech R n m F).homology (negativeCount m+1) ≅
      F.obj ((integerCech R n m).homology (negativeCount m+1)) :=
  coefficientHomologyIso R n m F (negativeCount m+1) ≪≫
    singleObjHomologySelfIso (.up ℤ) (negativeCount m+1) _

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootSectionDiagram
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (m : Fin n → ℤ)

def gridCechEquiv (s : Finset (Fin (n+1))) :
    zeroAugGrid R n m s ≃ₗ[R] CechSection R n m s where
  toFun x hs := ⟨x.val,by
    change x.val ∈ grid R n m s ∅
    simpa only [zeroAugGrid,AlternatingCech.zeroAugmentation,
      ite_eq_right (Finset.nonempty_iff_ne_empty.mp hs.down)] using x.property⟩
  invFun x := if hs : s.Nonempty then ⟨(x ⟨hs⟩).val,by
    have hx : (x ⟨hs⟩).val ∈ grid R n m s ∅ := (x ⟨hs⟩).property
    simpa only [zeroAugGrid,AlternatingCech.zeroAugmentation,
      ite_eq_right (Finset.nonempty_iff_ne_empty.mp hs)] using hx⟩ else 0
  left_inv x := by
    classical
    by_cases hs : s.Nonempty
    · simp only [dite_eq_left hs]
    · simp only [dite_eq_right hs]
      apply Subtype.ext
      have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have hx : x.val=0 := by simpa [zeroAugGrid,AlternatingCech.zeroAugmentation,he] using x.property
      exact hx.symm
  right_inv x := by
    classical
    funext hs
    simp only [dite_eq_left hs.down]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma gridCechEquiv_natural {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (x : zeroAugGrid R n m s) :
    gridCechEquiv R n m t
      (Submodule.inclusion (AlternatingCech.zeroAugmentation_mono R (GridAmbient R n)
        (fun s => grid R n m s ∅) (grid_target_mono R n m ∅) hst) x)=
      (cechRes R n m hst).hom (gridCechEquiv R n m s x) := by
  classical
  funext ht
  by_cases hs : s.Nonempty
  · rw [cechRes_apply R n m hst hs ht.down]
    rfl
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hx : x.val=0 := by
      simpa [zeroAugGrid,AlternatingCech.zeroAugmentation,he] using x.property
    have hz : (cechRes R n m hst).hom (gridCechEquiv R n m s x) ht=0 := by
      change (if hs : s.Nonempty then _ else 0)=0
      rw [dite_eq_right hs]
    rw [hz]
    apply Subtype.ext
    exact hx

variable [LinearOrder (Chart n)]
 
def gridComplexIso : targetCech R n m ≅ FiniteModuleCech.complex (cechDiagram R n m) :=
  HomologicalComplex.Hom.isoOfComponents (fun q =>
    (LinearEquiv.piCongrRight (fun s : Set.powersetCard (Fin (n+1)) q =>
      gridCechEquiv R n m s.val)).toModuleIso) (by
        intro q r h
        obtain rfl : q+1=r := h
        dsimp only [targetCech,AlternatingCech.unaugmentedComplex]
        rw [FiniteModuleCech.complex_d,AlternatingCech.sortedComplex_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext s
        change _ = gridCechEquiv R n m s.val
          (∑ j : Fin (q+1), (-1:ℤ)^j.val •
            Submodule.inclusion _ (x (AlternatingCech.delete s j)))
        rw [map_sum]
        simp only [map_zsmul]
        change (∑ j : Fin (q+1), (-1:ℤ)^j.val •
          (cechRes R n m (AlternatingCech.delete_subset s j)).hom
            (gridCechEquiv R n m (AlternatingCech.delete s j).val (x (AlternatingCech.delete s j)))) = _
        apply Finset.sum_congr rfl
        intro j _
        rw [gridCechEquiv_natural])
end Lech.ProjectiveRoot

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

def reductionCechIso :
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℕ)).obj (targetCech R n m) ≅
      reducedCech R n m I :=
  ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℕ)).mapIso (gridComplexIso R n m) ≪≫
    FiniteModuleCech.reductionComplexIso (cechDiagram R n m) I

def integerReductionIso :
    coefficientCech R n m (TensorIdeal.quotientFunctor I) ≅
      (reducedCech R n m I).extend ComplexShape.embeddingUpNat :=
  ComplexExtension.mapExtendIso (TensorIdeal.quotientFunctor I) (targetCech R n m) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
      (reductionCechIso R n m I)

end Lech.ProjectiveRoot

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
namespace Lech.ProjectiveRoot
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
variable (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ)

def downEquiv (k : Fin (n+1)) (hk : k ∈ s) :
    Sections R n s hs (fun i => m i+1) ≃ₗ[Ring R n s] Sections R n s hs m :=
  twistEquiv R n k s hk hs _ m (-1) (by intro i; omega)

lemma downEquiv_change (k j : Fin (n+1)) (hk : k ∈ s) (hj : j ∈ s)
    (x : Sections R n s hs (fun i => m i+1)) :
    downEquiv R n s hs m k hk x = ratio R n s k j hk • downEquiv R n s hs m j hj x := by
  apply Subtype.ext
  change (↑((targetUnit R n k)^(-1:ℤ)) : GridAmbient R n) * x.val =
    scalarMap R n s (ratio R n s k j hk) *
      ((↑((targetUnit R n j)^(-1:ℤ)) : GridAmbient R n) * x.val)
  rw [scalarMap_ratio]
  simp only [zpow_neg_one]
  rw [mul_assoc,←mul_assoc (↑(targetUnit R n j) : GridAmbient R n),Units.mul_inv,one_mul]

lemma downEquiv_restriction {t : Finset (Fin (n+1))} (ht : t.Nonempty) (hst : s ⊆ t)
    (k : Fin (n+1)) (hk : k ∈ s) (x : Sections R n s hs (fun i => m i+1)) :
    sectionsRestriction R n hs ht m hst (downEquiv R n s hs m k hk x) =
      downEquiv R n t ht m k (hst hk) (sectionsRestriction R n hs ht _ hst x) := rfl
end Lech.ProjectiveRoot

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

 
theorem exists_powerSection_basis (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    ∃ b : Module.Basis (PowerIndex n) (Ring R n s)
      (Sections R n s hs (fun i => (powerWeight n i:ℤ))),
      ∀ e,(b e : GridAmbient R n)=powerSection R n e := by
  let k := hs.choose
  have hk : k∈s := hs.choose_spec
  let : Fact (k∈s) := ⟨hk⟩
  let : Algebra (UniversalCoefficientChart.Ring R n k) (Ring R n s) :=
    coefficientAlgebra R n k s hk
  obtain ⟨b,hb⟩ := ProductSourceCover.exists_powerSection_basis R n k
  refine ⟨(b.baseChange (Ring R n s)).map (chartBaseChange R n k s hs _),?_⟩
  intro e
  rw [Module.Basis.map_apply,Module.Basis.baseChange_apply]
  rw [chartBaseChange_one R n k s hs _ (b e)]
  exact hb e

 
def powerSectionBasis (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    Module.Basis (PowerIndex n) (Ring R n s)
      (Sections R n s hs (fun i => (powerWeight n i:ℤ))) :=
  (exists_powerSection_basis R n s hs).choose
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

lemma permute_coefficientEvaluation (a : MvPolynomial (Fin (n+1)) R) :
    permuteGrid R n σ (coefficientEvaluation R n a)=coefficientEvaluation R n a := by
  have he : (permuteGrid R n σ).toAlgHom.comp (coefficientEvaluation R n)=coefficientEvaluation R n := by
    ext j
    simp only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,coefficientEvaluation_X,
      targetUnit_val,permuteGrid_embed,ProductLaurent.permute_coefficient]
  exact DFunLike.congr_fun he a

lemma permute_scalarMap (s : Finset (Fin (n+1))) (a : Ring R n s) :
    permuteGrid R n σ (scalarMap R n s a)=scalarMap R n s a := by
  let f := Localization.awayLift (coefficientEvaluation R n).toRingHom
    (product R n s) (coefficientEvaluation_unit R n s)
  have he : ((permuteGrid R n σ : GridAmbient R n →+* GridAmbient R n).comp f)=f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (product R n s))
    apply RingHom.ext
    intro x
    change permuteGrid R n σ (f (algebraMap _ _ x))=f (algebraMap _ _ x)
    dsimp only [f]
    rw [IsLocalization.Away.lift_eq]
    exact permute_coefficientEvaluation R n σ x
  exact DFunLike.congr_fun he a.val



end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootProjectiveEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

def eulerLeft (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Sections R n s hs m →ₗ[Ring R n s]
      Sections R n s hs (Pi.single i 1+m) × Sections R n s hs (Pi.single i 1+m) :=
  (coordinateMul R n s hs m i false).prod (-coordinateMul R n s hs m i true)
def eulerRight (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Sections R n s hs (Pi.single i 1+m) × Sections R n s hs (Pi.single i 1+m) →ₗ[Ring R n s]
      Sections R n s hs (Pi.single i 1+(Pi.single i 1+m)) :=
  (coordinateMul R n s hs (Pi.single i 1+m) i true).coprod
    (coordinateMul R n s hs (Pi.single i 1+m) i false)

section Intersection
variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hs : s.Nonempty) [hks : Fact (k∈s)]

attribute [local instance] OAI.Lech.ProjectiveRoot.projectiveEulerInstance1
def chartEulerMiddle (m : Fin n → ℤ) :
    Ring R n s ⊗[UniversalCoefficientChart.Ring R n k] (sectionModule R n k m × sectionModule R n k m)
      ≃ₗ[Ring R n s] Sections R n s hs m × Sections R n s hs m :=
  TensorProduct.prodRight _ (Ring R n s) (Ring R n s) _ _ ≪≫ₗ
    (chartBaseChange R n k s hs m).prodCongr (chartBaseChange R n k s hs m)

include k hks in
lemma intersection_euler_shortExact (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft R n s hs m i) ∧
      Function.Exact (eulerLeft R n s hs m i) (eulerRight R n s hs m i) ∧
        Function.Surjective (eulerRight R n s hs m i) := by
  let := (sectionModule_properties R n k (Pi.single i 1+(Pi.single i 1+m))).2.1
  obtain ⟨hi,he,hq⟩ := ProductSourceCover.euler_shortExact R n k m i
  obtain ⟨hi,he,hq⟩ := ModuleSequence.baseChange (Ring R n s)
    (ProductSourceCover.eulerLeft R n k m i) (ProductSourceCover.eulerRight R n k m i) hi he hq
  apply ModuleSequence.transport
    (A := Ring R n s)
    (M := Ring R n s ⊗[UniversalCoefficientChart.Ring R n k] sectionModule R n k m)
    (N := Ring R n s ⊗[UniversalCoefficientChart.Ring R n k]
      (sectionModule R n k (Pi.single i 1+m) × sectionModule R n k (Pi.single i 1+m)))
    (P := Ring R n s ⊗[UniversalCoefficientChart.Ring R n k]
      sectionModule R n k (Pi.single i 1+(Pi.single i 1+m)))
    ((ProductSourceCover.eulerLeft R n k m i).baseChange (Ring R n s))
    ((ProductSourceCover.eulerRight R n k m i).baseChange (Ring R n s))
    (eulerLeft R n s hs m i) (eulerRight R n s hs m i)
    (chartBaseChange R n k s hs m) (chartEulerMiddle R n k s hs (Pi.single i 1+m))
    (chartBaseChange R n k s hs (Pi.single i 1+(Pi.single i 1+m)))
  · apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul a x =>
        apply Prod.ext
        · exact chartBaseChange_coordinateMul R n k s hs m i false a x
        · change chartBaseChange R n k s hs (Pi.single i 1+m)
            (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] (-ProductSourceCover.coordinateMul R n k m i true x))=_
          rw [TensorProduct.tmul_neg]
          change chartBaseChange R n k s hs (Pi.single i 1+m)
            (-(a ⊗ₜ[UniversalCoefficientChart.Ring R n k] ProductSourceCover.coordinateMul R n k m i true x))=
            -(coordinateMul R n s hs m i true (chartBaseChange R n k s hs m
              (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] x)))
          exact (map_neg (chartBaseChange R n k s hs (Pi.single i 1+m)) _).trans
            (congrArg Neg.neg (chartBaseChange_coordinateMul R n k s hs m i true a x))
    | add x y hx hy => simp only [map_add,hx,hy]
  · apply LinearMap.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul a x =>
        change chartBaseChange R n k s hs _
          (a ⊗ₜ[UniversalCoefficientChart.Ring R n k]
            (ProductSourceCover.coordinateMul R n k _ i true x.1+
              ProductSourceCover.coordinateMul R n k _ i false x.2))=_
        rw [TensorProduct.tmul_add,map_add,chartBaseChange_coordinateMul,chartBaseChange_coordinateMul]
        rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  · exact hi
  · exact he
  · exact hq
end Intersection

 

theorem euler_shortExact (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft R n s hs m i) ∧
      Function.Exact (eulerLeft R n s hs m i) (eulerRight R n s hs m i) ∧
        Function.Surjective (eulerRight R n s hs m i) := by
  let k := hs.choose
  let : Fact (k∈s) := ⟨hs.choose_spec⟩
  exact intersection_euler_shortExact R n k s hs m i

lemma coordinateMul_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (m : Fin n → ℤ) (i : Fin n) (b : Bool) (x : Sections R n s hs m) :
    sectionsRestriction R n hs ht (Pi.single i 1+m) hst (coordinateMul R n s hs m i b x)=
      coordinateMul R n t ht m i b (sectionsRestriction R n hs ht m hst x) := rfl
end Lech.ProjectiveRoot

end

end OAI
end


