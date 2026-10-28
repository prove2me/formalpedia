-- Prove2me | Definitions.Def_OAIQ032L024
-- name    : OAIQ032L024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:12:37.239498+00:00
-- url     : https://prove2.me/theorems/ae4b3342-b7ce-4766-85c1-869c26886f49
-- title:
--   Definitions bundle OAIQ032L024 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 25 definitions, 1 instance and 8 theorems. The definitions and types are `OAI.Lech.DoubleCech.columnZeroIso`, `OAI.Lech.DoubleCech.coverComparison`, `OAI.Lech.DoubleCech.rowZeroIso`, `OAI.Lech.DoubleCech.unaugmentedCoverComparison`, `OAI.Lech.FilteredCech.ordinaryPositive`, `OAI.Lech.FilteredCech.shiftOrdinaryIso`, `OAI.Lech.FilteredCech.shiftRestrictionIso`, `OAI.Lech.FilteredCech.shiftToOrdinary`, `OAI.Lech.FilteredCech.shiftXIso`, `OAI.Lech.FiniteModuleCech.Map.positiveComplex`, `OAI.Lech.FiniteModuleCech.complex`, `OAI.Lech.FiniteModuleCech.copiesCongr`, `OAI.Lech.FiniteModuleCech.copiesSuccIso`, `OAI.Lech.FiniteModuleCech.positiveHomologyIso`, `OAI.Lech.FiniteModuleCech.positiveIso`, `OAI.Lech.FiniteModuleCech.positiveIsoOfNonempty`, `OAI.Lech.FiniteModuleCech.positiveShortComplex`, `OAI.Lech.FiniteModuleCech.positiveSuccScIso`, `OAI.Lech.FiniteModuleCech.positiveZ`, `OAI.Lech.FiniteModuleCech.positiveZeroScMap`, `OAI.Lech.FiniteModuleCech.tensorCech`, `OAI.Lech.FiniteModuleCech.tensorCechMap`, `OAI.Lech.FiniteModuleCech.tensorEuler`, `OAI.Lech.ProductSourceCover.GridAmbient`, `OAI.Lech.ProductSourceCover.targetCoeff`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_CechCopies`, `Multiplicity_CechExact`, `Multiplicity_CechIndexing`, `Multiplicity_FiniteModuleCech`, `Multiplicity_LechConnectingIso`, `Multiplicity_ProductSourceCoverOrdinaryPositive`, `Multiplicity_ReesRootCech`, `Multiplicity_ReesUlrichCech`, `Multiplicity_ScalarCechComparison`, `Multiplicity_ScalarCechShift`, `Multiplicity_ScalarChartComparison`, `Multiplicity_TensorCechEuler`.
--
--   **Imports.** It imports the bundles `OAIQ032L019`, `OAIQ032L020` and `OAIQ032L021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L028` and `OAIQ032L029`; the statements `OAI.Lech.FiniteModuleCech.tensorEuler_copies`, `OAI.Lech.FiniteModuleCech.tensor_euler_rank_zero`, `OAI.Lech.ReesRoot.scalarEuler_value` and `OAI.Lech.ReesRoot.scalarHomology_value`; the proof of `OAI.Lech.FiniteModuleCech.tensor_euler_rank_zero`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L019
import Definitions.Def_OAIQ032L020
import Definitions.Def_OAIQ032L021

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechConnectingIso
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.DoubleCech

section
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
omit [Fintype ι] [LinearOrder ι] in
lemma row_exact (p : ℕ)
    (h : ∀ s : powersetCard ι p,(AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).Acyclic) :
    (row R M F h₂ p).Acyclic := by
  intro q
  cases q with
  | zero =>
    apply ((row R M F h₂ p).exactAt_iff' (i:=0) (j:=0) (k:=1) (by simp) (by simp)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change ((row R M F h₂ p).d 0 1).hom x=0 at hx
    rw [row_d] at hx
    have hx0 : x=0 := by
      funext s
      have hs := ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).exactAt_iff'
        (i:=0) (j:=0) (k:=1) (by simp) (by simp)).mp (h s 0)
      rw [ShortComplex.moduleCat_exact_iff] at hs
      obtain ⟨y,hy⟩ := hs (x s) (by
        change ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).d 0 1).hom (x s)=0
        rw [AlternatingCech.sortedComplex_d]
        exact congrFun hx s)
      have hd := (AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).shape 0 0 (by simp)
      change ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).d 0 0).hom y=x s at hy
      rw [hd] at hy
      exact hy.symm
    exact ⟨0,by simp [hx0]⟩
  | succ q =>
    apply ((row R M F h₂ p).exactAt_iff' (i:=q) (j:=q+1) (k:=q+2) (by simp) (by simp)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change ((row R M F h₂ p).d (q+1) (q+2)).hom x=0 at hx
    rw [row_d] at hx
    have hs (s : powersetCard ι p) : ∃ y : AlternatingCech.sorted R M (F s.val) q,
        AlternatingCech.sortedDelta R M (F s.val) (h₂ s.val) q y=x s := by
      have he := ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).exactAt_iff'
        (i:=q) (j:=q+1) (k:=q+2) (by simp) (by simp)).mp (h s (q+1))
      rw [ShortComplex.moduleCat_exact_iff] at he
      obtain ⟨y,hy⟩ := he (x s) (by
        change ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).d (q+1) (q+2)).hom (x s)=0
        rw [AlternatingCech.sortedComplex_d]
        exact congrFun hx s)
      refine ⟨y,?_⟩
      change ((AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).d q (q+1)).hom y=x s at hy
      rw [AlternatingCech.sortedComplex_d] at hy
      exact hy
    choose y hy using hs
    refine ⟨y,?_⟩
    change ((row R M F h₂ p).d q (q+1)).hom y=x
    rw [row_d]
    exact funext hy
lemma row_bounded (p : ℕ) (hp : Fintype.card ι<p) : IsZero ((complex R M F h₁ h₂).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply Hom.ext
  funext q
  let : Subsingleton (term R M F p q) := term_zero_horizontal R M F p q hp
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (term R M F p q))).eq_of_src _ _
lemma column_bounded (q : ℕ) (hq : Fintype.card κ<q) : IsZero ((flip (complex R M F h₁ h₂)).X q) :=
  (row_bounded R M (fun t s => F s t) h₂ h₁ q hq).of_iso (columnIso R M F h₁ h₂ q)
 

def coverComparison
    (hr : ∀ p,0<p → ∀ s : powersetCard ι p,
      (AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).Acyclic)
    (hc : ∀ q,0<q → ∀ t : powersetCard κ q,
      (AlternatingCech.sortedComplex R M (fun s => F s t.val) (h₁ t.val)).Acyclic)
    (i : ℤ) :
    (((complex R M F h₁ h₂).X 0).extend ComplexShape.embeddingUpNat).homology i ≅
      (((flip (complex R M F h₁ h₂)).X 0).extend ComplexShape.embeddingUpNat).homology i :=
  ComplexExtension.natDoubleCoverIso (complex R M F h₁ h₂)
    (Fintype.card ι+1) (Fintype.card κ+1)
    (fun p hp => row_bounded R M F h₁ h₂ p (by omega))
    (fun q hq => column_bounded R M F h₁ h₂ q (by omega))
    (fun p hp => row_exact R M F h₂ p (hr p hp))
    (fun q hq j => (row_exact R M (fun t s => F s t) h₁ q (hc q hq) j).of_iso
      (columnIso R M F h₁ h₂ q).symm) i
end


open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
def rowZeroIso : ((complex R M F h₁ h₂).X 0) ≅
    AlternatingCech.sortedComplex R M (F ∅) (h₂ ∅) :=
  HomologicalComplex.Hom.isoOfComponents (fun q => (rowZeroEquiv R M F q).toModuleIso)
    (fun q r h => by
      obtain rfl : q+1=r := h
      rw [AlternatingCech.sortedComplex_d]
      change (ModuleCat.ofHom (rowZeroEquiv R M F q).toLinearMap) ≫ _ =
        (row R M F h₂ 0).d q (q+1) ≫ _
      rw [row_d]
      rfl)
def columnZeroIso : ((flip (complex R M F h₁ h₂)).X 0) ≅
    AlternatingCech.sortedComplex R M (fun s => F s ∅) (h₁ ∅) :=
  (columnIso R M F h₁ h₂ 0) ≪≫ rowZeroIso R M (fun t s => F s t) h₂ h₁
end Lech.DoubleCech


namespace Lech.DoubleCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))


def unaugmentedCoverComparison
    (hr : ∀ p,0<p → ∀ s : powersetCard ι p,
      (AlternatingCech.sortedComplex R M (F s.val) (h₂ s.val)).Acyclic)
    (hc : ∀ q,0<q → ∀ t : powersetCard κ q,
      (AlternatingCech.sortedComplex R M (fun s => F s t.val) (h₁ t.val)).Acyclic)
    (i : ℤ) :
    ((AlternatingCech.sortedComplex R M (AlternatingCech.zeroAugmentation R M (F ∅))
      (AlternatingCech.zeroAugmentation_mono R M (F ∅) (h₂ ∅))).extend ComplexShape.embeddingUpNat).homology i ≅
    ((AlternatingCech.sortedComplex R M (AlternatingCech.zeroAugmentation R M (fun s => F s ∅))
      (AlternatingCech.zeroAugmentation_mono R M (fun s => F s ∅) (h₁ ∅))).extend ComplexShape.embeddingUpNat).homology i := by
  let G := puncture R M F
  let g₁ := puncture_left_mono R M F h₁
  let g₂ := puncture_right_mono R M F h₂
  have gr : ∀ p,0<p → ∀ s : powersetCard ι p,(AlternatingCech.sortedComplex R M (G s.val) (g₂ s.val)).Acyclic := by
    intro p hp s
    have he := puncture_row R M F s.val (Finset.card_pos.mp (s.property.symm ▸ hp))
    simpa only [G,he] using hr p hp s
  have gc : ∀ q,0<q → ∀ t : powersetCard κ q,(AlternatingCech.sortedComplex R M (fun s => G s t.val) (g₁ t.val)).Acyclic := by
    intro q hq t
    have he := puncture_column R M F t.val (Finset.card_pos.mp (t.property.symm ▸ hq))
    simpa only [G,he] using hc q hq t
  have e := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
    ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso (rowZeroIso R M G g₁ g₂).symm) ≪≫
      coverComparison R M G g₁ g₂ gr gc i ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso (columnZeroIso R M G g₁ g₂))
  change ((AlternatingCech.sortedComplex R M (G ∅) (g₂ ∅)).extend ComplexShape.embeddingUpNat).homology i ≅
    ((AlternatingCech.sortedComplex R M (fun s => G s ∅) (g₁ ∅)).extend ComplexShape.embeddingUpNat).homology i at e
  have e₁ : G ∅=AlternatingCech.zeroAugmentation R M (F ∅) := by
    funext t
    simp only [G,puncture,AlternatingCech.zeroAugmentation,true_and]
  have e₂ : (fun s => G s ∅)=AlternatingCech.zeroAugmentation R M (fun s => F s ∅) := by
    funext s
    simp only [G,puncture,AlternatingCech.zeroAugmentation,and_true]
  simpa only [e₁,e₂] using e
end Lech.DoubleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains D n))
    (fun n => ModuleCat.ofHom (d D n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact d_square D n)

lemma complex_d (n : ℕ) : (complex D).d n (n+1) = ModuleCat.ofHom (d D n) := by
  unfold complex
  exact CochainComplex.of_d (fun j => ModuleCat.of R (cochains D j))
    (fun j => ModuleCat.ofHom (d D j)) n

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverOrdinaryPositive
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
abbrev targetCoeff : Fin (n+1) → Ambient R n := fun k => (ProductLaurent.binaryForm R n).coeff k
abbrev GridAmbient := AwayCover.Total (targetCoeff R n)
end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]



def Map.positiveComplex {D E : Diagram R ι} (φ : Map D E) :
    positiveComplex D ⟶ positiveComplex E :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (φ.cochains (n+1))) (fun n => by
    rw [positiveComplex_d,positiveComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (φ.cochains_d (n+1) f).symm)
end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesUlrichCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
  {D E : Diagram R ι}

def positiveIso (e : ∀ s,D.obj s ≃ₗ[R] E.obj s)
    (he : ∀ {s t : Finset ι} (hst : s ⊆ t) (x : D.obj s),
      e t ((D.res hst).hom x)=(E.res hst).hom (e s x)) :
    positiveComplex D ≅ positiveComplex E :=
  HomologicalComplex.Hom.isoOfComponents (fun q =>
    (LinearEquiv.piCongrRight (fun s : Set.powersetCard ι (q+1) => e s.val)).toModuleIso) (by
      intro q r h
      obtain rfl : q+1=r := h
      rw [positiveComplex_d,positiveComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext s
      symm
      change e s.val (∑ i : Fin (q+2),(-1:ℤ)^i.val •
        (D.res (AlternatingCech.delete_subset s i)).hom (x (AlternatingCech.delete s i))) = _
      rw [map_sum]
      simp only [map_zsmul]
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun y => (-1:ℤ)^i.val • y) (he (AlternatingCech.delete_subset s i) _))
end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechExact
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

variable [Fintype ι] [LinearOrder ι]

def positiveShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk φ.positiveComplex ψ.positiveComplex (by
    apply Hom.ext
    funext q
    apply ModuleCat.hom_ext
    exact Map.cochains_comp_zero φ ψ hzero (q+1))

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechIndexing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
variable (D : Diagram R ι)

lemma complex_zero (hD : IsZero (D.obj ∅)) : IsZero ((complex D).X 0) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun f g => funext fun s => ?_⟩
  have hs : s.val = ∅ := Finset.card_eq_zero.mp s.property
  have hz : IsZero (D.obj s.val) := hs ▸ hD
  exact (ModuleCat.subsingleton_of_isZero hz).elim (f s) (g s)

def positiveSuccScIso (q : ℕ) :
    (positiveComplex D).sc' q (q+1) (q+1+1) ≅
      (complex D).sc' (q+1) (q+1+1) (q+1+1+1) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',Iso.refl_hom,
          positiveComplex_d,complex_d]
        exact (Category.id_comp (ModuleCat.ofHom (d D (q+1)))).trans (Category.comp_id _).symm)
    (by simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',Iso.refl_hom,
          positiveComplex_d,complex_d]
        exact (Category.id_comp (ModuleCat.ofHom (d D (q+1+1)))).trans (Category.comp_id _).symm)

def positiveZeroScMap :
    (positiveComplex D).sc' 0 0 1 ⟶ (complex D).sc' 0 1 2 where
  τ₁ := 0
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor']
    exact zero_comp.trans (((positiveComplex D).shape 0 0 (by decide)).symm.trans
      (Category.comp_id _).symm)
  comm₂₃ := by
    simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',
      positiveComplex_d,complex_d]
    exact (Category.id_comp (ModuleCat.ofHom (d D 1))).trans (Category.comp_id _).symm

 

def positiveHomologyIso (hD : IsZero (D.obj ∅)) (q : ℕ) :
    (positiveComplex D).homology q ≅ (complex D).homology (q+1) := by
  cases q with
  | zero =>
      haveI : Epi (positiveZeroScMap D).τ₁ := (complex_zero D hD).epi _
      haveI : IsIso (positiveZeroScMap D).τ₂ := inferInstanceAs (IsIso (𝟙 _))
      haveI : Mono (positiveZeroScMap D).τ₃ := inferInstanceAs (Mono (𝟙 _))
      exact (positiveComplex D).homologyIsoSc' 0 0 1 (by simp) (by simp) ≪≫
        asIso (ShortComplex.homologyMap (positiveZeroScMap D)) ≪≫
          ((complex D).homologyIsoSc' 0 1 2 (by simp) (by simp)).symm
  | succ q =>
      exact (positiveComplex D).homologyIsoSc' q (q+1) (q+1+1) (by simp) (by simp) ≪≫
        ShortComplex.homologyMapIso (positiveSuccScIso D q) ≪≫
          ((complex D).homologyIsoSc' (q+1) (q+1+1) (q+1+1+1) (by simp) (by simp)).symm

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorCechEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]

 
def positiveZ (D : Diagram R ι) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (positiveComplex D).extend ComplexShape.embeddingUpNat


def tensorCech (F : CochainComplex (ModuleCat.{u} R) ℤ) (D : Diagram R ι) :=
  (TensorTotal.Right.functor F).obj (positiveZ D)

variable {D E G : Diagram R ι} (φ : Map D E) (ψ : Map E G)
  (hzero : ∀ s,φ.app s ≫ ψ.app s=0)


variable {I : Ideal R} (ell : TorsionLength I)

def tensorEuler (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ) (D : Diagram R ι) : ℝ :=
  (-1:ℝ)^h * finiteHomologyEuler ell (tensorCech F D) (-(h:ℤ)) (h+Fintype.card ι)

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCopies
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

def tensorCechMap (F : CochainComplex (ModuleCat.{u} R) ℤ)
    {D E : Diagram R ι} (φ : Map D E) : tensorCech F D ⟶ tensorCech F E :=
  (TensorTotal.Right.functor F).map (extendMap φ.positiveComplex ComplexShape.embeddingUpNat)

variable {I : Ideal R} (ell : TorsionLength I)

def copiesCongr {κ η : Type} (e : κ ≃ η) :
    positiveComplex (copiesDiagram D κ) ≅ positiveComplex (copiesDiagram D η) :=
  positiveIso (copiesReindex D e) (fun _ _ => rfl)

def copiesSuccIso (a : ℕ) : positiveComplex (copiesDiagram D (Fin (a+1))) ≅
    positiveComplex (prodDiagram D (copiesDiagram D (Fin a))) :=
  positiveIso (copiesSuccEquiv D a) (fun _ _ => rfl)

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarChartComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FilteredCech
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ j,z j∈I)

lemma diagram_fullD (t p : ℕ) :
    CechNormalization.fullD (diagram I z hz t) p=LocalizationCech.d z (term I z t) (restriction_mem I z hz t) p := by
  apply LinearMap.ext
  intro x
  funext a
  change (∑ j : Fin (p+1),(-1:R)^j.val •
    CarrierOperators.toFixed (diagram I z hz t) (CechNormalization.fullCarrier p)
      (FiniteCoverCech.intersection a) x (a ∘ j.succAbove))=_
  apply Finset.sum_congr rfl
  intro j hj
  change (-1:R)^j.val • (if h : _ then _ else _)=_
  have hj' : (CechNormalization.fullCarrier p).support (a ∘ j.succAbove)⊆
      FiniteCoverCech.intersection a := ActualCech.intersection_delete a j
  rw [dite_eq_left hj']
  rfl
end Lech.FilteredCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarCechComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
  {D E : Diagram R ι}

def positiveIsoOfNonempty (e : ∀ s (_hs : s.Nonempty),D.obj s ≃ₗ[R] E.obj s)
    (he : ∀ {s t : Finset ι} (hst : s⊆t) (hs : s.Nonempty) (ht : t.Nonempty) (x : D.obj s),
      e t ht ((D.res hst).hom x)=(E.res hst).hom (e s hs x)) :
    positiveComplex D ≅ positiveComplex E :=
  Hom.isoOfComponents (fun q =>
    (LinearEquiv.piCongrRight (fun s : Set.powersetCard ι (q+1) => e s.val (nonempty_card s))).toModuleIso) (by
      intro q r h
      obtain rfl : q+1=r := h
      rw [positiveComplex_d,positiveComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext s
      symm
      change e s.val (nonempty_card s) (∑ j : Fin (q+2),(-1:ℤ)^j.val •
        (D.res (AlternatingCech.delete_subset s j)).hom (x (AlternatingCech.delete s j)))=_
      rw [map_sum]
      simp only [map_zsmul]
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun y => (-1:ℤ)^j.val • y)
        (he (AlternatingCech.delete_subset s j) (nonempty_card _) (nonempty_card _) _))
end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarCechShift
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ j,z j∈I)

abbrev ordinaryPositive (t : ℕ) := CechNormalization.fullPositive (diagram I z hz t)

def shiftXIso (t p : ℕ) :
    ((shiftedPositive I z hz t).restriction ComplexShape.embeddingUpNat).X p ≅ (ordinaryPositive I z hz t).X p where
  hom := (p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).hom
  inv := (p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).inv
  hom_inv_id := by
    change ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).hom) ≫
      ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).inv) =
        𝟙 ((positive I z hz t).X ((p+1:ℕ):ℤ))
    simp only [Linear.units_smul_comp,Linear.comp_units_smul,smul_smul,Int.units_mul_self,one_smul,Iso.hom_inv_id]
  inv_hom_id := by
    change ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).inv) ≫
      ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).hom) =
        𝟙 ((complex I z hz t).X (p+1))
    simp only [Linear.units_smul_comp,Linear.comp_units_smul,smul_smul,Int.units_mul_self,one_smul,Iso.inv_hom_id]

lemma shiftXIso_d (t p : ℕ) :
    (shiftXIso I z hz t p).hom ≫ (ordinaryPositive I z hz t).d p (p+1)=
    ((shiftedPositive I z hz t).restriction ComplexShape.embeddingUpNat).d p (p+1) ≫
      (shiftXIso I z hz t (p+1)).hom := by
  rw [CechNormalization.fullPositive_d]
  dsimp only [shiftXIso, restriction, shiftedPositive]
  rw [CochainComplex.shiftFunctor_obj_d']
  rw [diagram_fullD]
  change ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) _).hom) ≫
      ModuleCat.ofHom (LocalizationCech.d z (term I z t) (restriction_mem I z hz t) (p+1)) =
    ((1:ℤ).negOnePow • (positive I z hz t).d ((p+1:ℕ):ℤ) ((p+1+1:ℕ):ℤ)) ≫
      (((p+1:ℕ):ℤ).negOnePow • (positiveXIso I z hz t (p+1+1) _).hom)
  rw [←complex_d I z hz t (p+1)]
  change ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) _).hom) ≫ (complex I z hz t).d (p+1) (p+1+1)=
    ((1:ℤ).negOnePow • (positive I z hz t).d ((p+1:ℕ):ℤ) ((p+1+1:ℕ):ℤ)) ≫
      (((p+1:ℕ):ℤ).negOnePow • (positiveXIso I z hz t (p+1+1) _).hom)
  simp only [Linear.units_smul_comp,Linear.comp_units_smul,smul_smul]
  rw [positiveXIso_d]
  have he : ((p+1:ℕ):ℤ).negOnePow*(1:ℤ).negOnePow=(p:ℤ).negOnePow := by
    rw [Nat.cast_add,Nat.cast_one,Int.negOnePow_add,mul_assoc,Int.units_mul_self,mul_one]
  rw [he]

def shiftRestrictionIso (t : ℕ) :
    (shiftedPositive I z hz t).restriction ComplexShape.embeddingUpNat ≅ ordinaryPositive I z hz t :=
  Hom.isoOfComponents (shiftXIso I z hz t) (fun p q hpq => by
    obtain rfl : p+1=q := hpq
    exact shiftXIso_d I z hz t p)

lemma shiftRestriction_hasLift (t : ℕ) :
    ComplexShape.embeddingUpNat.HasLift (shiftRestrictionIso I z hz t).hom := by
  intro j hj i hi
  have hneg : i < 0 := by
    by_contra h
    have hnonneg : 0 ≤ i := by omega
    exact hj.notMem hi i.toNat (by change (i.toNat:ℤ)=i; exact Int.toNat_of_nonneg hnonneg)
  have hzero : IsZero ((shiftedPositive I z hz t).X i) :=
    positive_boundedBelow I z hz t (i+1) (by omega)
  exact hzero.eq_of_src _ _

def shiftToOrdinary (t : ℕ) : shiftedPositive I z hz t ⟶
    (ordinaryPositive I z hz t).extend ComplexShape.embeddingUpNat :=
  ComplexShape.embeddingUpNat.liftExtend (shiftRestrictionIso I z hz t).hom (shiftRestriction_hasLift I z hz t)

instance shiftToOrdinary_isIso (t : ℕ) : IsIso (shiftToOrdinary I z hz t) := by
  have hf (i : ℤ) : IsIso ((shiftToOrdinary I z hz t).f i) := by
    by_cases hi : 0 ≤ i
    · exact (ComplexShape.embeddingUpNat.isIso_liftExtend_f_iff _ _
        (i:=i.toNat) (i':=i) (by change (i.toNat:ℤ)=i; exact Int.toNat_of_nonneg hi)).mpr inferInstance
    · apply (positive_boundedBelow I z hz t (i+1) (by omega)).isIso
      exact (ordinaryPositive I z hz t).isZero_extend_X ComplexShape.embeddingUpNat i
        (fun p hp => by change (p:ℤ)=i at hp; omega)
  exact Hom.isIso_of_components (shiftToOrdinary I z hz t)

def shiftOrdinaryIso (t : ℕ) : shiftedPositive I z hz t ≅
    (ordinaryPositive I z hz t).extend ComplexShape.embeddingUpNat := asIso (shiftToOrdinary I z hz t)
end Lech.FilteredCech

end

end OAI
end


