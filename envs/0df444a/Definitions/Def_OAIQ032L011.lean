-- Prove2me | Definitions.Def_OAIQ032L011
-- name    : OAIQ032L011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:49:50.997142+00:00
-- url     : https://prove2.me/theorems/259f6a44-70e7-40d3-98e5-8b2c9ba65f4b
-- title:
--   Definitions bundle OAIQ032L011 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 104 declarations of OpenAI's Lean: 44 definitions, 4 instances and 56 theorems. The definitions and types are `OAI.Lech.BicomplexTotal.diagonal`, `OAI.Lech.BicomplexTotal.outOfSingle`, `OAI.Lech.BicomplexTotal.positiveRows`, `OAI.Lech.BicomplexTotal.singleXIso`, `OAI.Lech.BinaryChange.backward`, `OAI.Lech.BinaryChange.forward`, `OAI.Lech.BinaryChange.normalized`, `OAI.Lech.CechNormalization.AgreeOn`, `OAI.Lech.CechNormalization.altify`, `OAI.Lech.CechNormalization.expansion`, `OAI.Lech.CechNormalization.fullCarrier`, `OAI.Lech.CechNormalization.fullCochains`, `OAI.Lech.CechNormalization.fullSort`, `OAI.Lech.CechNormalization.normalize`, `OAI.Lech.CechNormalization.sortOp`, `OAI.Lech.CechNormalization.sortedRestriction`, `OAI.Lech.CechNormalization.tensorEquivalence`, `OAI.Lech.CoefficientReduction.chartMap`, `OAI.Lech.ComplexExtension.columnEvalIso`, `OAI.Lech.ComplexExtension.columnIso`, `OAI.Lech.ComplexExtension.doubleExtend`, `OAI.Lech.ComplexExtension.rowIso`, `OAI.Lech.DoubleCech.horizontal`, `OAI.Lech.DoubleCech.rowZeroEquiv`, `OAI.Lech.DoubleCech.vertical`, `OAI.Lech.FactorDescent.U`, `OAI.Lech.FactorDescent.canonical`, `OAI.Lech.FactorDescent.coefficients`, `OAI.Lech.FactorDescent.includeT`, `OAI.Lech.FactorDescent.instAlgebraS`, `OAI.Lech.FactorDescent.invariantMap`, `OAI.Lech.FactorDescent.right`, `OAI.Lech.FiniteModuleCech.d`, `OAI.Lech.RootCoaction.T`, `OAI.Lech.RootCoaction.coord`, `OAI.Lech.RootCoaction.hom`, `OAI.Lech.RootCoaction.instAlgebraS`, `OAI.Lech.RootCoaction.right`, `OAI.Lech.RootCoaction.roots`, `OAI.Lech.RootCoaction.unit` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_CechCarrierOperators`, `Multiplicity_CechNormalization`, `Multiplicity_CechNormalizationRows`, `Multiplicity_CompleteNoetherian`, `Multiplicity_FiniteComplexTopInclusion`, `Multiplicity_FiniteModuleCech`, `Multiplicity_LechConnectingIso`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_LechTorsionOf`, `Multiplicity_NativeDescentCanonicalAlg`, `Multiplicity_PrimitiveChartFaithfullyFlat`, `Multiplicity_ProductSourceCoverFaceSlice`, `Multiplicity_ProjectiveReduction`, `Multiplicity_RootBundleChartsDenominator`, `Multiplicity_RootCoactionT`, `Multiplicity_RootInvariantsWeightZero`, `Multiplicity_StandardFactorChartsL`, `Multiplicity_TensorCechHomotopy`, `Multiplicity_TotalExact`.
--
--   **Imports.** It imports the bundles `OAIQ032L000`, `OAIQ032L001`, `OAIQ032L002` and `OAIQ032L003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L019`, `OAIQ032L020`, `OAIQ032L021`, `OAIQ032L022` and `OAIQ032L023`; the proofs of `OAI.Lech.SourceGraded.acyclicity_finite_torsion` and `OAI.Lech.ordinaryPower_stableImage_isoMod`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L001
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L003

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.Homogeneous.module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech.FiniteComplex

section

variable {C : Type*} [Category C] [Abelian C]
variable (F : CochainComplex C ℤ) (n : ℤ)
  (hn : ∀ i, n < i → IsZero (F.X i))


theorem devissage (Q : ObjectProperty (CochainComplex C ℤ))
    [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ i, (S.map (eval C (ComplexShape.up ℤ) i)).Splitting) →
      Q S.X₁ → Q S.X₃ → Q S.X₂)
    (m : ℤ) (N : ℕ) (F : CochainComplex C ℤ)
    (hb : ∀ i, i < m ∨ m + N ≤ i → IsZero (F.X i))
    (hg : ∀ i, Q ((single C (ComplexShape.up ℤ) i).obj (F.X i))) : Q F := by
  induction N generalizing F with
  | zero =>
    apply Q.prop_of_isZero
    exact isZero_of_X F (fun i => hb i (by omega))
  | succ N ih =>
    let n : ℤ := m + N
    have hn : ∀ i, n < i → IsZero (F.X i) := fun i hi => hb i (by
      right
      dsimp [n] at hi
      exact_mod_cast (by omega : m + ((N : ℤ) + 1) ≤ i))
    let D := dropTop F n hn
    have hbD : ∀ i, i < m ∨ m + (N : ℤ) ≤ i → IsZero (D.X i) := by
      intro i hi
      by_cases hin : i = n
      · subst i
        exact dropTop_X_top F n hn
      · exact (hb i (by dsimp [n] at hin; omega)).of_iso (dropTopXIso F n hn i hin).symm
    have hgD : ∀ i, Q ((single C (ComplexShape.up ℤ) i).obj (D.X i)) := by
      intro i
      by_cases hin : i = n
      · subst i
        exact Q.prop_of_isZero ((single C (ComplexShape.up ℤ) n).map_isZero
          (dropTop_X_top F n hn))
      · exact Q.prop_of_iso ((single C (ComplexShape.up ℤ) i).mapIso
          (dropTopXIso F n hn i hin)) (hg i)
    exact hQ (topShortComplex F n hn) (topSplitting F n hn) (hg n) (ih D hbD hgD)


end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
lemma homology_devissage_to (P : ObjectProperty D) [P.IsSerreClass]
    (T : CochainComplex C ℤ ⥤ CochainComplex D ℤ) [T.Additive]
    (hT : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ j, (S.map (eval C (ComplexShape.up ℤ) j)).Splitting) →
      ∀ j, ((S.map T).map (eval D (ComplexShape.up ℤ) j)).Splitting)
    (m : ℤ) (N : ℕ) (F : CochainComplex C ℤ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (F.X j))
    (hg : ∀ j, P ((T.obj ((single C (ComplexShape.up ℤ) j).obj
      (F.X j))).homology i)) : P ((T.obj F).homology i) := by
  let Q := P.inverseImage (T ⋙ homologyFunctor D (ComplexShape.up ℤ) i)
  apply devissage Q ?_ m N F hb hg
  intro S hs h₁ h₃
  have hS : (S.map T).ShortExact :=
    shortExact_of_degreewise_shortExact _ (fun j => (hT S hs j).shortExact)
  exact P.prop_X₂_of_exact (hS.homology_exact₂ i) h₁ h₃
end Lech.FiniteComplex


namespace Lech.BicomplexTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable {F G H : Double (R := R)}
lemma devissage (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (m : ℤ) (N : ℕ) (F : Double (R := R)) (i : ℤ)
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (F.X j))
    (hg : ∀ j, P (((functor (R := R)).obj
      ((single (Row (R := R)) (.up ℤ) j).obj (F.X j))).homology i)) :
    P (((functor (R := R)).obj F).homology i) :=
  FiniteComplex.homology_devissage_to P functor splitting m N F i hb hg
end Lech.BicomplexTotal

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
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

instance source_graded (h : ℕ) : GradedAlgebra (sourceGrade I h) := inferInstanceAs
  (GradedAlgebra (fun n => (homogeneousSubmodule (Fin h) (R ⧸ I) n).restrictScalars R))
end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverFaceSlice
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
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))

def vertical (p q : ℕ) : term R M F p q →ₗ[R] term R M F p (q+1) where
  toFun f s := AlternatingCech.sortedDelta R M (F s.val) (h₂ s.val) q (f s)
  map_add' f g := by funext s;exact map_add _ (f s) (g s)
  map_smul' r f := by funext s;exact map_smul _ r (f s)
def horizontal (p q : ℕ) : term R M F p q →ₗ[R] term R M F (p+1) q where
  toFun f s t := AlternatingCech.sortedDelta R M (fun s => F s t.val) (h₁ t.val) p
    (fun s => f s t) s
  map_add' f g := by funext s t; exact congrFun (map_add _ (fun s => f s t) (fun s => g s t)) s
  map_smul' r f := by funext s t;exact congrFun ((AlternatingCech.sortedDelta R M (fun s => F s t.val) (h₁ t.val) p).map_smul r (fun s => f s t)) s
omit [Fintype ι] [Fintype κ] in
lemma horizontal_vertical (p q : ℕ) (f : term R M F p q) :
    vertical R M F h₂ (p+1) q (horizontal R M F h₁ p q f)=
      horizontal R M F h₁ p (q+1) (vertical R M F h₂ p q f) := by
  ext s t
  simp only [vertical,horizontal,AlternatingCech.sortedDelta,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,map_zsmul,Finset.smul_sum,Submodule.coe_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

end Lech.DoubleCech


namespace Lech.BicomplexTotal

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (F : Row (R := R))
def outOfSingle (i : ℤ) : (totalSingleZero F).X i ⟶ F.X i :=
  totalDesc (singleZero F) (fun p q hpq => if hp : p=0 then
    have hq : q=i := by change p+q=i at hpq; omega
    (singleObjXIsoOfEq (.up ℤ) 0 F p hp).hom.f q ≫ (F.XIsoOfEq hq).hom
    else 0)
lemma into_out_single (i : ℤ) : intoSingle F i ≫ outOfSingle F i=𝟙 _ := by
  simp only [intoSingle,outOfSingle,Category.assoc,ι_totalDesc,dite_true,
    XIsoOfEq_rfl,Iso.refl_hom,Category.comp_id]
  rw [←HomologicalComplex.comp_f]
  simp only [singleObjXSelf,Iso.inv_hom_id,HomologicalComplex.id_f]
lemma out_into_single (i : ℤ) : outOfSingle F i ≫ intoSingle F i=𝟙 _ := by
  apply total.hom_ext
  intro p q hpq
  by_cases hp : p=0
  · subst p
    have hq : q=i := by change 0+q=i at hpq; omega
    subst q
    simp only [outOfSingle,ι_totalDesc_assoc,dite_true,XIsoOfEq_rfl,
      Iso.refl_hom,Category.comp_id]
    dsimp only [intoSingle]
    rw [←Category.assoc,←HomologicalComplex.comp_f]
    simp only [singleObjXSelf,Iso.hom_inv_id,HomologicalComplex.id_f,Category.id_comp]
  · have hzero := (eval (ModuleCat.{u} R) (.up ℤ) q).map_isZero
      (isZero_single_obj_X (.up ℤ) 0 F p hp)
    exact hzero.eq_of_src _ _
def singleXIso (i : ℤ) : F.X i ≅ (totalSingleZero F).X i where
  hom := intoSingle F i
  inv := outOfSingle F i
  hom_inv_id := into_out_single F i
  inv_hom_id := out_into_single F i
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
end Lech.BicomplexTotal


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechConnectingIso
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


namespace Lech.BicomplexTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (K : Double (R := R)) (N : ℕ)
  (hb : ∀ j, j < 0 ∨ (N:ℤ) ≤ j → IsZero (K.X j))
  (hr : ∀ j, 0<j → ∀ i, IsZero ((K.X j).homology i))
def positiveRows : Double (R := R) :=
  FiniteComplex.dropBottom K 0 (fun j hj => hb j (Or.inl hj))
lemma positiveRows_bounded (j : ℤ) (hj : j<0 ∨ (N:ℤ)≤j) :
    IsZero ((positiveRows K N hb).X j) := by
  by_cases hj0 : j=0
  · subst j
    exact FiniteComplex.dropBottom_X_bottom K 0 _
  · exact (hb j hj).of_iso (FiniteComplex.dropBottomXIso K 0 _ j hj0)
include hr in
lemma positiveRows_acyclic (j i : ℤ) :
    IsZero (((positiveRows K N hb).X j).homology i) := by
  by_cases hj : j≤0
  · apply (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).map_isZero
    exact FiniteComplex.dropBottom_boundedBelow K 0 _ j (by omega)
  · exact (hr j (by omega) i).of_iso
      ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
        (FiniteComplex.dropBottomXIso K 0 _ j (by omega)))
lemma bottom_total_shortExact :
    ((FiniteComplex.bottomShortComplex K 0 (fun j hj => hb j (Or.inl hj))).map
      (functor (R := R))).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun i =>
    (splitting _ (FiniteComplex.bottomSplitting K 0 _) i).shortExact)
end Lech.BicomplexTotal


namespace Lech.ComplexExtension
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (K : NatDouble (R := R))
 
def doubleExtend : BicomplexTotal.Double (R := R) :=
  ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj
    (K.extend ComplexShape.embeddingUpNat)
def rowIso (n : ℕ) : (doubleExtend K).X (n:ℤ) ≅ (K.X n).extend ComplexShape.embeddingUpNat :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
    (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
def columnEvalIso (n : ℕ) : (flip (doubleExtend K)).X (n:ℤ) ≅
    ((eval (ModuleCat.{u} R) (.up ℕ) n).mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat) :=
  Hom.isoOfComponents (fun i => ((K.extend ComplexShape.embeddingUpNat).X i).extendXIso
    ComplexShape.embeddingUpNat (i := n) rfl) (fun i j _ => by
      change _ = (extendMap ((K.extend ComplexShape.embeddingUpNat).d i j)
        ComplexShape.embeddingUpNat).f (n:ℤ) ≫ _
      erw [extendMap_f _ ComplexShape.embeddingUpNat (i := n) (show ComplexShape.embeddingUpNat.f n=(n:ℤ) from rfl)]
      erw [Category.assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id]
      rfl)
def columnIso (n : ℕ) : (flip (doubleExtend K)).X (n:ℤ) ≅
    ((flip K).X n).extend ComplexShape.embeddingUpNat :=
  columnEvalIso K n ≪≫ mapExtendIso (eval (ModuleCat.{u} R) (.up ℕ) n) K
lemma row_negative (i : ℤ) (hi : i < 0) : IsZero ((doubleExtend K).X i) := by
  apply (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map_isZero
  apply K.isZero_extend_X
  intro n hn
  change (n:ℤ)=i at hn
  omega
lemma column_negative (i : ℤ) (hi : i < 0) : IsZero ((flip (doubleExtend K)).X i) := by
  apply FiniteComplex.isZero_of_X
  intro j
  apply ((K.extend ComplexShape.embeddingUpNat).X j).isZero_extend_X
  intro n hn
  change (n:ℤ)=i at hn
  omega
variable (N M : ℕ) (hrb : ∀ n,N≤n → IsZero (K.X n))
  (hcb : ∀ n,M≤n → IsZero ((flip K).X n))
  (hr : ∀ n,0<n → (K.X n).Acyclic) (hc : ∀ n,0<n → ((flip K).X n).Acyclic)
include hrb in
lemma row_bounded (i : ℤ) (hi : i < 0 ∨ (N:ℤ) ≤ i) : IsZero ((doubleExtend K).X i) := by
  by_cases hi0 : i < 0
  · exact row_negative K i hi0
  obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map_isZero
    (hrb n (by omega))).of_iso (rowIso K n)
include hcb in
lemma column_bounded (i : ℤ) (hi : i < 0 ∨ (M:ℤ) ≤ i) : IsZero ((flip (doubleExtend K)).X i) := by
  by_cases hi0 : i < 0
  · exact column_negative K i hi0
  obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map_isZero
    (hcb n (by omega))).of_iso (columnIso K n)
include hr in
lemma row_positive (i : ℤ) (hi : 0 < i) (j : ℤ) : IsZero (((doubleExtend K).X i).homology j) := by
  obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact ((extended_acyclic (K.X n) (hr n (by omega)) j).isZero_homology).of_iso
    ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) j).mapIso (rowIso K n))
include hc in
lemma column_positive (i : ℤ) (hi : 0 < i) (j : ℤ) : IsZero (((flip (doubleExtend K)).X i).homology j) := by
  obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact ((extended_acyclic ((flip K).X n) (hc n (by omega)) j).isZero_homology).of_iso
    ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) j).mapIso (columnIso K n))


end Lech.ComplexExtension


namespace Lech.DoubleCech


open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))


def rowZeroEquiv (q : ℕ) : term R M F 0 q ≃ₗ[R] AlternatingCech.sorted R M (F ∅) q where
  toFun f := f emptyIndex
  invFun f s := (zeroIndex_eq s).symm ▸ f
  left_inv f := by funext s;cases zeroIndex_eq s;rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' r f := rfl
end Lech.DoubleCech


namespace Lech.DoubleCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))


include h₁ in
omit [Fintype ι] [Fintype κ] in
lemma puncture_left_mono (t : Finset κ) : Monotone (fun s => puncture R M F s t) := by
  intro s s' hs
  by_cases he : s=∅ ∧ t=∅
  · simp only [puncture,ite_eq_left he,bot_le]
  · have he' : ¬(s'=∅ ∧ t=∅) := by
      rintro ⟨rfl,ht⟩
      exact he ⟨Finset.subset_empty.mp hs,ht⟩
    simpa only [puncture,ite_eq_right he,ite_eq_right he'] using h₁ t hs
include h₂ in
omit [Fintype ι] [Fintype κ] in
lemma puncture_right_mono (s : Finset ι) : Monotone (puncture R M F s) := by
  intro t t' ht
  by_cases he : s=∅ ∧ t=∅
  · simp only [puncture,ite_eq_left he,bot_le]
  · have he' : ¬(s=∅ ∧ t'=∅) := by
      rintro ⟨hs,rfl⟩
      exact he ⟨hs,Finset.subset_empty.mp ht⟩
    simpa only [puncture,ite_eq_right he,ite_eq_right he'] using h₂ s ht
end Lech.DoubleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleCech
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

def d (n : ℕ) : cochains D n →ₗ[R] cochains D (n+1) where
  toFun f s := ∑ i : Fin (n+1), (-1:ℤ)^i.val •
    (D.res (delete_subset s i)).hom (f (delete s i))
  map_add' f g := by
    funext s
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _



end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechNormalizationRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open Set FiniteCoverCech
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
  {ι : Type} [Fintype ι] [LinearOrder ι]

def sortedRestriction (p : ℕ) : Row M (ι:=ι) p →ₗ[R] (powersetCard ι p → M) where
  toFun f s := f (s.val.orderEmbOfFin s.property)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def altify (p : ℕ) : Row M (ι:=ι) p →ₗ[R] AlternatingCech.Alt R M (ι:=ι) p :=
  (AlternatingCech.sortedCoordinates R M p).symm.toLinearMap.comp (sortedRestriction R M p)

def normalize (p : ℕ) : Row M (ι:=ι) p →ₗ[R] Row M (ι:=ι) p :=
  (AlternatingCech.evaluation R M p).comp (altify R M p)

lemma normalize_perm (p : ℕ) (f : Row M (ι:=ι) p) (a : Fin p → ι) (σ : Equiv.Perm (Fin p)) :
    normalize R M p f (a ∘ σ)=(Equiv.Perm.sign σ:ℤ) • normalize R M p f a := by
  change altify R M p f ((fun i => AlternatingCech.basis R (a i)) ∘ σ)=_
  exact (altify R M p f).map_perm _ σ

lemma normalize_degenerate (p : ℕ) (f : Row M (ι:=ι) p) (a : Fin p → ι)
    (ha : ¬Function.Injective a) : normalize R M p f a=0 := by
  apply (altify R M p f).map_eq_zero_of_not_injective
  intro h
  apply ha
  intro i j hij
  exact h (congrArg (AlternatingCech.basis R) hij)

def AgreeOn (S : Finset ι) (p : ℕ) (f g : Row M (ι:=ι) p) : Prop :=
  ∀ a,intersection a ⊆ S → f a=g a

end Lech.CechNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCarrierOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open Set FiniteCoverCech CarrierOperators
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]

abbrev fullCarrier (p : ℕ) : Carrier ι := ⟨Fin p → ι,intersection⟩

def sortOp (p : ℕ) : Op (R:=R) (fullCarrier (ι:=ι) p) (sortedCarrier p) where
  app M := sortedRestriction R M p
  natural _ _ := rfl
  locality M S f g h s hs := by
    apply h
    change intersection (s.val.orderEmbOfFin s.property)⊆S
    intro index hindex
    obtain ⟨position,_,rfl⟩ := Finset.mem_image.mp hindex
    exact hs (s.val.orderEmbOfFin_mem s.property position)

variable (R) (M : Type u) [AddCommGroup M] [Module R M]

def expansion (p : ℕ) : (powersetCard ι p → M) →ₗ[R] Row M (ι:=ι) p :=
  (AlternatingCech.evaluation R M p).comp (AlternatingCech.sortedCoordinates R M p).symm.toLinearMap

lemma expansion_perm (p : ℕ) (f : powersetCard ι p → M) (a : Fin p → ι) (σ : Equiv.Perm (Fin p)) :
    expansion R M p f (a ∘ σ)=(Equiv.Perm.sign σ:ℤ) • expansion R M p f a := by
  change ((AlternatingCech.sortedCoordinates R M p).symm f)
    ((fun i => AlternatingCech.basis R (a i)) ∘ σ)=_
  exact ((AlternatingCech.sortedCoordinates R M p).symm f).map_perm _ σ

lemma expansion_degenerate (p : ℕ) (f : powersetCard ι p → M) (a : Fin p → ι)
    (ha : ¬Function.Injective a) : expansion R M p f a=0 := by
  apply ((AlternatingCech.sortedCoordinates R M p).symm f).map_eq_zero_of_not_injective
  intro h
  apply ha
  intro i j hij
  exact h (congrArg (AlternatingCech.basis R) hij)

end Lech.CechNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
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


namespace Lech.UniversalSplitting
open Polynomial
universe u

attribute [instance] Data.ring Data.algebra


variable {R : Type u} [CommRing R] {n : ℕ} {f : R[X]}

lemma Data.hom_ext (d : Data R n f) {T : Type u} [CommRing T] [Algebra R T]
    (φ ψ : d.S →ₐ[R] T) (h : ∀ i, φ (d.roots i)=ψ (d.roots i)) : φ=ψ := by
  have hfac : f.map (algebraMap R T)=∏ i, (Polynomial.X-C (ψ (d.roots i))) := by
    have he := congrArg (Polynomial.map ψ.toRingHom) d.factorization
    simpa only [Polynomial.map_map, AlgHom.comp_algebraMap, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using he
  obtain ⟨a, _, ha⟩ := d.universal T (fun i => ψ (d.roots i)) hfac
  exact (ha φ h).trans (ha ψ (fun _ => rfl)).symm


end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimitiveChartFaithfullyFlat
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


namespace Lech.BinaryChange
open Polynomial
universe u
variable {B : Type u} [CommRing B]

def forward (t : B) : Binary (B := B) →ₐ[B] Binary (B := B) :=
  MvPolynomial.aeval ![MvPolynomial.C t*MvPolynomial.X 0+MvPolynomial.X 1,
    MvPolynomial.X 0]

def backward (t : B) : Binary (B := B) →ₐ[B] Binary (B := B) :=
  MvPolynomial.aeval ![MvPolynomial.X 1,
    MvPolynomial.X 0-MvPolynomial.C t*MvPolynomial.X 1]

lemma backward_forward (t : B) : (backward t).comp (forward t)=AlgHom.id B _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [forward,backward]

lemma forward_homogeneous {p : Binary (B := B)} {n : ℕ}
    (hp : p.IsHomogeneous n) (t : B) : ((forward t) p).IsHomogeneous n := by
  have hx : ∀ i : Fin 2,
      (![MvPolynomial.C t*MvPolynomial.X 0+MvPolynomial.X 1,
        MvPolynomial.X 0] i : Binary (B := B)).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · simpa using ((MvPolynomial.isHomogeneous_X (R := B) 0).C_mul t).add
        (MvPolynomial.isHomogeneous_X (R := B) 1)
    · exact MvPolynomial.isHomogeneous_X (R := B) 0
  simpa only [one_mul,forward] using hp.aeval _ hx

lemma transform_degree (f : B[X]) (n : ℕ) (t : B) :
    (transform f n t).natDegree≤n := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact term_degree t _ (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

lemma transform_top (f : B[X]) (n : ℕ) (t : B) (hn : f.natDegree≤n) :
    (transform f n t).coeff n=f.eval t := by
  rw [transform,finsetSum_coeff,eval_eq_sum_range' (Nat.lt_succ_iff.mpr hn)]
  apply Finset.sum_congr rfl
  intro k hk
  exact term_coeff t _ (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

lemma transform_eq_aeval (f : B[X]) (n : ℕ) (t : B) :
    transform f n t = MvPolynomial.aeval ![C t*Polynomial.X+1,Polynomial.X] (f.homogenize n) := by
  classical
  rw [Polynomial.homogenize, map_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k _
  simp [MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two,
    mul_assoc]

lemma homogenize_transform (f : B[X]) (n : ℕ) (t : B) :
    (transform f n t).homogenize n=(forward t) (f.homogenize n) := by
  apply homogenize_eq_of_isHomogeneous (forward_homogeneous (isHomogeneous_homogenize f) t)
  have he : (MvPolynomial.aeval ![Polynomial.X,1]).comp (forward t) =
      MvPolynomial.aeval ![C t*Polynomial.X+1,Polynomial.X] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [forward]
  rw [transform_eq_aeval]
  exact DFunLike.congr_fun he (f.homogenize n)

def normalized (f : B[X]) (n : ℕ) (t : B) (v : Bˣ) : B[X] :=
  C (↑v⁻¹ : B)*transform f n t

lemma normalized_top (f : B[X]) {n : ℕ} (t : B) (v : Bˣ)
    (hn : f.natDegree≤n) (hv : f.eval t=(v : B)) :
    (normalized f n t v).coeff n=1 := by
  rw [normalized,coeff_C_mul,transform_top f n t hn,hv]
  exact v.inv_mul



lemma binary_factorization (f : B[X]) (n : ℕ) (t : B) (v : Bˣ) (rs : Fin n → B)
    (hs : normalized f n t v=∏ i, (Polynomial.X-C (rs i))) :
    f.homogenize n=MvPolynomial.C (v : B)*∏ i,
      (MvPolynomial.C (-rs i)*MvPolynomial.X 0+
        MvPolynomial.C (1+t*rs i)*MvPolynomial.X 1) := by
  classical
  have hh : (normalized f n t v).homogenize n=
      ∏ i : Fin n, (MvPolynomial.X 0-MvPolynomial.C (rs i)*MvPolynomial.X 1) := by
    rw [hs]
    have hp := homogenize_finsetProd (s := Finset.univ) (p := fun i : Fin n => Polynomial.X-C (rs i))
      (n := fun _ => 1) (fun _ _ => natDegree_X_sub_C_le _)
    simpa using hp
  have hmul : C (v : B)*normalized f n t v=transform f n t := by
    simp [normalized,← mul_assoc,← C_mul]
  have hc := congrArg (fun p : B[X] => p.homogenize n) hmul
  rw [homogenize_C_mul,hh,homogenize_transform] at hc
  have hb := congrArg (backward t) hc
  have hinv : (backward t) ((forward t) (f.homogenize n))=f.homogenize n :=
    DFunLike.congr_fun (backward_forward t) (f.homogenize n)
  rw [hinv] at hb
  rw [← hb]
  simp only [map_mul,map_prod]
  congr 1
  · simp [backward]
  · apply Finset.prod_congr rfl
    intro i _
    simp only [map_sub,map_mul,backward,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
      Matrix.cons_val_zero,Matrix.cons_val_one,
      MvPolynomial.C_neg,MvPolynomial.C_add,map_one,MvPolynomial.algebraMap_eq]
    ring

end Lech.BinaryChange


namespace Lech.BinaryCover
open Polynomial
universe u

lemma map_transform {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (f : A[X]) (n : ℕ) (t : A) :
    (BinaryChange.transform f n t).map φ=
      BinaryChange.transform (f.map φ) n (φ t) := by
  simp [BinaryChange.transform,Polynomial.map_sum]

lemma map_normalized {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (f : A[X]) (n : ℕ) (t : A) (v : Aˣ) :
    (BinaryChange.normalized f n t v).map φ=
      BinaryChange.normalized (f.map φ) n (φ t) (Units.map φ v) := by
  simp [BinaryChange.normalized,map_transform]



attribute [instance] Data.ring Data.algebra Data.chartAlgebra Data.tower

end Lech.BinaryCover


namespace Lech.RootTransitions
open Polynomial
universe u
variable {B : Type u} [CommRing B]

lemma value_product (f : B[X]) {n : ℕ} (hn : f.natDegree≤n)
    (t u : B) (v : Bˣ) (rs : Fin n → B)
    (hs : BinaryChange.normalized f n t v=∏ i, (Polynomial.X-C (rs i))) :
    f.eval u=(v:B)*∏ i, (1+(t-u)*rs i) := by
  classical
  have h := congrArg (MvPolynomial.aeval ![u,1])
    (BinaryChange.binary_factorization f n t v rs hs)
  rw [aeval_homogenize_of_eq_one hn ![u,1] (by simp)] at h
  have h' : f.eval u=(v:B)*∏ i, (-rs i*u+(1+t*rs i)) := by
    simpa using h
  rw [h']
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma denominator_isUnit (f : B[X]) {n : ℕ} (hn : f.natDegree≤n)
    (t u : B) (v w : Bˣ) (rs : Fin n → B)
    (hs : BinaryChange.normalized f n t v=∏ i, (Polynomial.X-C (rs i)))
    (hw : f.eval u=(w:B)) (i : Fin n) : IsUnit (1+(t-u)*rs i) := by
  have h := value_product f hn t u v rs hs
  rw [hw] at h
  have hp : IsUnit ((v:B)*∏ i, (1+(t-u)*rs i)) := h ▸ w.isUnit
  exact IsUnit.prod_univ_iff.mp (isUnit_of_mul_isUnit_right hp) i

lemma normalized_shift (f : B[X]) {n : ℕ} (hn : f.natDegree≤n)
    (t u : B) (v w : Bˣ) (rs : Fin n → B) (ds : Fin n → Bˣ)
    (hd : ∀ i, (ds i:B)=1+(t-u)*rs i)
    (hs : BinaryChange.normalized f n t v=∏ i, (Polynomial.X-C (rs i)))
    (hw : f.eval u=(w:B)) :
    BinaryChange.normalized f n u w=
      ∏ i, (Polynomial.X-C (rs i*(↑(ds i)⁻¹:B))) := by
  have hprod : (w:B)=(v:B)*∏ i, (ds i:B) := by
    rw [← hw,value_product f hn t u v rs hs]
    simp only [hd]
  have h := congrArg (MvPolynomial.aeval ![C u*Polynomial.X+1,Polynomial.X])
    (BinaryChange.binary_factorization f n t v rs hs)
  rw [← BinaryChange.transform_eq_aeval] at h
  have htrans : BinaryChange.transform f n u=
      C (v:B)*∏ i, (C (-rs i)*(C u*Polynomial.X+1)+C (1+t*rs i)*Polynomial.X) := by
    simpa using h
  rw [BinaryChange.normalized,htrans]
  simp_rw [linear_shift t u _ _ (hd _)]
  rw [Finset.prod_mul_distrib,← map_prod,← mul_assoc,← mul_assoc,← C_mul,← C_mul]
  rw [mul_assoc,← hprod,w.inv_mul,C_1,one_mul]

end Lech.RootTransitions


namespace Lech.RootGluing
open Polynomial
universe u
variable {B : Type u} [CommRing B]

lemma map_rootShift {C : Type u} [CommRing C] (φ : B →+* C) (a x : B)
    (hx : IsUnit (1+a*x)) :
    φ (rootShift a x)=rootShift (φ a) (φ x) := by
  rw [rootShift,map_mul,map_inverse φ _ hx]
  simp only [map_add,map_one,map_mul,rootShift]

lemma normalized_shift (f : B[X]) {n : ℕ} (hn : f.natDegree≤n)
    (t u : B) (v w : Bˣ) (rs : Fin n → B)
    (hs : BinaryChange.normalized f n t v=∏ i, (Polynomial.X-C (rs i)))
    (hw : f.eval u=(w:B)) :
    BinaryChange.normalized f n u w=∏ i, (Polynomial.X-C (rootShift (t-u) (rs i))) := by
  let ds : Fin n → Bˣ := fun i =>
    (RootTransitions.denominator_isUnit f hn t u v w rs hs hw i).unit
  have hd (i) : (ds i:B)=1+(t-u)*rs i := IsUnit.unit_spec _
  have hh := RootTransitions.normalized_shift f hn t u v w rs ds hd hs hw
  simpa only [rootShift,← Ring.inverse_unit,hd] using hh

variable (f : B[X]) (n : ℕ) (hn : f.natDegree≤n)
  (t u : B) (v w : Bˣ) (hv : f.eval t=(v:B)) (hw : f.eval u=(w:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized f n t v))
  (e : UniversalSplitting.Data B n (BinaryChange.normalized f n u w))

lemma mapped_factorization :
    BinaryChange.normalized (f.map (algebraMap B d.S)) n (algebraMap B d.S t)
      (Units.map (algebraMap B d.S) v)=∏ i, (Polynomial.X-C (d.roots i)) := by
  rw [← BinaryCover.map_normalized]
  exact d.factorization

end Lech.RootGluing
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootBundleChartsDenominator
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

include hn hv hs in
lemma shift_factorization :
    (BinaryChange.normalized f n t v).map (algebraMap B C)=
      ∏ i,(Polynomial.X-Polynomial.C (rootShift (u-algebraMap B C t) (rs i))) := by
  rw [BinaryCover.map_normalized]
  exact normalized_shift _ (natDegree_map_le.trans hn) u (algebraMap B C t) w
    (Units.map (algebraMap B C).toMonoidHom v) rs hs (mapped_eval f t v hv)


def hom : d.S →ₐ[B] C :=
  (d.universal C (fun i => rootShift (u-algebraMap B C t) (rs i))
    (shift_factorization f n hn t v hv u w rs hs)).choose

lemma hom_root (i : Fin n) : hom f n hn t v hv d u w rs hs (d.roots i)=
    rootShift (u-algebraMap B C t) (rs i) :=
  (d.universal C _ (shift_factorization f n hn t v hv u w rs hs)).choose_spec.1 i

include hn hv hs in
lemma denominator_unit (i : Fin n) : IsUnit (1+(u-algebraMap B C t)*rs i) :=
  RootTransitions.denominator_isUnit _ (natDegree_map_le.trans hn) u (algebraMap B C t)
    w (Units.map (algebraMap B C).toMonoidHom v) rs hs (mapped_eval f t v hv) i

end Lech.RootTransport

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCoactionT
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

local instance instAlgebraS : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance instIsScalarTowerS : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev T := B ⊗[A] d.S

def right : d.S →ₐ[A] T f n t v d := Algebra.TensorProduct.includeRight

def coord : T f n t v d := right f n t v d (algebraMap B d.S t)
def unit : (T f n t v d)ˣ := Units.map (right f n t v d).toMonoidHom
    (Units.map (algebraMap B d.S).toMonoidHom v)
def roots (i : Fin n) : T f n t v d := right f n t v d (d.roots i)

lemma coeff_poly :
    (f.map (algebraMap A B)).map (algebraMap B (T f n t v d)) =
      ((f.map (algebraMap A B)).map (algebraMap B d.S)).map (right f n t v d).toRingHom := by
  simp only [Polynomial.map_map]
  congr 1
  rw [← IsScalarTower.algebraMap_eq A B (T f n t v d),
    ← IsScalarTower.algebraMap_eq A B d.S]
  exact (AlgHom.comp_algebraMap (right f n t v d)).symm

lemma factorization :
    BinaryChange.normalized ((f.map (algebraMap A B)).map (algebraMap B (T f n t v d))) n
      (coord f n t v d) (unit f n t v d)=∏ i,(Polynomial.X-Polynomial.C (roots f n t v d i)) := by
  rw [coeff_poly]
  have h := congrArg (Polynomial.map (right f n t v d).toRingHom)
    (RootGluing.mapped_factorization (f.map (algebraMap A B)) n t v d)
  simp only [BinaryCover.map_normalized,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,
    Polynomial.map_C,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] at h
  simp only [coord,unit,roots,AlgHom.toRingHom_eq_coe]
  exact h


def hom : d.S →ₐ[B] T f n t v d :=
  RootTransport.hom (f.map (algebraMap A B)) n (natDegree_map_le.trans hn) t v hv d
    (coord f n t v d) (unit f n t v d) (roots f n t v d) (factorization f n t v d)

lemma hom_root (i : Fin n) : hom f n hn t v hv d (d.roots i)=
    rootShift (coord f n t v d-algebraMap B (T f n t v d) t) (roots f n t v d i) :=
  RootTransport.hom_root _ _ _ _ _ _ _ _ _ _ _ i

include hn hv in
lemma denominator_unit (i : Fin n) :
    IsUnit (1+(coord f n t v d-algebraMap B (T f n t v d) t)*roots f n t v d i) :=
  RootTransport.denominator_unit _ _ (natDegree_map_le.trans hn) _ _ hv _ _ _
    (factorization f n t v d) i

end


open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u

end


open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u

end


open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
end Lech.RootCoaction


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootInvariantsWeightZero
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
local instance weightZeroBaseAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance weightZeroBaseScalarTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl


def algebra : Subalgebra A d.S :=
  AlgHom.equalizer ((RootCoaction.hom f n hn t v hv d).restrictScalars A)
    (RootCoaction.right f n t v d)


def algebraBaseMap : B ⊗[A] algebra f n hn t v hv d →ₐ[B] d.S :=
  Algebra.TensorProduct.lift (Algebra.ofId B d.S) (algebra f n hn t v hv d).val
    (fun _ _ => Commute.all _ _)

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


universe u
variable {R : Type u} [CommRing R]


lemma change_root (a b s t : R) (μ ν : Rˣ)
    (hμ : (μ:R)=s*a+b) (hν : (ν:R)=t*a+b) :
    RootGluing.rootShift (s-t) (-a*(μ⁻¹:Rˣ))= -a*(ν⁻¹:Rˣ) := by
  rw [RootGluing.rootShift,change_denominator a b s t μ ν hμ hν,Ring.inverse_unit]
  simp only [mul_inv_rev,inv_inv,Units.val_mul]
  rw [← mul_assoc,mul_assoc (-a),Units.inv_mul,mul_one]

open Polynomial
end Lech.FactorNormalization


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NativeDescentCanonicalAlg
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
local instance instAlgebraS : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance instIsScalarTowerS : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev U := B ⊗[A] R (A := A) (B := B) (T := T)
abbrev includeT : T →ₐ[A] R (A := A) (B := B) (T := T) := Algebra.TensorProduct.includeRight
abbrev right : R (A := A) (B := B) (T := T) →ₐ[A] U (A := A) (B := B) (T := T) := Algebra.TensorProduct.includeRight
abbrev canonical : R (A := A) (B := B) (T := T) →ₐ[B] U (A := A) (B := B) (T := T) := NativeDescent.canonicalAlg B T

lemma canonical_include (a : T) : canonical (A := A) (B := B) (includeT a)=right (includeT a) := by
  simp [canonical,includeT,right,NativeDescent.canonicalAlg]

variable (φ : d.S →ₐ[B] R (A := A) (B := B) (T := T))

def coefficients : RootCoaction.T f n t v d →ₐ[B] U (A := A) (B := B) (T := T) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (right.comp (φ.restrictScalars A)) (fun _ _ => Commute.all _ _)

lemma coefficients_right (x : d.S) : coefficients f n t v d φ (RootCoaction.right f n t v d x)=right (φ x) := by
  simp [coefficients,RootCoaction.right]

 

lemma natural (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
    (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
    (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val) :
    (canonical (A := A) (B := B) (T := T)).comp φ=
      (coefficients f n t v d φ).comp (RootCoaction.hom f n hn t v hv d) := by
  apply d.hom_ext
  intro i
  let ν : (U (A := A) (B := B) (T := T))ˣ := Units.map (canonical (A := A) (B := B) (T := T)).toMonoidHom (μ i)
  let η : (U (A := A) (B := B) (T := T))ˣ := Units.map (right (A := A) (B := B) (T := T)).toMonoidHom (μ i)
  have hν : (ν:U (A := A) (B := B) (T := T))=algebraMap B _ t*right (includeT (a i))+right (includeT (b i)) := by
    change canonical (μ i:R (A := A) (B := B) (T := T))=_
    rw [hμ,map_add,map_mul,AlgHom.commutes,canonical_include,canonical_include]
  have hη : (η:U (A := A) (B := B) (T := T))=right (algebraMap B (R (A := A) (B := B) (T := T)) t)*right (includeT (a i))+right (includeT (b i)) := by
    change right (μ i:R (A := A) (B := B) (T := T))=_
    rw [hμ,map_add,map_mul]
  simp only [AlgHom.comp_apply,RootCoaction.hom_root]
  rw [hφ,map_mul,map_neg,canonical_include]
  change -right (includeT (a i))*(ν⁻¹).val=_
  rw [← FactorNormalization.change_root (right (includeT (a i))) (right (includeT (b i)))
    (right (algebraMap B (R (A := A) (B := B) (T := T)) t)) (algebraMap B _ t) η ν hη hν]
  change _=(coefficients f n t v d φ).toRingHom (RootGluing.rootShift _ _)
  rw [RootGluing.map_rootShift _ _ _ (RootCoaction.denominator_unit f n hn t v hv d i)]
  simp only [map_sub,RootCoaction.coord,RootCoaction.roots,coefficients_right,AlgHom.commutes,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,hφ,map_neg,map_mul]
  rfl

 
def invariantMap (a b : Fin n → T) (μ : Fin n → (R (A := A) (B := B) (T := T))ˣ)
    (hμ : ∀ i,(μ i:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i))
    (hφ : ∀ i,φ (d.roots i)= -includeT (a i)*((μ i)⁻¹).val) :
    RootInvariants.algebra f n hn t v hv d →ₐ[A] NativeDescent.canonicalAlgebra (A := A) B T where
  toFun x := ⟨φ (x:d.S),by
    change canonical (φ (x:d.S))=right (φ (x:d.S))
    have h := AlgHom.congr_fun (natural f n hn t v hv d φ a b μ hμ hφ) (x:d.S)
    change canonical (φ (x:d.S))=coefficients f n t v d φ (RootCoaction.hom f n hn t v hv d (x:d.S)) at h
    have hx : RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S) := x.property
    rw [hx,coefficients_right] at h
    exact h⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_one' := Subtype.ext (map_one φ)
  map_add' x y := Subtype.ext (map_add φ _ _)
  map_mul' x y := Subtype.ext (map_mul φ _ _)
  commutes' c := Subtype.ext ((φ.restrictScalars A).commutes c)



end Lech.FactorDescent


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open CategoryTheory CategoryTheory.Limits HomologicalComplex Set CarrierOperators
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
  (D : FiniteModuleCech.Diagram R ι)

abbrev fullCochains (p : ℕ) := Sections D (fullCarrier p)
abbrev fullSort (p : ℕ) := lift D (sortOp p)
end Lech.CechNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CompleteNoetherian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing MvPowerSeries
namespace Lech.CompleteLocal
variable {k S : Type*} [Field k] [CommRing S] [IsLocalRing S]
  [IsAdicComplete (maximalIdeal S) S]

lemma noetherian_of_coefficient_and_fg (φ : k →+* S)
    (hφ : Function.Surjective ((residue S).comp φ)) (hfg : (maximalIdeal S).FG) :
    IsNoetherianRing S := by
  obtain ⟨n,z,hzspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hz : ∀ i,z i ∈ maximalIdeal S := fun i => hzspan ▸ Ideal.subset_span (Set.mem_range_self i)
  let A := MvPowerSeries (Fin n) k
  let I := Lech.PowerSeries.variablesIdeal (Fin n) k
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal S) z hz
  let : Algebra k S := φ.toAlgebra
  let : Algebra A S := ψ.toAlgebra
  let : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (Lech.PowerSeries.eval_C φ (maximalIdeal S) z hz a).symm)
  have hmap : I.map (algebraMap A S)=maximalIdeal S := by
    change (Ideal.span (Set.range (X : Fin n → A))).map (algebraMap A S)=_
    rw [Ideal.map_span,← Set.range_comp]
    have he : (algebraMap A S) ∘ X=z := funext (fun i => Lech.PowerSeries.eval_X φ (maximalIdeal S) z hz i)
    rw [he]
    exact hzspan
  let : IsHausdorff I S := IsHausdorff.of_map (I:=I) (J:=maximalIdeal S) hmap.le
  let : IsPrecomplete I A := (Lech.PowerSeries.complete_variables (Fin n) k).toIsPrecomplete
  let : Module.Finite k (S ⧸ maximalIdeal S) :=
    Module.Finite.of_surjective (Algebra.linearMap k (S ⧸ maximalIdeal S)) hφ
  let : Module.Finite A (S ⧸ maximalIdeal S) := Module.Finite.of_restrictScalars_finite k A _
  have hsub : I • (⊤ : Submodule A S)=(maximalIdeal S).restrictScalars A := by
    rw [← hmap]
    symm
    simpa only [smul_eq_mul,Ideal.mul_top,Submodule.restrictScalars_top] using
      Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule S S)
  let e := (Submodule.quotEquivOfEq _ _ hsub).trans
    (Submodule.Quotient.restrictScalarsEquiv A (maximalIdeal S))
  let : Module.Finite A (S ⧸ (I • (⊤ : Submodule A S))) := Module.Finite.equiv e.symm
  let : Module.Finite A S := Lech.AdicNakayama.finite_of_quotient I
  exact IsNoetherianRing.of_finite A S
end Lech.CompleteLocal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProjectiveReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CoefficientReduction
open MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (h : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma graded_smul (r : R) (a : MvPolynomial (Fin h) R) :
    graded I h (r • a)=r • graded I h a :=
  (MvPolynomial.mapAlgHom (Ideal.Quotient.mkₐ R I)).toLinearMap.map_smul r a

lemma graded_surjective : Function.Surjective (graded I h) :=
  MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective



variable {f : MvPolynomial (Fin h) R} {d : ℕ} (hf : f ∈ grade (R:=R) h d)

def chartMap (f : MvPolynomial (Fin h) R) :=
  Homogeneous.awayMap (grade (R:=R) h) (SourceGraded.sourceGrade I h)
    (graded I h) (graded_smul I h) f

include hf in
lemma chartMap_surjective : Function.Surjective (chartMap I h f) :=
  Homogeneous.awayMap_surjective _ _ _ _ hf (graded_surjective I h)

end Lech.CoefficientReduction

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorCechHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

def tensorEquivalence {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv K L) :
    HomotopyEquiv ((TensorTotal.Right.functor F).obj K) ((TensorTotal.Right.functor F).obj L) where
  hom := (TensorTotal.Right.functor F).map e.hom
  inv := (TensorTotal.Right.functor F).map e.inv
  homotopyHomInvId := by
    have h := tensorHomotopy F e.homotopyHomInvId
    erw [(TensorTotal.Right.functor F).map_comp e.hom e.inv, (TensorTotal.Right.functor F).map_id K] at h
    exact h
  homotopyInvHomId := by
    have h := tensorHomotopy F e.homotopyInvHomId
    erw [(TensorTotal.Right.functor F).map_comp e.inv e.hom, (TensorTotal.Right.functor F).map_id L] at h
    exact h
end Lech.CechNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalExact
attribute [-instance] _root_.OAI.Lech.Homogeneous.module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.BicomplexTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]

def diagonal (k : ℤ) : Double (R:=R) ⥤ (Discrete (Diagonal k) ⥤ ModuleCat.{u} R) where
  obj K := Discrete.functor (fun pq => (K.X pq.val.1).X pq.val.2)
  map f := Discrete.natTrans (fun pq => (f.f pq.as.val.1).f pq.as.val.2)

instance diagonal_preservesFiniteLimits (k : ℤ) : PreservesFiniteLimits (diagonal (R:=R) k) := by
  apply preservesFiniteLimits_of_evaluation
  intro pq
  change PreservesFiniteLimits (eval (Row (R:=R)) (.up ℤ) pq.as.val.1 ⋙ eval (ModuleCat.{u} R) (.up ℤ) pq.as.val.2)
  infer_instance
instance diagonal_preservesFiniteColimits (k : ℤ) : PreservesFiniteColimits (diagonal (R:=R) k) := by
  apply preservesFiniteColimits_of_evaluation
  intro pq
  change PreservesFiniteColimits (eval (Row (R:=R)) (.up ℤ) pq.as.val.1 ⋙ eval (ModuleCat.{u} R) (.up ℤ) pq.as.val.2)
  infer_instance
instance diagonal_additive (k : ℤ) : (diagonal (R:=R) k).Additive where
  map_add := by intros; ext pq; rfl

end Lech.BicomplexTotal

end

end OAI
end


