-- Prove2me | Definitions.Def_OAIQ032L019
-- name    : OAIQ032L019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:57:41.912154+00:00
-- url     : https://prove2.me/theorems/35cb6d3b-a5bd-49ac-a062-d6692ec3d6cc
-- title:
--   Definitions bundle OAIQ032L019 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 74 declarations of OpenAI's Lean: 28 definitions and 46 theorems. The definitions and types are `OAI.Lech.ArbitraryCoefficientField.localSection`, `OAI.Lech.BicomplexTotal.bottomHomologyIso`, `OAI.Lech.BicomplexTotal.doubleCoverIso`, `OAI.Lech.BicomplexTotal.singleHomologyIso`, `OAI.Lech.BicomplexTotal.singleIso`, `OAI.Lech.BicomplexTotal.singleZeroIso`, `OAI.Lech.CechNormalization.contraction`, `OAI.Lech.CechNormalization.contractionOp`, `OAI.Lech.CechNormalization.deltaOp`, `OAI.Lech.CechNormalization.expandMap`, `OAI.Lech.CechNormalization.expandOp`, `OAI.Lech.CechNormalization.fullD`, `OAI.Lech.CechNormalization.fullExpand`, `OAI.Lech.CechNormalization.fullH`, `OAI.Lech.CechNormalization.fullN`, `OAI.Lech.CechNormalization.fullPositive`, `OAI.Lech.CechNormalization.homotopyComponent`, `OAI.Lech.CechNormalization.homotopyEquiv`, `OAI.Lech.CechNormalization.normalizationHomotopy`, `OAI.Lech.CechNormalization.normalizeOp`, `OAI.Lech.CechNormalization.sortMap`, `OAI.Lech.CechNormalization.sortedDeltaOp`, `OAI.Lech.ComplexExtension.natDoubleCoverIso`, `OAI.Lech.DoubleCech.columnIso`, `OAI.Lech.DoubleCech.complex`, `OAI.Lech.DoubleCech.row`, `OAI.Lech.DoubleCech.rowMap`, `OAI.Lech.FiniteModuleCech.positiveComplex`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ArbitraryCoefficientField`, `Multiplicity_CechCarrierOperators`, `Multiplicity_CechNormalization`, `Multiplicity_CechNormalizationRows`, `Multiplicity_FiniteModuleCech`, `Multiplicity_LechConnectingIso`, `Multiplicity_ProductSourceCoverFaceSlice`, `Multiplicity_ReesRootCech`.
--
--   **Imports.** It imports the bundles `OAIQ032L010` and `OAIQ032L011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L024`, `OAIQ032L025` and `OAIQ032L027`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L010
import Definitions.Def_OAIQ032L011

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ArbitraryCoefficientField
attribute [-instance] _root_.OAI.Lech.Homogeneous.module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ArbitraryCoefficientField
open IsLocalRing
variable (R : Type*) [CommRing R] [IsLocalRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p] [IsAdicComplete (maximalIdeal R) R]


def localSection : R ⧸ maximalIdeal R →+* R := (quotientSectionData R p).1

lemma localSection_rightInverse :
    Function.RightInverse (localSection R p) (Ideal.Quotient.mk (maximalIdeal R)) :=
  (quotientSectionData R p).2

end Lech.ArbitraryCoefficientField

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverFaceSlice
attribute [-instance] _root_.OAI.Lech.BicomplexTotal.diagonal_additive _root_.OAI.Lech.BicomplexTotal.diagonal_preservesFiniteColimits _root_.OAI.Lech.BicomplexTotal.diagonal_preservesFiniteLimits
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
omit [Fintype ι] [LinearOrder ι] in
lemma vertical_square (p q : ℕ) (f : term R M F p q) :
    vertical R M F h₂ p (q+1) (vertical R M F h₂ p q f)=0 := by
  funext s
  exact AlternatingCech.sortedDelta_square R M (F s.val) (h₂ s.val) q (f s)
omit [Fintype κ] [LinearOrder κ] in
lemma horizontal_square (p q : ℕ) (f : term R M F p q) :
    horizontal R M F h₁ (p+1) q (horizontal R M F h₁ p q f)=0 := by
  funext s t
  exact congrFun (AlternatingCech.sortedDelta_square R M (fun s => F s t.val) (h₁ t.val)
    p (fun s => f s t)) s

def row (p : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of R (term R M F p q))
    (fun q => ModuleCat.ofHom (vertical R M F h₂ p q)) (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact vertical_square R M F h₂ p q)
omit [Fintype ι] [LinearOrder ι] in
lemma row_d (p q : ℕ) : (row R M F h₂ p).d q (q+1)=ModuleCat.ofHom (vertical R M F h₂ p q) := by
  change CochainComplex.of.d (fun q => ModuleCat.of R (term R M F p q))
    (fun q => ModuleCat.ofHom (vertical R M F h₂ p q)) q (q+1)=_
  exact CochainComplex.of_d _ _ q
 
def rowMap (p : ℕ) : row R M F h₂ p ⟶ row R M F h₂ (p+1) :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (horizontal R M F h₁ p q)) (fun q => by
    rw [row_d,row_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact horizontal_vertical R M F h₁ h₂ p q f)
lemma rowMap_square (p : ℕ) : rowMap R M F h₁ h₂ p ≫ rowMap R M F h₁ h₂ (p+1)=0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact horizontal_square R M F h₁ p q
 

def complex : CochainComplex (CochainComplex (ModuleCat.{u} R) ℕ) ℕ :=
  CochainComplex.of (row R M F h₂) (rowMap R M F h₁ h₂) (rowMap_square R M F h₁ h₂)
end Lech.DoubleCech


namespace Lech.BicomplexTotal

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (F : Row (R := R))


def singleZeroIso : F ≅ totalSingleZero F :=
  Hom.isoOfComponents (singleXIso F) (fun _ _ hij => into_single_comm F _ _ hij)
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (F : Row (R := R))
 
def singleIso (j : ℤ) :
    total ((single (Row (R := R)) (.up ℤ) j).obj F) (.up ℤ) ≅ F⟦-j⟧ :=
  (functor (R := R)).mapIso
    (((CochainComplex.singleFunctors (Row (R := R))).shiftIso (-j) j 0 (by omega)).app F).symm ≪≫
    totalShift₁Iso (singleZero F) (-j) ≪≫
    (shiftFunctor (Row (R := R)) (-j)).mapIso (singleZeroIso F).symm

def singleHomologyIso (j i : ℤ) :
    (total ((single (Row (R := R)) (.up ℤ) j).obj F) (.up ℤ)).homology i ≅
      F.homology (-j+i) :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (singleIso F j) ≪≫
    (((homologyFunctor (ModuleCat.{u} R) (.up ℤ) (0:ℤ)).shiftIso (-j) i _ rfl).app F)


theorem acyclic_of_rows (m : ℤ) (N : ℕ) (K : Double (R := R))
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (K.X j))
    (hr : ∀ j i, IsZero ((K.X j).homology i)) (i : ℤ) :
    IsZero ((total K (.up ℤ)).homology i) := by
  apply devissage (IsZero (C := ModuleCat.{u} R)) m N K i hb
  intro j
  exact (hr j (-j+i)).of_iso (singleHomologyIso (K.X j) j i)
end Lech.BicomplexTotal


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechConnectingIso
attribute [-instance] _root_.OAI.Lech.BicomplexTotal.diagonal_additive _root_.OAI.Lech.BicomplexTotal.diagonal_preservesFiniteColimits _root_.OAI.Lech.BicomplexTotal.diagonal_preservesFiniteLimits
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
include hr in
lemma positiveRows_total_acyclic (i : ℤ) :
    IsZero ((total (positiveRows K N hb) (.up ℤ)).homology i) := by
  apply acyclic_of_rows 0 N (positiveRows K N hb)
  · intro j hj
    exact positiveRows_bounded K N hb j (by simpa only [zero_add] using hj)
  · exact positiveRows_acyclic K N hb hr
include hr in
lemma bottom_total_homology_isIso (i : ℤ) :
    IsIso (homologyMap ((functor (R := R)).map
      (FiniteComplex.bottomProjection K 0 (fun j hj => hb j (Or.inl hj)))) i) := by
  let S := (FiniteComplex.bottomShortComplex K 0 (fun j hj => hb j (Or.inl hj))).map
    (functor (R := R))
  have hS : S.ShortExact := bottom_total_shortExact K N hb
  have h0 (j : ℤ) : IsZero (S.X₁.homology j) := positiveRows_total_acyclic K N hb hr j
  have : Mono (homologyMap S.g i) :=
    (hS.homology_exact₂ i).mono_g ((h0 i).eq_of_src _ _)
  have : Epi (homologyMap S.g i) :=
    (hS.homology_exact₃ i (i+1) rfl).epi_f ((h0 (i+1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (homologyMap S.g i)
 

def bottomHomologyIso (i : ℤ) :
    (total K (.up ℤ)).homology i ≅ (K.X 0).homology i := by
  exact @asIso _ _ _ _ (homologyMap ((functor (R := R)).map
    (FiniteComplex.bottomProjection K 0 (fun j hj => hb j (Or.inl hj)))) i)
      (bottom_total_homology_isIso K N hb hr i) ≪≫
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (singleZeroIso (K.X 0)).symm
 

def doubleCoverIso (M : ℕ)
    (hc : ∀ j, j<0 ∨ (M:ℤ)≤j → IsZero ((flip K).X j))
    (hcExact : ∀ j,0<j → ∀ i,IsZero (((flip K).X j).homology i)) (i : ℤ) :
    (K.X 0).homology i ≅ ((flip K).X 0).homology i :=
  (bottomHomologyIso K N hb hr i).symm ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (totalFlipIso K (.up ℤ)).symm ≪≫
      bottomHomologyIso (flip K) M hc hcExact i
end Lech.BicomplexTotal


namespace Lech.ComplexExtension
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (K : NatDouble (R := R))

variable (N M : ℕ) (hrb : ∀ n,N≤n → IsZero (K.X n))
  (hcb : ∀ n,M≤n → IsZero ((flip K).X n))
  (hr : ∀ n,0<n → (K.X n).Acyclic) (hc : ∀ n,0<n → ((flip K).X n).Acyclic)


def natDoubleCoverIso (i : ℤ) :
    ((K.X 0).extend ComplexShape.embeddingUpNat).homology i ≅
      (((flip K).X 0).extend ComplexShape.embeddingUpNat).homology i :=
  ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (rowIso K 0)).symm ≪≫
    BicomplexTotal.doubleCoverIso (doubleExtend K) N (row_bounded K N hrb)
      (row_positive K hr) M (column_bounded K M hcb) (column_positive K hc) i ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (columnIso K 0)
end Lech.ComplexExtension


namespace Lech.DoubleCech

section
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
lemma complex_d (p : ℕ) : (complex R M F h₁ h₂).d p (p+1)=rowMap R M F h₁ h₂ p := by
  change CochainComplex.of.d (row R M F h₂) (rowMap R M F h₁ h₂) p (p+1)=_
  exact CochainComplex.of_d _ _ p

def columnIso (q : ℕ) : ((flip (complex R M F h₁ h₂)).X q) ≅
    row R M (fun t s => F s t) h₁ q :=
  Hom.isoOfComponents (fun p =>
    (switch R M F p q).toModuleIso)
    (fun p r h => by
      obtain rfl : p+1=r := h
      change _ ≫ (row R M (fun t s => F s t) h₁ q).d p (p+1)=
        ((complex R M F h₁ h₂).d p (p+1)).f q ≫ _
      rw [complex_d,row_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)
end


open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
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



lemma raw_square (N : Type u) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : powersetCard ι n → N) :
    rawDelta R N (n+1) (rawDelta R N n f) = 0 := by
  have he := sortedDelta_square R N (fun _ : Finset ι => ⊤) (fun _ _ _ => le_rfl) n
    (fun s => (⟨f s,Submodule.mem_top⟩ : (⊤ : Submodule R N)))
  funext s
  have hh := congrArg (fun g => (g s : N)) he
  simpa only [sortedDelta,rawDelta,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,
    Submodule.coe_smul_of_tower,Submodule.coe_zero,Pi.zero_apply,Submodule.inclusion_apply] using hh



omit [Fintype ι] in
lemma toFixed_d (S : Finset ι) (n : ℕ) (f : cochains D n)
    (t : powersetCard ι (n+1)) (ht : t.val ⊆ S) :
    rawDelta R (D.obj S) n (toFixed D S n f) t = (D.res ht).hom (d D n f t) := by
  change (∑ i : Fin (n+1), (-1:ℤ)^i.val • toFixed D S n f (delete t i)) =
    (D.res ht).hom (∑ i : Fin (n+1), (-1:ℤ)^i.val •
      (D.res (delete_subset t i)).hom (f (delete t i)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  rw [toFixed,dite_eq_left ((delete_subset t i).trans ht)]
  exact congrArg (fun φ : D.obj (delete t i).val ⟶ D.obj S => φ.hom (f (delete t i)))
    (D.res_comp (delete_subset t i) ht).symm

lemma d_square (n : ℕ) (f : cochains D n) : d D (n+1) (d D n f) = 0 := by
  funext s
  calc
    d D (n+1) (d D n f) s =
      rawDelta R (D.obj s.val) (n+1)
        (rawDelta R (D.obj s.val) n (toFixed D s.val n f)) s := by
      change (∑ i : Fin (n+2), (-1:ℤ)^i.val •
        (D.res (delete_subset s i)).hom (d D n f (delete s i))) =
        ∑ i : Fin (n+2), (-1:ℤ)^i.val •
          rawDelta R (D.obj s.val) n (toFixed D s.val n f) (delete s i)
      apply Finset.sum_congr rfl
      intro i _
      rw [toFixed_d D _ _ _ _ (delete_subset s i)]
    _ = 0 := congrFun (raw_square (R:=R) (ι:=ι) (D.obj s.val) n (toFixed D s.val n f)) s

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

lemma normalize_sorted (p : ℕ) (f : Row M (ι:=ι) p) (s : powersetCard ι p) :
    normalize R M p f (s.val.orderEmbOfFin s.property)=f (s.val.orderEmbOfFin s.property) := by
  change AlternatingCech.evaluation R M p (altify R M p f) (s.val.orderEmbOfFin s.property)=_
  rw [←AlternatingCech.sortedCoordinates_eq_evaluation]
  change AlternatingCech.sortedCoordinates R M p
    ((AlternatingCech.sortedCoordinates R M p).symm (sortedRestriction R M p f)) s=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma altify_delta (p : ℕ) (f : Row M (ι:=ι) p) :
    altify R M (p+1) (delta R M p f)=AlternatingCech.delta R M p (altify R M p f) := by
  apply (AlternatingCech.sortedCoordinates R M (p+1)).injective
  ext s
  change AlternatingCech.sortedCoordinates R M (p+1)
    ((AlternatingCech.sortedCoordinates R M (p+1)).symm _) s=_
  rw [LinearEquiv.apply_symm_apply,AlternatingCech.sortedCoordinates_delta]
  change (∑ i : Fin (p+1),(-1:R)^i.val • f (s.val.orderEmbOfFin s.property ∘ i.succAbove)) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Int.cast_smul_eq_zsmul R]
  simp only [Int.cast_pow,Int.cast_neg,Int.cast_one]
  congr 1
  change f (powersetCard.ofFinEmbEquiv.symm s ∘ i.succAbove)=
    AlternatingCech.sortedCoordinates R M p
      ((AlternatingCech.sortedCoordinates R M p).symm (sortedRestriction R M p f)) (AlternatingCech.delete s i)
  rw [LinearEquiv.apply_symm_apply]
  change f (powersetCard.ofFinEmbEquiv.symm s ∘ i.succAbove)=
    f (powersetCard.ofFinEmbEquiv.symm (AlternatingCech.delete s i))
  rw [AlternatingCech.delete_sorted]
  rfl

lemma normalize_delta (p : ℕ) (f : Row M (ι:=ι) p) :
    normalize R M (p+1) (delta R M p f)=delta R M p (normalize R M p f) := by
  change AlternatingCech.evaluation R M (p+1) (altify R M (p+1) (delta R M p f))=_
  rw [altify_delta,AlternatingCech.evaluation_delta]
  rfl

lemma normalize_zero (f : Row M (ι:=ι) 0) : normalize R M 0 f=f := by
  ext a
  let s : powersetCard ι 0 := ⟨∅,rfl⟩
  have ha : a=s.val.orderEmbOfFin s.property := Subsingleton.elim _ _
  rw [ha,normalize_sorted]

lemma normalize_agree (S : Finset ι) (p : ℕ) (f g : Row M (ι:=ι) p)
    (hf : AgreeOn M S p f g) : AgreeOn M S p (normalize R M p f) (normalize R M p g) := by
  intro a ha
  by_cases h : Function.Injective a
  · obtain ⟨s,σ,_,hσ⟩ := AlternatingCech.tuple_sort a h
    rw [hσ,normalize_perm,normalize_perm,normalize_sorted,normalize_sorted]
    congr 1
    apply hf
    intro index hindex
    obtain ⟨position,_,hposition⟩ := Finset.mem_image.mp hindex
    apply ha
    refine Finset.mem_image.mpr ⟨σ.symm position,Finset.mem_univ _,?_⟩
    simpa only [hσ,Function.comp_apply,Equiv.apply_symm_apply] using hposition
  · rw [normalize_degenerate R M p f a h,normalize_degenerate R M p g a h]

variable {N : Type u} [AddCommGroup N] [Module R N]
lemma normalize_natural (l : M →ₗ[R] N) (p : ℕ) (f : Row M (ι:=ι) p) :
    normalize R N p (l ∘ f)=l ∘ normalize R M p f := by
  ext a
  by_cases h : Function.Injective a
  · obtain ⟨s,σ,hs,hσ⟩ := AlternatingCech.tuple_sort a h
    rw [hσ,normalize_perm,normalize_sorted]
    change _=l (normalize R M p f (s.val.orderEmbOfFin s.property ∘ σ))
    rw [normalize_perm,normalize_sorted,map_zsmul]
    rfl
  · rw [normalize_degenerate R N p _ a h]
    change _=l (normalize R M p f a)
    rw [normalize_degenerate R M p f a h,map_zero]

omit [Fintype ι] [LinearOrder ι] in
lemma delta_natural (l : M →ₗ[R] N) (p : ℕ) (f : Row M (ι:=ι) p) :
    delta R N p (l ∘ f)=l ∘ delta R M p f := by
  ext a
  simp only [delta,LinearMap.coe_mk,AddHom.coe_mk,Function.comp_apply,map_sum,map_smul]

omit [Fintype ι] in
lemma delta_agree (S : Finset ι) (p : ℕ) (f g : Row M (ι:=ι) p)
    (hf : AgreeOn M S p f g) : AgreeOn M S (p+1) (delta R M p f) (delta R M p g) := by
  intro a ha
  change (∑ i : Fin (p+1),(-1:R)^i.val • f (a ∘ i.succAbove)) =
    ∑ i : Fin (p+1),(-1:R)^i.val • g (a ∘ i.succAbove)
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact hf _ ((intersection_delete a i).trans ha)

omit [Fintype ι] in
lemma extra_agree (S : Finset ι) (c : ι) (hc : c∈S) (p : ℕ) (f g : Row M (ι:=ι) (p+1))
    (hf : AgreeOn M S (p+1) f g) : AgreeOn M S p (extra R M c p f) (extra R M c p g) := by
  intro a ha
  apply hf
  rw [intersection_cons]
  exact Finset.insert_subset hc ha

 

def contraction : (p : ℕ) → Row M (ι:=ι) (p+1) →ₗ[R] Row M (ι:=ι) p
  | 0 => 0
  | p+1 => LinearMap.pi (fun a : Fin (p+1) → ι =>
      (LinearMap.proj a).comp
        (extra R M (a 0) (p+1) -
          (normalize R M (p+1)).comp (extra R M (a 0) (p+1)) -
          (delta R M p).comp ((contraction p).comp (extra R M (a 0) (p+1)))))

lemma contraction_succ (p : ℕ) (f : Row M (ι:=ι) (p+2)) (a : Fin (p+1) → ι) :
    contraction R M (p+1) f a =
      (extra R M (a 0) (p+1) f - normalize R M (p+1) (extra R M (a 0) (p+1) f) -
        delta R M p (contraction R M p (extra R M (a 0) (p+1) f))) a := rfl

lemma contraction_identity_step (p : ℕ)
    (h : ∀ g : Row M (ι:=ι) p,
      delta R M p (contraction R M p (delta R M p g))=
        delta R M p g-normalize R M (p+1) (delta R M p g))
    (f : Row M (ι:=ι) (p+1)) :
    contraction R M (p+1) (delta R M (p+1) f)+delta R M p (contraction R M p f)=
      f-normalize R M (p+1) f := by
  ext a
  rw [Pi.add_apply,contraction_succ]
  let c := a 0
  let g := extra R M c p f
  have he : extra R M c (p+1) (delta R M (p+1) f)=f-delta R M p g :=
    eq_sub_iff_add_eq.mpr (extra_delta R M c p f)
  have hh : extra R M c (p+1) (delta R M (p+1) f)-
      normalize R M (p+1) (extra R M c (p+1) (delta R M (p+1) f))-
      delta R M p (contraction R M p (extra R M c (p+1) (delta R M (p+1) f)))+
      delta R M p (contraction R M p f)=f-normalize R M (p+1) f := by
    rw [he,map_sub,map_sub,map_sub,h g]
    abel
  exact congrFun hh a

lemma contraction_identity (p : ℕ) (f : Row M (ι:=ι) (p+1)) :
    contraction R M (p+1) (delta R M (p+1) f)+delta R M p (contraction R M p f)=
      f-normalize R M (p+1) f := by
  induction p with
  | zero =>
    apply contraction_identity_step
    intro g
    rw [contraction,LinearMap.zero_apply,map_zero,normalize_delta,normalize_zero,sub_self]
  | succ p ih =>
    apply contraction_identity_step
    intro g
    have hi := congrArg (delta R M (p+1)) (ih g)
    rw [map_add,delta_square,add_zero,map_sub,←normalize_delta] at hi
    exact hi

lemma contraction_natural (l : M →ₗ[R] N) (p : ℕ) (f : Row M (ι:=ι) (p+1)) :
    contraction R N p (l ∘ f)=l ∘ contraction R M p f := by
  induction p with
  | zero => ext a; simp [contraction]
  | succ p ih =>
    ext a
    rw [contraction_succ]
    change _=l (contraction R M (p+1) f a)
    rw [contraction_succ]
    have he : extra R N (a 0) (p+1) (l ∘ f)=l ∘ extra R M (a 0) (p+1) f := rfl
    rw [he,normalize_natural,ih,delta_natural]
    simp only [Pi.sub_apply,Function.comp_apply,map_sub]

lemma contraction_agree (S : Finset ι) (p : ℕ) (f g : Row M (ι:=ι) (p+1))
    (hf : AgreeOn M S (p+1) f g) : AgreeOn M S p (contraction R M p f) (contraction R M p g) := by
  induction p with
  | zero => intro a ha; rfl
  | succ p ih =>
    intro a ha
    rw [contraction_succ,contraction_succ]
    have hc : a 0∈S := ha (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩)
    have he := extra_agree R M S (a 0) hc (p+1) f g hf
    simp only [Pi.sub_apply]
    rw [he a ha,normalize_agree R M S (p+1) _ _ he a ha,
      delta_agree R M S p _ _ (ih _ _ he) a ha]
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

def deltaOp (p : ℕ) : Op (R:=R) (fullCarrier (ι:=ι) p) (fullCarrier (p+1)) where
  app M := delta R M p
  natural l f := delta_natural R _ l p f
  locality M S f g h := delta_agree R M S p f g h

def normalizeOp (p : ℕ) : Op (R:=R) (fullCarrier (ι:=ι) p) (fullCarrier p) where
  app M := normalize R M p
  natural l f := normalize_natural R _ l p f
  locality M S f g h := normalize_agree R M S p f g h

def contractionOp (p : ℕ) : Op (R:=R) (fullCarrier (ι:=ι) (p+1)) (fullCarrier p) where
  app M := contraction R M p
  natural l f := contraction_natural R _ l p f
  locality M S f g h := contraction_agree R M S p f g h

variable (R) (M : Type u) [AddCommGroup M] [Module R M]

lemma expansion_sorted (p : ℕ) (f : powersetCard ι p → M) (s : powersetCard ι p) :
    expansion R M p f (s.val.orderEmbOfFin s.property)=f s := by
  change AlternatingCech.evaluation R M p ((AlternatingCech.sortedCoordinates R M p).symm f)
    (s.val.orderEmbOfFin s.property)=_
  rw [←AlternatingCech.sortedCoordinates_eq_evaluation,LinearEquiv.apply_symm_apply]

lemma expansion_natural {N : Type u} [AddCommGroup N] [Module R N]
    (l : M →ₗ[R] N) (p : ℕ) (f : powersetCard ι p → M) :
    expansion R N p (l ∘ f)=l ∘ expansion R M p f := by
  ext a
  by_cases h : Function.Injective a
  · obtain ⟨s,σ,hs,hσ⟩ := AlternatingCech.tuple_sort a h
    rw [hσ,expansion_perm,expansion_sorted]
    change _=l (expansion R M p f (s.val.orderEmbOfFin s.property ∘ σ))
    rw [expansion_perm,expansion_sorted,map_zsmul]
    rfl
  · rw [expansion_degenerate R N p _ a h]
    change _=l (expansion R M p f a)
    rw [expansion_degenerate R M p f a h,map_zero]

lemma expansion_agree (S : Finset ι) (p : ℕ) (f g : powersetCard ι p → M)
    (hf : Agree (sortedCarrier p) M S f g) :
    Agree (fullCarrier p) M S (expansion R M p f) (expansion R M p g) := by
  intro a ha
  by_cases h : Function.Injective a
  · obtain ⟨s,σ,hs,hσ⟩ := AlternatingCech.tuple_sort a h
    rw [hσ,expansion_perm,expansion_perm,expansion_sorted,expansion_sorted]
    congr 1
    apply hf
    change s.val⊆S
    rw [←hs]
    intro index hindex
    obtain ⟨position,_,hposition⟩ :=
      (@Finset.mem_image (Fin p) ι
        (fun left right => Classical.propDecidable (left=right)) a Finset.univ index).mp hindex
    exact ha (Finset.mem_image.mpr ⟨position,Finset.mem_univ _,hposition⟩)
  · rw [expansion_degenerate R M p f a h,expansion_degenerate R M p g a h]

variable {R M}
def expandOp (p : ℕ) : Op (R:=R) (sortedCarrier (ι:=ι) p) (fullCarrier p) where
  app M := expansion R M p
  natural l f := expansion_natural R _ l p f
  locality M S f g h := expansion_agree R M S p f g h

def sortedDeltaOp (p : ℕ) : Op (R:=R) (sortedCarrier (ι:=ι) p) (sortedCarrier (p+1)) where
  app M := AlternatingCech.rawDelta R M p
  natural l f := by
    ext s
    change (∑ i : Fin (p+1),(-1:ℤ)^i.val • l (f (AlternatingCech.delete s i))) =
      l (∑ i : Fin (p+1),(-1:ℤ)^i.val • f (AlternatingCech.delete s i))
    rw [map_sum]
    simp only [map_zsmul]
  locality M S f g h s hs := by
    change (∑ i : Fin (p+1),(-1:ℤ)^i.val • f (AlternatingCech.delete s i)) =
      ∑ i : Fin (p+1),(-1:ℤ)^i.val • g (AlternatingCech.delete s i)
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact h _ ((AlternatingCech.delete_subset s i).trans hs)

omit [Fintype ι] in
lemma sort_delta (M : ModuleCat.{u} R) (p : ℕ) :
    ((sortOp (R:=R) (ι:=ι) (p+1)).app M).comp ((deltaOp p).app M) =
      ((sortedDeltaOp p).app M).comp ((sortOp p).app M) := by
  apply LinearMap.ext
  intro f
  funext s
  change (∑ i : Fin (p+1),(-1:R)^i.val • f (s.val.orderEmbOfFin s.property ∘ i.succAbove)) =
    ∑ i : Fin (p+1),(-1:ℤ)^i.val • f ((AlternatingCech.delete s i).val.orderEmbOfFin (AlternatingCech.delete s i).property)
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Int.cast_smul_eq_zsmul R]
  simp only [Int.cast_pow,Int.cast_neg,Int.cast_one]
  congr 1
  change f (powersetCard.ofFinEmbEquiv.symm s ∘ i.succAbove)=
    f (powersetCard.ofFinEmbEquiv.symm (AlternatingCech.delete s i))
  rw [AlternatingCech.delete_sorted]
  rfl

lemma sort_expand (M : ModuleCat.{u} R) (p : ℕ) :
    ((sortOp (R:=R) (ι:=ι) p).app M).comp ((expandOp p).app M)=LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext s
  exact expansion_sorted R M p f s

lemma expand_sort (M : ModuleCat.{u} R) (p : ℕ) :
    ((expandOp (R:=R) (ι:=ι) p).app M).comp ((sortOp p).app M)=(normalizeOp p).app M := rfl

lemma expand_delta (M : ModuleCat.{u} R) (p : ℕ) :
    ((expandOp (R:=R) (ι:=ι) (p+1)).app M).comp ((sortedDeltaOp p).app M) =
      ((deltaOp p).app M).comp ((expandOp p).app M) := by
  apply LinearMap.ext
  intro f
  have hr : sortedRestriction R M p (expansion R M p f)=f := by
    ext s
    exact expansion_sorted R M p f s
  have hs := DFunLike.congr_fun (sort_delta (R:=R) (ι:=ι) M p) (expansion R M p f)
  change sortedRestriction R M (p+1) (delta R M p (expansion R M p f))=
    AlternatingCech.rawDelta R M p (sortedRestriction R M p (expansion R M p f)) at hs
  rw [hr] at hs
  change expansion R M (p+1) (AlternatingCech.rawDelta R M p f)=delta R M p (expansion R M p f)
  rw [←hs]
  change normalize R M (p+1) (delta R M p (expansion R M p f))=_
  rw [normalize_delta]
  change delta R M p (expansion R M p (sortedRestriction R M p (expansion R M p f)))=_
  rw [hr]
end Lech.CechNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootCech
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

 

def positiveComplex (D : Diagram R ι) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains D (n+1)))
    (fun n => ModuleCat.ofHom (d D (n+1))) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact d_square D (n+1))
lemma positiveComplex_d (D : Diagram R ι) (n : ℕ) :
    (positiveComplex D).d n (n+1) = ModuleCat.ofHom (d D (n+1)) := by
  unfold positiveComplex
  exact CochainComplex.of_d (fun j => ModuleCat.of R (cochains D (j+1)))
    (fun j => ModuleCat.ofHom (d D (j+1))) n
end Lech.FiniteModuleCech

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

abbrev fullD (p : ℕ) := lift D (deltaOp p)
abbrev fullExpand (p : ℕ) := lift D (expandOp p)
abbrev fullH (p : ℕ) := lift D (contractionOp p)
abbrev fullN (p : ℕ) := lift D (normalizeOp p)

omit [Fintype ι] in
lemma fullD_square (p : ℕ) (f : fullCochains D p) : fullD D (p+1) (fullD D p f)=0 := by
  change ((lift D (deltaOp (p+1))).comp (lift D (deltaOp p))) f=0
  rw [←lift_comp]
  funext a
  exact congrFun (FiniteCoverCech.delta_square R (D.obj (FiniteCoverCech.intersection a)) p
    (toFixed D (fullCarrier p) (FiniteCoverCech.intersection a) f)) a

omit [Fintype ι] in
lemma sortedD_eq (p : ℕ) : lift D (sortedDeltaOp p)=FiniteModuleCech.d D p := by
  apply LinearMap.ext
  intro f
  funext s
  change (∑ i : Fin (p+1),(-1:ℤ)^i.val •
      toFixed D (sortedCarrier p) s.val f (AlternatingCech.delete s i))=_
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  change (if h : (AlternatingCech.delete s i).val⊆s.val then _ else _)=_
  rw [dite_eq_left (AlternatingCech.delete_subset s i)]

omit [Fintype ι] in
lemma fullSort_d (p : ℕ) :
    (fullSort D (p+1)).comp (fullD D p)=(FiniteModuleCech.d D p).comp (fullSort D p) := by
  rw [←sortedD_eq]
  exact (by
    rw [←lift_comp,←lift_comp]
    exact lift_congr D (fun M => sort_delta M p))

lemma fullExpand_d (p : ℕ) :
    (fullExpand D (p+1)).comp (FiniteModuleCech.d D p)=(fullD D p).comp (fullExpand D p) := by
  rw [←sortedD_eq]
  rw [←lift_comp,←lift_comp]
  exact lift_congr D (fun M => expand_delta M p)

lemma fullSort_expand (p : ℕ) : (fullSort D p).comp (fullExpand D p)=LinearMap.id := by
  rw [←lift_id D (sortedCarrier p)]
  rw [←lift_comp]
  exact lift_congr D (fun M => sort_expand M p)

lemma fullExpand_sort (p : ℕ) : (fullExpand D p).comp (fullSort D p)=fullN D p := by
  rw [←lift_comp]
  exact lift_congr D (fun M => expand_sort M p)

lemma fullH_zero : fullH D 0=0 := by
  apply LinearMap.ext
  intro f
  funext a
  rfl

lemma fullH_identity (p : ℕ) :
    (fullH D (p+1)).comp (fullD D (p+1))+(fullD D p).comp (fullH D p)=
      LinearMap.id-fullN D (p+1) := by
  change (lift D (contractionOp (p+1))).comp (lift D (deltaOp (p+1)))+
    (lift D (deltaOp p)).comp (lift D (contractionOp p))=LinearMap.id-lift D (normalizeOp (p+1))
  rw [←lift_comp,←lift_comp,←lift_add,←lift_id D (fullCarrier (p+1)),←lift_sub]
  apply lift_congr D
  intro M
  apply LinearMap.ext
  exact contraction_identity R M p

 
def fullPositive : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of R (fullCochains D (p+1)))
    (fun p => ModuleCat.ofHom (fullD D (p+1))) (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact fullD_square D (p+1))

omit [Fintype ι] in
lemma fullPositive_d (p : ℕ) : (fullPositive D).d p (p+1)=ModuleCat.ofHom (fullD D (p+1)) := by
  unfold fullPositive
  exact CochainComplex.of_d (fun q => ModuleCat.of R (fullCochains D (q+1)))
    (fun q => ModuleCat.ofHom (fullD D (q+1))) p

def sortMap : fullPositive D ⟶ FiniteModuleCech.positiveComplex D :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (fullSort D (p+1))) (fun p => by
    rw [fullPositive_d,FiniteModuleCech.positiveComplex_d]
    apply ModuleCat.hom_ext
    exact (fullSort_d D (p+1)).symm)

def expandMap : FiniteModuleCech.positiveComplex D ⟶ fullPositive D :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (fullExpand D (p+1))) (fun p => by
    rw [fullPositive_d,FiniteModuleCech.positiveComplex_d]
    apply ModuleCat.hom_ext
    exact (fullExpand_d D (p+1)).symm)

lemma expand_sortMap : expandMap D ≫ sortMap D=𝟙 _ := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  exact fullSort_expand D (p+1)

lemma sort_expandMap (p : ℕ) :
    ((sortMap D ≫ expandMap D).f p).hom=fullN D (p+1) := fullExpand_sort D (p+1)

def homotopyComponent (i j : ℕ) : (fullPositive D).X i ⟶ (fullPositive D).X j :=
  if h : j+1=i then by subst i; exact ModuleCat.ofHom (fullH D (j+1)) else 0

lemma homotopyComponent_succ (j : ℕ) :
    homotopyComponent D (j+1) j=ModuleCat.ofHom (fullH D (j+1)) := by
  rw [homotopyComponent,dite_eq_left rfl]

def normalizationHomotopy : Homotopy (𝟙 (fullPositive D)) (sortMap D ≫ expandMap D) where
  hom := homotopyComponent D
  zero i j h := by
    change ¬j+1=i at h
    rw [homotopyComponent,dite_eq_right h]
  comm i := by
    rw [Homotopy.dNext_cochainComplex,homotopyComponent_succ,fullPositive_d]
    cases i with
    | zero =>
        rw [Homotopy.prevD_zero_cochainComplex,add_zero]
        apply ModuleCat.hom_ext
        have hh := fullH_identity D 0
        rw [fullH_zero,LinearMap.comp_zero,add_zero] at hh
        change LinearMap.id=(fullH D 1).comp (fullD D 1)+_
        rw [sort_expandMap]
        exact (eq_sub_iff_add_eq.mp hh).symm
    | succ i =>
        rw [Homotopy.prevD_succ_cochainComplex,homotopyComponent_succ,fullPositive_d]
        apply ModuleCat.hom_ext
        change LinearMap.id=(fullH D (i+2)).comp (fullD D (i+2))+
          (fullD D (i+1)).comp (fullH D (i+1))+_
        rw [sort_expandMap]
        exact (eq_sub_iff_add_eq.mp (fullH_identity D (i+1))).symm

 
def homotopyEquiv : HomotopyEquiv (fullPositive D) (FiniteModuleCech.positiveComplex D) where
  hom := sortMap D
  inv := expandMap D
  homotopyHomInvId := (normalizationHomotopy D).symm
  homotopyInvHomId := Homotopy.ofEq (expand_sortMap D)
end Lech.CechNormalization

end

end OAI
end


