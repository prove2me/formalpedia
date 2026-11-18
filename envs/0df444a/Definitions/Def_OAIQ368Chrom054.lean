-- Prove2me | Definitions.Def_OAIQ368Chrom054
-- name    : OAIQ368Chrom054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:58:02.448687+00:00
-- url     : https://prove2.me/theorems/733f92da-31f0-48f5-ada8-f1556d7f6e7b
-- title:
--   Definitions bundle OAIQ368Chrom054 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 375 declarations of OpenAI's Lean: 146 definitions, 9 instances and 220 theorems. The definitions and types are `OAI.ElementaryPositivity.EnergyLaurent.Admissible`, `OAI.ElementaryPositivity.EnergyLaurent.family`, `OAI.ElementaryPositivity.EnergyLaurent.series`, `OAI.ElementaryPositivity.EnergyLaurent.sigmaEnergyFiber`, `OAI.ElementaryPositivity.LinearFiltration.homogeneousMk`, `OAI.ElementaryPositivity.OrderedSignedWord`, `OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidTorusLaurentSeriesRatVUnit`, `OAI.ElementaryPositivity.RawShuffle.BlockRows`, `OAI.ElementaryPositivity.RawShuffle.DecoratedHN`, `OAI.ElementaryPositivity.RawShuffle.HNBasisIndex`, `OAI.ElementaryPositivity.RawShuffle.HNGradedIndex`, `OAI.ElementaryPositivity.RawShuffle.HNRowsIndex`, `OAI.ElementaryPositivity.RawShuffle.HNStringCoefficient`, `OAI.ElementaryPositivity.RawShuffle.HNStringIndex`, `OAI.ElementaryPositivity.RawShuffle.HomogeneousBIndex`, `OAI.ElementaryPositivity.RawShuffle.LowHNIndex`, `OAI.ElementaryPositivity.RawShuffle.LowHNWord`, `OAI.ElementaryPositivity.RawShuffle.OutputEnergyCoefficient`, `OAI.ElementaryPositivity.RawShuffle.PackExponent`, `OAI.ElementaryPositivity.RawShuffle.PrimitiveCounts`, `OAI.ElementaryPositivity.RawShuffle.RawAlgebra`, `OAI.ElementaryPositivity.RawShuffle.RowBlock`, `OAI.ElementaryPositivity.RawShuffle.SlopeStringStart`, `OAI.ElementaryPositivity.RawShuffle.SortedPackExponent`, `OAI.ElementaryPositivity.RawShuffle.StringBlockIndex`, `OAI.ElementaryPositivity.RawShuffle.blockRowsEnergy`, `OAI.ElementaryPositivity.RawShuffle.blockRowsEquiv`, `OAI.ElementaryPositivity.RawShuffle.blockWordEquiv`, `OAI.ElementaryPositivity.RawShuffle.decorateOutput`, `OAI.ElementaryPositivity.RawShuffle.decoratedDimension`, `OAI.ElementaryPositivity.RawShuffle.decoratedEnergy`, `OAI.ElementaryPositivity.RawShuffle.degreeQuotient`, `OAI.ElementaryPositivity.RawShuffle.degreeSection`, `OAI.ElementaryPositivity.RawShuffle.dimensionProduct`, `OAI.ElementaryPositivity.RawShuffle.gradeBEquiv`, `OAI.ElementaryPositivity.RawShuffle.hnBasisDegree`, `OAI.ElementaryPositivity.RawShuffle.hnExpansion`, `OAI.ElementaryPositivity.RawShuffle.hnExpansionRaw`, `OAI.ElementaryPositivity.RawShuffle.hnGradedBasis`, `OAI.ElementaryPositivity.RawShuffle.hnHomogeneousBasis` and 106 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_CompleteUnit`, `Chromatic_GradedAlgebra_EnergyLaurentFinite`, `Chromatic_GradedAlgebra_EnergyLaurentSeries`, `Chromatic_GradedAlgebra_FinitelySupportedUnitRows`, `Chromatic_GradedAlgebra_HomogeneousBasisFibre`, `Chromatic_GradedAlgebra_StringBackshift`, `Chromatic_GradedAlgebra_StringStripSeries`, `Chromatic_GradedAlgebra_UnitIndexEnergy`, `Chromatic_GradedAlgebra_WeightedPushTwist`, `Chromatic_QuantumTorus_StringStripDimension`, `Chromatic_QuantumTorus_UnitRowSelection`, `Chromatic_Shuffle_ComponentB`, `Chromatic_Shuffle_DimensionGrid`, `Chromatic_Shuffle_GlobalHilbertGrading`, `Chromatic_Shuffle_GradeBInternal`, `Chromatic_Shuffle_HNExpansion`, `Chromatic_Shuffle_HNHilbert`, `Chromatic_Shuffle_HNHomogeneousBasis`, `Chromatic_Shuffle_HNIndependent`, `Chromatic_Shuffle_HNPolynomial`, `Chromatic_Shuffle_HNThreshold`, `Chromatic_Shuffle_HNZeroRows`, `Chromatic_Shuffle_OriginalDegree`, `Chromatic_Shuffle_PackExponentSorting`, `Chromatic_Shuffle_PackOrbitBasis`, `Chromatic_Shuffle_PrimitiveBlockRows`, `Chromatic_Shuffle_PrimitiveStringBounds`, `Chromatic_Shuffle_PrimitiveUnitRows`, `Chromatic_Shuffle_RawGradedAlgebra`, `Chromatic_Shuffle_UnitalOriginalDegree`, `Chromatic_Walls_FiltrationHomogeneousRank`, `Chromatic_Walls_FiniteFibreFinsupp`, `Chromatic_Walls_FiniteReorderingEnergy`, `Chromatic_Walls_FiniteStringReordering`, `Chromatic_Walls_HNGeometry`, `Chromatic_Walls_HNSpanning`, `Chromatic_Walls_SignedMultiplicity`, `Chromatic_Walls_StringPositiveFactor`, `Chromatic_Walls_StringReorderingEnergy`, `Chromatic_Walls_StringStrip`, `Chromatic_Walls_ThresholdWords`, `Chromatic_Walls_TorusPositive`, `Chromatic_Walls_WeightedInverseAdjoint`.
--
--   **Imports.** It imports the bundles `OAIQ368Chrom038`, `OAIQ368Chrom051` and `OAIQ368Chrom053` of this split; the published statements `OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective`, `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom055` and `OAIQ368Chrom056`; the statement `OAI.ElementaryPositivity.RawShuffle.literalInput_primitiveFactor`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint`, `OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction`, `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain` and `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom038
import Definitions.Def_OAIQ368Chrom051
import Definitions.Def_OAIQ368Chrom053
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_hnPolynomialExpansion_injective
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_slopeStringCoefficient_bounds
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_stringPBWBasis_component

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_EnergyLaurentSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.EnergyLaurent
open scoped LaurentSeries
noncomputable section
variable {A B : Type*}

def Admissible (e : A → ℤ) : Prop :=
  (∃K : ℤ,∀a,e a≤K) ∧ ∀E : ℤ,Finite {a // e a=E}

def family (e : A → ℤ) (h : Admissible e) : HahnSeries.SummableFamily ℤ ℚ A where
  toFun a := HahnSeries.single (-e a) 1
  isPWO_iUnion_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    obtain ⟨K,hK⟩:=h.1
    refine ⟨-K,?_⟩
    intro j hj
    simp only [Set.mem_iUnion,HahnSeries.support_single_of_ne (by norm_num : (1:ℚ)≠0),
      Set.mem_singleton_iff] at hj
    obtain ⟨a,rfl⟩:=hj
    exact neg_le_neg (hK a)
  finite_co_support' j := by
    have hs : {a : A | (HahnSeries.single (-e a) (1:ℚ)).coeff j≠0}={a | e a= -j} := by
      ext a
      simp only [HahnSeries.coeff_single,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not,
        Set.mem_ofPred_eq]
      omega
    rw [hs]
    exact Set.finite_coe_iff.mp (h.2 (-j))

def series (e : A → ℤ) (h : Admissible e) : LaurentSeries ℚ := (family e h).hsum

lemma admissible_prod {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f) :
    Admissible (fun p : A×B=>e p.1+f p.2) := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    obtain ⟨L,hL⟩:=hf.1
    exact ⟨K+L,fun p=>add_le_add (hK p.1) (hL p.2)⟩
  · intro E
    have hs := ((family e he).mul (family f hf)).finite_co_support (-E)
    have hh : {p : A×B | (((family e he).mul (family f hf)) p).coeff (-E)≠0}=
        {p : A×B | e p.1+f p.2=E} := by
      ext p
      change (HahnSeries.single (-e p.1) (1:ℚ)*HahnSeries.single (-f p.2) 1).coeff (-E)≠0 ↔ _
      rw [HahnSeries.single_mul_single,mul_one,HahnSeries.coeff_single]
      simp only [ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not,Set.mem_ofPred_eq]
      omega
    change {p : A×B | (((family e he).mul (family f hf)) p).coeff (-E)≠0}.Finite at hs
    rw [hh] at hs
    exact hs.to_subtype

lemma admissible_shift {e : A → ℤ} (he : Admissible e) (k : ℤ) :
    Admissible (fun a=>e a+k) := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    exact ⟨K+k,fun a=>add_le_add (hK a) le_rfl⟩
  · intro E
    let T:={a : A // e a=E-k}
    let : Finite T:=he.2 (E-k)
    exact Finite.of_injective (fun a : {a : A // e a+k=E}=>
      (⟨a.val,by have h:=a.property; omega⟩:T))
        (fun _ _ h=>Subtype.ext (congrArg (fun t:T=>t.val) h))

end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_UnitIndexEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
noncomputable section

def weight {n : ℕ} (f : Fin n → ℕ) : ℤ := ∑i,(f i:ℤ)

abbrev UnitIndex (a n : ℕ) := {f : Fin n → ℕ // if a=0 then StrictMono f else Monotone f}

def unitWeight (a n : ℕ) (q : UnitIndex a n) : ℤ := weight q.val

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_CompleteUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.EnergyLaurent
open scoped LaurentSeries
noncomputable section

lemma admissible_equiv {A B : Type*} {e : A → ℤ} {f : B → ℤ}
    (he : Admissible e) (q : A ≃ B) (hq : ∀a,f (q a)=e a) : Admissible f := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    refine ⟨K,fun b=>?_⟩
    have hh:=hK (q.symm b)
    rw [←hq (q.symm b),q.apply_symm_apply] at hh
    exact hh
  · intro E
    let := he.2 E
    exact Finite.of_equiv {a // e a=E} (q.subtypeEquiv (fun a=>by rw [hq]))

end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_EnergyLaurentFinite
attribute [-instance] _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.EnergyLaurent
noncomputable section
variable {A : Type*} {e : A → ℤ}

variable {J : Type*} [Fintype J] {B : J → Type*} (f : ∀j,B j → ℤ)

def sigmaEnergyFiber (E : ℤ) :
    {x : Σj,B j // f x.1 x.2=E} ≃ Σj,{x : B j // f j x=E} where
  toFun x:=⟨x.val.1,⟨x.val.2,x.property⟩⟩
  invFun x:=⟨⟨x.1,x.2.val⟩,x.2.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

lemma admissible_sigma (hf : ∀j,Admissible (f j)) :
    Admissible (fun x : Σj,B j=>f x.1 x.2) := by
  classical
  constructor
  · let K : J → ℤ:=fun j=>Classical.choose (hf j).1
    refine ⟨∑j,|K j|,fun x=>?_⟩
    have H : f x.1 x.2≤K x.1 := Classical.choose_spec (hf x.1).1 x.2
    exact H.trans ((le_abs_self _).trans (Finset.single_le_sum (f:=fun j=>|K j|) (fun j _=>abs_nonneg (K j)) (Finset.mem_univ x.1)))
  · intro E
    let : ∀j,Finite {x : B j // f j x=E} := fun j=>(hf j).2 E
    exact Finite.of_equiv _ (sigmaEnergyFiber f E).symm

end
end ElementaryPositivity.EnergyLaurent

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SignedMultiplicity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.SignedMultiplicity
variable {α : Type*} [DecidableEq α]

lemma pairwise_iff_count (even : α → Prop) (w : List α) :
    w.Pairwise (fun x y=>x=y → even x) ↔ ∀a,¬even a → w.count a≤1 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.pairwise_cons,ih]
    constructor
    · rintro ⟨hh,ht⟩ a ha
      by_cases hx : x=a
      · subst a
        have hn : x∉w := fun he=>ha (hh x he rfl)
        simp only [List.count_cons_self, List.count_eq_zero_of_not_mem hn]
        omega
      · simpa [List.count_cons,hx,eq_comm] using ht a ha
    · intro h
      constructor
      · intro y hy hxy
        subst y
        by_contra hn
        have hb:=h x hn
        have hp : 0<w.count x := List.count_pos_iff.mpr hy
        simp only [List.count_cons_self] at hb
        omega
      · intro a ha
        have hb:=h a ha
        have hl : w.count a≤(x::w).count a := List.count_le_count_cons
        omega

section Ordered
variable [LinearOrder α]

abbrev Word (even : α → Prop) :=
  {w : List α // w.Pairwise (·≤·) ∧ w.Pairwise (fun x y=>x=y → even x)}
abbrev Selection (even : α → Prop) := {m : Multiset α // ∀a,¬even a → m.count a≤1}

def wordSelectionEquiv (even : α → Prop) : Word even ≃ Selection even where
  toFun w:=⟨(w.val:Multiset α),by
    simpa only [Multiset.coe_count] using (pairwise_iff_count even w.val).mp w.property.2⟩
  invFun m:=⟨m.val.sort (·≤·),Multiset.pairwise_sort _ _,by
    apply (pairwise_iff_count even _).mpr
    intro a ha
    have hh:=m.property a ha
    simpa only [←Multiset.coe_count,Multiset.sort_eq] using hh⟩
  left_inv w:=by
    apply Subtype.ext
    change (w.val:Multiset α).sort (·≤·)=w.val
    exact List.Perm.eq_of_pairwise' (Multiset.pairwise_sort (w.val:Multiset α) (·≤·)) w.property.1
      (Quotient.exact (Multiset.sort_eq (w.val:Multiset α) (·≤·)))
  right_inv m:=Subtype.ext (Multiset.sort_eq m.val (·≤·))

abbrev CountSelection (even : α → Prop) := {f : α →₀ ℕ // ∀a,¬even a → f a≤1}

noncomputable def selectionCountEquiv (even : α → Prop) : Selection even ≃ CountSelection even :=
  Multiset.toFinsupp.toEquiv.subtypeEquiv (fun m=>by
    rfl)

noncomputable def wordCountEquiv (even : α → Prop) : Word even ≃ CountSelection even :=
  (wordSelectionEquiv even).trans (selectionCountEquiv even)
end Ordered
end ElementaryPositivity.SignedMultiplicity
end
namespace ElementaryPositivity.UnitSelections
noncomputable section
def unitEnergy (a n : ℕ) (k : ℤ) (f : UnitIndex a n) : ℤ :=
  (n:ℤ)*k-2*unitWeight a n f
end
end ElementaryPositivity.UnitSelections

section
namespace ElementaryPositivity.SignedMultiplicity
variable {A B : Type*}

lemma multiset_count_sum [DecidableEq A] {T : Type*} [AddCommMonoid T]
    (m : Multiset A) (e : A → T) :
    m.toFinsupp.sum (fun x n=>n • e x)=(m.map e).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    change (({x}:Multiset A)+m).toFinsupp.sum _=((({x}:Multiset A)+m).map e).sum
    rw [Multiset.toFinsupp_add]
    rw [Finsupp.sum_add_index' (h:=fun x n=>n • e x) (by simp)
      (by intro a b c; exact add_nsmul (e a) b c)]
    simp only [Multiset.toFinsupp_singleton,Multiset.map_add,Multiset.sum_add,
      Multiset.map_singleton,Multiset.sum_singleton,ih]
    rw [Finsupp.sum_single_index (h:=fun x n=>n • e x) (by simp),one_nsmul]

def countReindex (e : A ≃ B) (evenA : A → Prop) (evenB : B → Prop)
    (he : ∀a,evenA a ↔ evenB (e a)) : CountSelection evenA ≃ CountSelection evenB :=
  (Finsupp.equivCongrLeft e).subtypeEquiv (fun f=>by
    constructor
    · intro h b hb
      have ha : ¬evenA (e.symm b) := by simpa only [he,Equiv.apply_symm_apply] using hb
      exact h (e.symm b) ha
    · intro h a ha
      have hb : ¬evenB (e a):=by simpa only [he] using ha
      have hh:=h (e a) hb
      simpa only [Finsupp.equivCongrLeft_apply,Finsupp.equivMapDomain_apply,
        Equiv.symm_apply_apply] using hh)

lemma countReindex_sum (e : A ≃ B) (evenA : A → Prop) (evenB : B → Prop)
    (he : ∀a,evenA a ↔ evenB (e a)) (f : CountSelection evenA)
    {T : Type*} [AddCommMonoid T] (energy : B → T) :
    (countReindex e evenA evenB he f).val.sum (fun b n=>n • energy b)=
      f.val.sum (fun a n=>n • energy (e a)) :=
  Finsupp.sum_equivMapDomain e f.val (fun b n=>n • energy b)
end ElementaryPositivity.SignedMultiplicity
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_UnitRowSelection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity
noncomputable section

def unitSigmaSubtype (a : ℕ) : (Σn,UnitIndex a n) ≃
    {q : Σn,Fin n → ℕ // if a=0 then StrictMono q.2 else Monotone q.2} where
  toFun q:=⟨⟨q.1,q.2.val⟩,q.2.property⟩
  invFun q:=⟨q.val.1,⟨q.val.2,q.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

lemma ofFn_signed_iff (a n : ℕ) (f : Fin n → ℕ) :
    (if a=0 then StrictMono f else Monotone f) ↔
      (List.ofFn f).Pairwise (·≤·) ∧
        (List.ofFn f).Pairwise (fun x y=>x=y → a≠0) := by
  rw [List.pairwise_ofFn,List.pairwise_ofFn]
  by_cases h : a=0
  · simp only [ite_eq_left h]
    constructor
    · intro hf
      exact ⟨fun i j hij=>(hf hij).le,fun i j hij he=>False.elim ((hf hij).ne he)⟩
    · rintro ⟨hl,he⟩ i j hij
      exact lt_of_le_of_ne (hl hij) (fun hx=>he hij hx h)
  · simp only [ite_eq_right h]
    constructor
    · intro hf
      exact ⟨fun i j hij=>hf hij.le,fun _ _ _ _=>h⟩
    · rintro ⟨hl,_⟩ i j hij
      rcases hij.eq_or_lt with he|hlt
      · subst j; rfl
      · exact hl hlt

def unitWordEquiv (a : ℕ) : (Σn,UnitIndex a n) ≃ Word (fun _ : ℕ=>a≠0) :=
  (unitSigmaSubtype a).trans
    (List.equivSigmaTuple.symm.subtypeEquiv (fun q=>ofFn_signed_iff a q.1 q.2))

def unitRowSelection (a : ℕ) : (Σn,UnitIndex a n) ≃ Selection (fun _ : ℕ=>a≠0) :=
  (unitWordEquiv a).trans (wordSelectionEquiv _)

def unitRowCount (a : ℕ) : (Σn,UnitIndex a n) ≃ CountSelection (fun _ : ℕ=>a≠0) :=
  (unitWordEquiv a).trans (wordCountEquiv _)

lemma unitRowSelection_val (a n : ℕ) (f : UnitIndex a n) :
    (unitRowSelection a ⟨n,f⟩).val=(List.ofFn f.val:Multiset ℕ) := rfl

lemma unitRowSelection_card (a n : ℕ) (f : UnitIndex a n) :
    (unitRowSelection a ⟨n,f⟩).val.card=n := by
  rw [unitRowSelection_val,Multiset.coe_card,List.length_ofFn]

lemma unitRowSelection_energy (a n : ℕ) (k : ℤ) (f : UnitIndex a n) :
    (((unitRowSelection a ⟨n,f⟩).val).map (fun j:ℕ=>k-2*(j:ℤ))).sum=unitEnergy a n k f := by
  rw [unitRowSelection_val,Multiset.map_coe,Multiset.sum_coe,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_def,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,unitEnergy,unitWeight,weight]
end
end ElementaryPositivity.UnitSelections
end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity
noncomputable section

lemma multiset_count_energy {A : Type*} [DecidableEq A] (m : Multiset A) (e : A → ℤ) :
    m.toFinsupp.sum (fun x n=>n • e x)=(m.map e).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    change (({x}:Multiset A)+m).toFinsupp.sum _=((({x}:Multiset A)+m).map e).sum
    rw [Multiset.toFinsupp_add]
    rw [Finsupp.sum_add_index' (h:=fun x n=>n • e x) (by simp) (by intro a b c; exact add_nsmul (e a) b c)]
    simp only [Multiset.toFinsupp_singleton,Multiset.map_add,Multiset.sum_add,
      Multiset.map_singleton,Multiset.sum_singleton,ih]
    rw [Finsupp.sum_single_index (h:=fun x n=>n • e x) (by simp),one_nsmul]

lemma unitRowCount_energy (a n : ℕ) (k : ℤ) (f : UnitIndex a n) :
    (unitRowCount a ⟨n,f⟩).val.sum (fun j r=>r • (k-2*(j:ℤ)))=unitEnergy a n k f := by
  change ((unitRowSelection a ⟨n,f⟩).val).toFinsupp.sum _=_
  rw [multiset_count_energy,unitRowSelection_energy]

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_FinitelySupportedUnitRows
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity
noncomputable section
variable {S : Type*} (a : S → ℕ)

lemma unitRowCount_sum (b : ℕ) (q : Σn,UnitIndex b n) :
    (unitRowCount b q).val.sum (fun _ m=>m)=q.1 := by
  change ((unitRowSelection b q).val).toFinsupp.sum (fun _ m=>m)=q.1
  exact (Multiset.toFinsupp_sum_eq _).trans (unitRowSelection_card b q.1 q.2)

abbrev SupportedUnitRows := {r : ∀s,Σn,UnitIndex (a s) n //
  (Function.support (fun s=>(unitRowCount (a s) (r s)).val)).Finite}

def columnRow (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) (s : S) :
    CountSelection (fun _ : ℕ=>a s≠0) :=
  ⟨f.val.curry s,fun j h=>f.property (s,j) h⟩

def columnRows (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) : SupportedUnitRows a :=
  ⟨fun s=>(unitRowCount (a s)).symm (columnRow a f s),by
    have he : (fun s=>(unitRowCount (a s)
        ((unitRowCount (a s)).symm (columnRow a f s))).val)=f.val.curry := by
      funext s
      rw [Equiv.apply_symm_apply]
      rfl
    rw [he]
    exact Finsupp.hasFiniteSupport f.val.curry⟩

def rowsColumn (r : SupportedUnitRows a) : CountSelection (fun u : S×ℕ=>a u.1≠0) :=
  ⟨(Finsupp.ofSupportFinite (fun s=>(unitRowCount (a s) (r.val s)).val) r.property).uncurry,
    fun u h=>(unitRowCount (a u.1) (r.val u.1)).property u.2 h⟩

def allUnitRowsEquiv : CountSelection (fun u : S×ℕ=>a u.1≠0) ≃ SupportedUnitRows a where
  toFun:=columnRows a
  invFun:=rowsColumn a
  left_inv f:=by
    apply Subtype.ext
    ext u
    change ((unitRowCount (a u.1)) ((unitRowCount (a u.1)).symm (columnRow a f u.1))).val u.2=f.val u
    rw [Equiv.apply_symm_apply]
    rfl
  right_inv r:=by
    apply Subtype.ext
    funext s
    apply (unitRowCount (a s)).injective
    change (unitRowCount (a s)) ((unitRowCount (a s)).symm (columnRow a (rowsColumn a r) s))=_
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    ext j
    rfl

lemma allUnitRows_count (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) (s : S) :
    (unitRowCount (a s) ((allUnitRowsEquiv a f).val s)).val=f.val.curry s := by
  change (unitRowCount (a s) ((unitRowCount (a s)).symm (columnRow a f s))).val=_
  rw [Equiv.apply_symm_apply]
  rfl

lemma allUnitRows_energy (k : S → ℤ) (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    f.val.sum (fun u m=>m • (k u.1-2*(u.2:ℤ)))=
      f.val.curry.sum (fun s _=>unitEnergy (a s)
        ((allUnitRowsEquiv a f).val s).1 (k s) ((allUnitRowsEquiv a f).val s).2) := by
  rw [←Finsupp.sum_curry_index f.val (fun s j m=>m • (k s-2*(j:ℤ)))]
  apply Finset.sum_congr rfl
  intro s _
  rw [←allUnitRows_count a f s]
  exact unitRowCount_energy (a s) ((allUnitRowsEquiv a f).val s).1 (k s) ((allUnitRowsEquiv a f).val s).2

lemma allUnitRows_dimension {T : Type*} [AddCommMonoid T] (dim : S → T)
    (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    f.val.sum (fun u m=>m • dim u.1)=
      f.val.curry.sum (fun s _=>((allUnitRowsEquiv a f).val s).1 • dim s) := by
  rw [←Finsupp.sum_curry_index f.val (fun s _ m=>m • dim s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [←allUnitRows_count a f s]
  change (∑j∈(unitRowCount (a s) ((allUnitRowsEquiv a f).val s)).val.support,
    (unitRowCount (a s) ((allUnitRowsEquiv a f).val s)).val j • dim s)=_
  rw [←Finset.sum_smul]
  congr 1
  exact unitRowCount_sum (a s) ((allUnitRowsEquiv a f).val s)

def rowFinsupp (r : SupportedUnitRows a) : S →₀ ℕ →₀ ℕ :=
  Finsupp.ofSupportFinite (fun s=>(unitRowCount (a s) (r.val s)).val) r.property

lemma rowFinsupp_equiv (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    rowFinsupp a (allUnitRowsEquiv a f)=f.val.curry := by
  ext s j
  exact congrArg (fun r : ℕ →₀ ℕ=>r j) (allUnitRows_count a f s)

def rowsDimension {T : Type*} [AddCommMonoid T] (dim : S → T) (r : SupportedUnitRows a) : T :=
  (rowFinsupp a r).sum (fun s _=>(r.val s).1 • dim s)

def rowsEnergy (k : S → ℤ) (r : SupportedUnitRows a) : ℤ :=
  (rowFinsupp a r).sum (fun s _=>unitEnergy (a s) (r.val s).1 (k s) (r.val s).2)

lemma rowsDimension_equiv {T : Type*} [AddCommMonoid T] (dim : S → T)
    (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    rowsDimension a dim (allUnitRowsEquiv a f)=f.val.sum (fun u m=>m • dim u.1) := by
  rw [rowsDimension,rowFinsupp_equiv]
  exact (allUnitRows_dimension a dim f).symm

lemma rowsEnergy_equiv (k : S → ℤ) (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    rowsEnergy a k (allUnitRowsEquiv a f)=f.val.sum (fun u m=>m • (k u.1-2*(u.2:ℤ))) := by
  rw [rowsEnergy,rowFinsupp_equiv]
  exact (allUnitRows_energy a k f).symm

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HomogeneousBasisFibre
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open Module
attribute [local instance] Classical.propDecidable
variable {M J K : Type*} [DecidableEq K] [AddCommGroup M] [Module ℚ M]
variable (b : Basis J ℚ M) (degree : J → K) (p : K → Module.End ℚ M)
variable (hp : ∀ k i,p k (b i)=if degree i=k then b i else 0)

include hp in
lemma homogeneousBasis_span (k : K) :
    Submodule.span ℚ (Set.range (fun i : {i : J // degree i=k}=>b i.val))=LinearMap.range (p k) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨b i.val,by rw [hp,ite_eq_left i.property]⟩
  · rintro _ ⟨x,rfl⟩
    have hx := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩:=hy
      rw [hp]
      split_ifs with h
      · exact Submodule.subset_span ⟨⟨i,h⟩,rfl⟩
      · exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul r x hx ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

noncomputable def homogeneousBasisFibre (k : K) :
    Basis {i : J // degree i=k} ℚ (LinearMap.range (p k)) :=
  (Basis.span (b.linearIndependent.comp _ Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (homogeneousBasis_span b degree p hp k))

include b hp in
lemma homogeneousBasis_finite (k : K) [Module.Finite ℚ (LinearMap.range (p k))] :
    Finite {i : J // degree i=k} :=
  Module.Finite.finite_basis (homogeneousBasisFibre b degree p hp k)

include b hp in
lemma homogeneousBasis_finrank (k : K) [Module.Finite ℚ (LinearMap.range (p k))] :
    Module.finrank ℚ (LinearMap.range (p k))=Nat.card {i : J // degree i=k} := by
  let := homogeneousBasis_finite b degree p hp k
  let := Fintype.ofFinite {i : J // degree i=k}
  rw [Module.finrank_eq_card_basis (homogeneousBasisFibre b degree p hp k),Nat.card_eq_fintype_card]
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DimensionGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
noncomputable section
variable {I A B : Type*} (δ : A → I → ℕ) (ε : B → I → ℕ)

lemma subtypePair_heq {p q : A → Prop} {r s : B → Prop}
    (hp : p=q) (hr : r=s) (x : A) (y : B)
    (hx : p x) (hy : r y) (hx' : q x) (hy' : s y) :
    HEq ((⟨x,hx⟩ : Subtype p),(⟨y,hy⟩ : Subtype r))
      ((⟨x,hx'⟩ : Subtype q),(⟨y,hy'⟩ : Subtype s)) := by
  cases hp
  cases hr
  rfl

def dimensionProduct (d : I → ℕ) :
    (Σ s : DimensionSplit d,{x : A // δ x=s.left} × {y : B // ε y=s.right}) ≃
      {p : A×B // δ p.1+ε p.2=d} where
  toFun x:=⟨(x.2.1.val,x.2.2.val),by rw [x.2.1.property,x.2.2.property,DimensionSplit.left_add_right]⟩
  invFun p:=⟨DimensionSplit.ofPair (δ p.val.1) (ε p.val.2) p.property,
    ⟨p.val.1,rfl⟩,⟨p.val.2,(DimensionSplit.right_ofPair _ _ _).symm⟩⟩
  right_inv p:=rfl
  left_inv x:=by
    rcases x with ⟨s,⟨x,hx⟩,⟨y,hy⟩⟩
    dsimp only
    have hs : DimensionSplit.ofPair (δ x) (ε y) (by rw [hx,hy,DimensionSplit.left_add_right])=s := by
      apply DimensionSplit.ext
      exact hx
    apply Sigma.ext hs
    exact subtypePair_heq (congrArg (fun t : DimensionSplit d=>fun z=>δ z=t.left) hs)
      (congrArg (fun t : DimensionSplit d=>fun z=>ε z=t.right) hs) x y _ _ _ _

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StringStrip
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SignedMultiplicity
noncomputable section
variable {A B : Type*} (evenA : A → Prop) (evenB : B → Prop)

def countSumEquiv : CountSelection (Sum.elim evenA evenB) ≃
    CountSelection evenA × CountSelection evenB where
  toFun f:=⟨⟨(Finsupp.sumFinsuppEquivProdFinsupp f.val).1,fun a ha=>f.property (.inl a) ha⟩,
    ⟨(Finsupp.sumFinsuppEquivProdFinsupp f.val).2,fun b hb=>f.property (.inr b) hb⟩⟩
  invFun fg:=⟨fg.1.val.sumElim fg.2.val,by
    intro x hx
    cases x with
    | inl a=>exact fg.1.property a hx
    | inr b=>exact fg.2.property b hx⟩
  left_inv f:=by
    apply Subtype.ext
    exact Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply f.val
  right_inv fg:=by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply (fg.1.val,fg.2.val))
    · apply Subtype.ext
      exact congrArg Prod.snd (Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply (fg.1.val,fg.2.val))

lemma countSum_sum {T : Type*} [AddCommMonoid T]
    (f : CountSelection (Sum.elim evenA evenB)) (e : A ⊕ B → T) :
    f.val.sum (fun x n=>n • e x)=
      ((countSumEquiv evenA evenB f).1).val.sum (fun a n=>n • e (.inl a))+
      ((countSumEquiv evenA evenB f).2).val.sum (fun b n=>n • e (.inr b)) := by
  have H:=Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply f.val
  change ((Finsupp.sumFinsuppEquivProdFinsupp f.val).1.sumElim
    (Finsupp.sumFinsuppEquivProdFinsupp f.val).2)=f.val at H
  conv_lhs=>rw [←H]
  exact Finsupp.sum_sumElim _ _ _
end
end ElementaryPositivity.SignedMultiplicity

namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity
noncomputable section
variable {S : Type*} (a : S → ℕ) (t : S → ℕ)

abbrev HeadLevel := Σs,Fin (t s)

def levelCutEquiv : S×ℕ ≃ HeadLevel t ⊕ (S×ℕ) where
  toFun x:=if h:x.2<t x.1 then .inl ⟨x.1,⟨x.2,h⟩⟩ else .inr (x.1,x.2-t x.1)
  invFun x:=Sum.elim (fun x : HeadLevel t=>(x.1,x.2.val))
    (fun x : S×ℕ=>(x.1,x.2+t x.1)) x
  left_inv x:=by
    dsimp only
    split_ifs with h
    · rfl
    · change (x.1,x.2-t x.1+t x.1)=x
      exact Prod.ext rfl (Nat.sub_add_cancel (Nat.le_of_not_gt h))
  right_inv x:=by
    cases x with
    | inl x=>
      dsimp only [Sum.elim_inl]
      rw [dite_eq_left x.2.isLt]
    | inr x=>
      dsimp only [Sum.elim_inr]
      rw [dite_eq_right (show ¬x.2+t x.1<t x.1 by omega),Nat.add_sub_cancel_right]

lemma levelCut_even (x : S×ℕ) :
    (a x.1≠0) ↔ Sum.elim (fun x : HeadLevel t=>a x.1≠0)
      (fun x : S×ℕ=>a x.1≠0) (levelCutEquiv t x) := by
  dsimp only [levelCutEquiv,Equiv.coe_fn_mk]
  split_ifs <;> rfl

def stringStripEquiv : CountSelection (fun x : S×ℕ=>a x.1≠0) ≃
    CountSelection (fun x : HeadLevel t=>a x.1≠0) ×
      CountSelection (fun x : S×ℕ=>a x.1≠0) :=
  (countReindex (levelCutEquiv t) _ _ (levelCut_even a t)).trans
    (countSumEquiv _ _)

lemma stringStrip_sum {T : Type*} [AddCommMonoid T]
    (f : CountSelection (fun x : S×ℕ=>a x.1≠0)) (e : S×ℕ → T) :
    f.val.sum (fun x n=>n • e x)=
      (stringStripEquiv a t f).1.val.sum (fun x n=>n • e (x.1,x.2.val))+
      (stringStripEquiv a t f).2.val.sum (fun x n=>n • e (x.1,x.2+t x.1)) := by
  have H:=countReindex_sum (levelCutEquiv t) _ _ (levelCut_even a t) f
    (fun x=>e ((levelCutEquiv t).symm x))
  simp only [Equiv.symm_apply_apply] at H
  rw [←H,countSum_sum]
  rfl

lemma stringStrip_dimension {T : Type*} [AddCommMonoid T] (dim : S → T)
    (f : CountSelection (fun x : S×ℕ=>a x.1≠0)) :
    f.val.sum (fun x n=>n • dim x.1)=
      (stringStripEquiv a t f).1.val.sum (fun x n=>n • dim x.1)+
      (stringStripEquiv a t f).2.val.sum (fun x n=>n • dim x.1) :=
  stringStrip_sum a t f (fun x=>dim x.1)

lemma stringStrip_energy (k : S → ℤ)
    (f : CountSelection (fun x : S×ℕ=>a x.1≠0)) :
    f.val.sum (fun x n=>n • (k x.1+2*(t x.1:ℤ)-2*(x.2:ℤ)))=
      (stringStripEquiv a t f).1.val.sum (fun x n=>n • (k x.1+2*(t x.1:ℤ)-2*(x.2.val:ℤ)))+
      (stringStripEquiv a t f).2.val.sum (fun x n=>n • (k x.1-2*(x.2:ℤ))) := by
  rw [stringStrip_sum]
  congr 1
  apply Finsupp.sum_congr
  intro x hx
  congr 1
  simp only [Nat.cast_add]
  ring
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.SignedMultiplicity
noncomputable section
variable {S I : Type*} (even : S → Prop) (dim : S → (I → ℕ))

def countDimension (f : CountSelection even) : I → ℕ :=
  f.val.sum (fun s n=>n • dim s)

def zeroCount : CountSelection even := ⟨0,by simp⟩

@[simp] lemma countDimension_zero : countDimension even dim (zeroCount even)=0 := by
  simp [countDimension,zeroCount]

lemma countDimension_apply (f : CountSelection even) (i : I) :
    countDimension even dim f i=∑s∈f.val.support,f.val s*dim s i := by
  simp [countDimension,Finsupp.sum,Finset.sum_apply]

lemma count_eq_zero_of_dimension (hdim : ∀s,dim s≠0) (f : CountSelection even)
    (h : countDimension even dim f=0) : f=zeroCount even := by
  classical
  apply Subtype.ext
  ext s
  by_contra H
  have hs : s∈f.val.support := Finsupp.mem_support_iff.mpr (by simpa [zeroCount] using H)
  obtain ⟨i,hi⟩:=Function.ne_iff.mp (hdim s)
  have HE:=congrArg (fun d : I→ℕ=>d i) h
  rw [countDimension_apply] at HE
  have HB : f.val s*dim s i≤0 :=
    (Finset.single_le_sum (fun _ _=>Nat.zero_le _) hs).trans_eq HE
  have hf : 0<f.val s := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs)
  have hd : 0<dim s i := Nat.pos_of_ne_zero hi
  exact (not_lt_of_ge HB) (Nat.mul_pos hf hd)

abbrev DimensionCounts (d : I → ℕ) := {f : CountSelection even // countDimension even dim f=d}

include dim in
lemma dimensionCounts_zero_subsingleton (hdim : ∀s,dim s≠0) :
    Subsingleton (DimensionCounts even dim 0) := by
  constructor
  intro f g
  apply Subtype.ext
  exact (count_eq_zero_of_dimension even dim hdim f.val f.property).trans
    (count_eq_zero_of_dimension even dim hdim g.val g.property).symm

def countEnergy (e : S → ℤ) (f : CountSelection even) : ℤ := f.val.sum (fun s n=>n • e s)

@[simp] lemma countEnergy_zero (e : S → ℤ) : countEnergy even e (zeroCount even)=0 := by
  simp [countEnergy,zeroCount]

lemma dimensionCounts_zero_energy (hdim : ∀s,dim s≠0) (e : S → ℤ)
    (f : DimensionCounts even dim 0) : countEnergy even e f.val=0 := by
  rw [count_eq_zero_of_dimension even dim hdim f.val f.property,countEnergy_zero]

lemma countDimension_mem (D : AddSubmonoid (I → ℕ)) (hd : ∀s,dim s∈D) (f : CountSelection even) :
    countDimension even dim f∈D := by
  unfold countDimension Finsupp.sum
  exact D.sum_mem (fun s hs=>D.nsmul_mem (hd s) _)

lemma countEnergy_shift (τ : (I→ℕ) →+ ℤ) (e : S → ℤ) (f : CountSelection even) :
    countEnergy even (fun s=>e s+τ (dim s)) f=
      countEnergy even e f+τ (countDimension even dim f) := by
  simp only [countEnergy,countDimension,Finsupp.sum,map_sum,map_nsmul,smul_add,Finset.sum_add_distrib]
end
end ElementaryPositivity.SignedMultiplicity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_StringStripDimension
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle
noncomputable section
variable {S I : Type*} (a : S → ℕ) (t : S → ℕ) (dim : S → (I → ℕ))

abbrev StringCounts (d : I → ℕ) :=
  DimensionCounts (fun x : S×ℕ=>a x.1≠0) (fun x=>dim x.1) d
abbrev StripCounts (d : I → ℕ) :=
  DimensionCounts (fun x : HeadLevel t=>a x.1≠0) (fun x=>dim x.1) d

def stringStripDimensionEquiv (d : I → ℕ) :
    StringCounts a dim d ≃ Σs : DimensionSplit d,StripCounts a t dim s.left × StringCounts a dim s.right :=
  ((stringStripEquiv a t).subtypeEquiv (fun _=>by
    rw [countDimension,stringStrip_dimension]
    rfl)).trans (dimensionProduct (countDimension _ (fun x : HeadLevel t=>dim x.1))
      (countDimension _ (fun x : S×ℕ=>dim x.1)) d).symm

def stringEnergy (k : S → ℤ) (d : I → ℕ) (x : StringCounts a dim d) : ℤ :=
  countEnergy _ (fun x=>k x.1-2*(x.2:ℤ)) x.val

def stripEnergy (k : S → ℤ) (d : I → ℕ) (x : StripCounts a t dim d) : ℤ :=
  countEnergy _ (fun x=>k x.1+2*(t x.1:ℤ)-2*(x.2.val:ℤ)) x.val

lemma stringEnergy_shift (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
    (k : S → ℤ) (d : I → ℕ) (x : StringCounts a dim d) :
    stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d x=
      stringEnergy a dim k d x+2*τ d := by
  have H : (fun x : S×ℕ=>k x.1+2*(t x.1:ℤ)-2*(x.2:ℤ))=
      (fun x=>k x.1-2*(x.2:ℤ)+(2 • τ) (dim x.1)) := by
    funext x
    rw [hτ]
    simp only [AddMonoidHom.nsmul_apply,nsmul_eq_mul]
    ring
  change countEnergy _ _ x.val=_
  rw [H,countEnergy_shift,x.property]
  rfl

def stripInsert (d : I → ℕ) (x : StripCounts a t dim d) : StringCounts a dim d :=
  ⟨(stringStripEquiv a t).symm (x.val,zeroCount _),by
    change (_:S×ℕ→₀ℕ).sum _=d
    rw [stringStrip_dimension a t dim]
    simp only [Equiv.apply_symm_apply,zeroCount,Finsupp.sum_zero_index,add_zero]
    exact x.property⟩

lemma stripInsert_injective (d : I → ℕ) : Function.Injective (stripInsert a t dim d) := by
  intro x y H
  apply Subtype.ext
  have H':=congrArg (fun z : StringCounts a dim d=> (stringStripEquiv a t z.val).1) H
  simpa only [stripInsert,Equiv.apply_symm_apply] using H'

lemma stripInsert_energy (k : S → ℤ) (d : I → ℕ) (x : StripCounts a t dim d) :
    stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d (stripInsert a t dim d x)=
      stripEnergy a t dim k d x := by
  change ((stringStripEquiv a t).symm (x.val,zeroCount _)).val.sum
    (fun z n=>n • (k z.1+2*(t z.1:ℤ)-2*(z.2:ℤ)))=_
  rw [stringStrip_energy a t k]
  simp only [Equiv.apply_symm_apply,zeroCount,Finsupp.sum_zero_index,add_zero]
  rfl

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ComponentB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem gradeB_finite_independent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (s : Finset ℤ) (f : ℤ → B a μ d)
    (hf : ∀ k∈s,f k∈gradeB a μ d k) (hz : ∑ k ∈ s,f k=0) :
    ∀ k∈s,f k=0 := by
  classical
  intro k hk
  have h := congrArg (componentB a μ d k) hz
  rw [map_sum,map_zero] at h
  have heq : ∑ l ∈ s,componentB a μ d k (f l) = f k := by
    rw [Finset.sum_eq_single k]
    · exact (mem_gradeB_iff a μ d k _).mp (hf k hk)
    · intro l hl hlk
      rw [componentB_on_grade a μ d k l _ (hf l hl),ite_eq_right (Ne.symm hlk)]
    · exact fun hn=>(hn hk).elim
  rwa [heq] at h

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GradeBInternal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem gradeB_internal (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    DirectSum.IsInternal (gradeB a μ d) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
      (gradeB_finite_independent a μ d)
  · apply top_unique
    intro f hf
    obtain ⟨s,hs,heq⟩ := componentB_finite_decomposition a μ d f
    rw [← heq]
    apply Submodule.sum_mem
    intro k hk
    apply (le_iSup (gradeB a μ d) k)
    exact ⟨f,rfl⟩

lemma intWeight_eq_natWeight {σ : Type*} (x : σ →₀ ℕ) :
    Finsupp.weight (fun _=>(1:ℤ)) x = (Finsupp.weight (fun _=>(1:ℕ)) x : ℤ) := by
  classical
  simp [Finsupp.weight_apply,Finsupp.sum]

lemma homogeneous_int_nat {σ : Type*} (p : MvPolynomial σ ℚ) (k : ℕ) :
    p.IsWeightedHomogeneous (fun _=>(1:ℤ)) (k:ℤ) ↔
      p.IsWeightedHomogeneous (fun _=>(1:ℕ)) k := by
  simp only [IsWeightedHomogeneous,intWeight_eq_natWeight,Nat.cast_inj]

omit [DecidableEq I] in
lemma componentS_range_finite (d : I → ℕ) (k : ℤ) :
    Module.Finite ℚ (LinearMap.range (componentS d k)) := by
  classical
  by_cases hk : k<0
  · have hr : LinearMap.range (componentS d k)=⊥ := by
      apply bot_unique
      rintro x ⟨f,rfl⟩
      exact Subtype.ext (homogeneous_negative_eq_zero _ (componentS_homogeneous d k f) hk)
    rw [hr]
    infer_instance
  · have hk0 : 0≤k := le_of_not_gt hk
    let H := weightedHomogeneousSubmodule ℚ (fun _ : Σ i,Fin (d i)=>(1:ℕ)) k.toNat
    let : Module.Finite ℚ H := Module.Finite.of_fg
      (weightedHomogeneousSubmodule_fg ℚ _ (fun _=>one_ne_zero) _)
    let L : LinearMap.range (componentS d k) →ₗ[ℚ] H :=
      (((symmetricSpace d).val.toLinearMap).comp (LinearMap.range (componentS d k)).subtype).codRestrict H (by
        rintro ⟨f,⟨g,rfl⟩⟩
        apply (homogeneous_int_nat _ _).mp
        rw [Int.toNat_of_nonneg hk0]
        exact componentS_homogeneous d k g)
    have hL : Function.Injective L := by
      intro x y h
      have hv : x.val.val=y.val.val := congrArg (fun z : H=>z.val) h
      exact Subtype.ext (Subtype.ext hv)
    exact Module.Finite.of_injective L hL

theorem gradeB_finite (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (k : ℤ) :
    Module.Finite ℚ (gradeB a μ d k) := by
  classical
  let := componentS_range_finite d k
  let Q := destabilizingSpace a μ d
  let L : LinearMap.range (componentS d k) →ₗ[ℚ] gradeB a μ d k :=
    (Q.mkQ.comp (LinearMap.range (componentS d k)).subtype).codRestrict _ (by
      rintro ⟨f,⟨g,rfl⟩⟩
      exact ⟨Q.mkQ g,rfl⟩)
  apply Module.Finite.of_surjective L
  rintro ⟨f,hf⟩
  obtain ⟨x,rfl⟩ := hf
  obtain ⟨g,rfl⟩ := Q.mkQ_surjective x
  exact ⟨⟨componentS d k g,⟨g,rfl⟩⟩,rfl⟩

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNGeometry
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.restrictionB_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleB_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ)
noncomputable def slopeCross (d e : I → ℕ) : ℝ := mass η d*mass c e-mass c d*mass η e
@[simp] lemma slopeCross_zero_left (e : I → ℕ) : slopeCross c η 0 e=0 := by simp [slopeCross]
@[simp] lemma slopeCross_zero_right (d : I → ℕ) : slopeCross c η d 0=0 := by simp [slopeCross]
lemma slopeCross_add_left (d e b : I → ℕ) :
    slopeCross c η (d+e) b=slopeCross c η d b+slopeCross c η e b := by simp [slopeCross,mass_add] <;> ring
lemma slopeCross_add_right (d e b : I → ℕ) :
    slopeCross c η d (e+b)=slopeCross c η d e+slopeCross c η d b := by simp [slopeCross,mass_add] <;> ring
lemma slopeCross_eq (hc : ∀ i,0 < c i) (d e : I → ℕ) :
    slopeCross c η d e=(slope c η d-slope c η e)*(mass c d*mass c e) := by
  rw [slopeCross,mass_eq c η hc d,mass_eq c η hc e]
  ring
lemma slopeCross_pos_iff (hc : ∀ i,0 < c i) {d e : I → ℕ} (hd : d≠0) (he : e≠0) :
    0 < slopeCross c η d e ↔ slope c η e < slope c η d := by
  rw [slopeCross_eq c η hc,mul_pos_iff_of_pos_right (mul_pos (mass_pos c hc d hd) (mass_pos c hc e he)),sub_pos]
lemma slopeCross_nonpos_iff (hc : ∀ i,0 < c i) {d e : I → ℕ} (hd : d≠0) (he : e≠0) :
    slopeCross c η d e ≤ 0 ↔ slope c η d ≤ slope c η e := by
  rw [←not_lt, slopeCross_pos_iff c η hc hd he,not_lt]

noncomputable def polygonArea : List (I → ℕ) → ℝ
  | [] => 0
  | d::l => slopeCross c η d l.sum+polygonArea l
@[simp] lemma polygonArea_nil : polygonArea c η []=0 := rfl
@[simp] lemma polygonArea_cons (d : I → ℕ) (l : List (I → ℕ)) :
    polygonArea c η (d::l)=slopeCross c η d l.sum+polygonArea c η l := rfl
@[simp] lemma polygonArea_singleton (d : I → ℕ) : polygonArea c η [d]=0 := by simp
lemma slopeCross_list_sum (d : I → ℕ) (l : List (I → ℕ)) :
    slopeCross c η d l.sum=(l.map (slopeCross c η d)).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp [slopeCross_add_right,ih]
lemma polygonArea_append (l r : List (I → ℕ)) :
    polygonArea c η (l++r)=polygonArea c η l+polygonArea c η r+slopeCross c η l.sum r.sum := by
  induction l with
  | nil => simp
  | cons d l ih => simp [ih,slopeCross_add_right,slopeCross_add_left] <;> ring

lemma polygonArea_nonneg (hc : ∀ i,0 < c i) {l : List (I → ℕ)} (hl : HNOrdered c η l) :
    0 ≤ polygonArea c η l := by
  induction l with
  | nil => exact le_refl 0
  | cons d l ih =>
    have hpair := List.pairwise_cons.mp hl.2
    have htail : HNOrdered c η l := ⟨fun e he=>hl.1 e (List.mem_cons_of_mem _ he),hpair.2⟩
    rw [polygonArea_cons,slopeCross_list_sum]
    apply add_nonneg _ (ih htail)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact ((slopeCross_pos_iff c η hc (hl.1 d (by simp)) (htail.1 e he)).mpr (hpair.1 e he)).le

lemma polygonArea_pos (hc : ∀ i,0 < c i) {l : List (I → ℕ)} (hl : HNOrdered c η l)
    (hlen : 2 ≤ l.length) : 0 < polygonArea c η l := by
  cases l with
  | nil => simp at hlen
  | cons d l =>
    cases l with
    | nil => simp at hlen
    | cons e l =>
      have hp := List.pairwise_cons.mp hl.2
      have ht : HNOrdered c η (e::l) := ⟨fun x hx=>hl.1 x (List.mem_cons_of_mem _ hx),hp.2⟩
      have hrest : 0 ≤ slopeCross c η d l.sum := by
        rw [slopeCross_list_sum]
        apply List.sum_nonneg
        intro x hx
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
        exact ((slopeCross_pos_iff c η hc (hl.1 d (by simp))
          (hl.1 y (by simp [hy]))).mpr (hp.1 y (by simp [hy]))).le
      have hde : 0 < slopeCross c η d e :=
        (slopeCross_pos_iff c η hc (hl.1 d (by simp)) (hl.1 e (by simp))).mpr (hp.1 e (by simp))
      simpa only [polygonArea_cons,List.sum_cons,slopeCross_add_right] using
        add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hde hrest) (polygonArea_nonneg c η hc ht)

lemma polygonArea_replace (l r q : List (I → ℕ)) (d e : I → ℕ) (hq : q.sum=d+e) :
    polygonArea c η (l++q++r)-polygonArea c η (l++[d,e]++r)=
      polygonArea c η q-slopeCross c η d e := by
  simp only [polygonArea_append,List.sum_append,hq,List.sum_cons,List.sum_nil,add_zero,
    polygonArea_cons,polygonArea_nil,slopeCross_zero_right]
  ring

lemma reorder_progress (hc : ∀ i,0 < c i) (l r q : List (I → ℕ)) {d e : I → ℕ}
    (hd : d≠0) (he : e≠0) (hde : slope c η d ≤ slope c η e)
    (hq : q.sum=d+e) (ho : HNOrdered c η q) :
    polygonArea c η (l++[d,e]++r) < polygonArea c η (l++q++r) ∨
    (polygonArea c η (l++[d,e]++r)=polygonArea c η (l++q++r) ∧
      (l++q++r).length < (l++[d,e]++r).length) := by
  have hdiff := polygonArea_replace c η l r q d e hq
  have hq₀ := polygonArea_nonneg c η hc ho
  have hde₀ := (slopeCross_nonpos_iff c η hc hd he).mpr hde
  by_cases hlt : polygonArea c η (l++[d,e]++r) < polygonArea c η (l++q++r)
  · exact Or.inl hlt
  right
  have heq : polygonArea c η (l++[d,e]++r)=polygonArea c η (l++q++r) := by linarith
  have hlen : q.length < 2 := by
    by_contra hh
    have := polygonArea_pos c η hc ho (by omega)
    linarith
  exact ⟨heq,by simp only [List.length_append,List.length_cons,List.length_nil]; omega⟩

end ElementaryPositivity.SlopeArithmetic

end
section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

abbrev HNComposition (d : I → ℕ) := {l : List (I → ℕ) // l.sum=d ∧ ∀ e∈l,e≠0}

def hnSize (d : I → ℕ) := ∑ i,d i
lemma hnSize_add (d e : I → ℕ) : hnSize (d+e)=hnSize d+hnSize e := Finset.sum_add_distrib
@[simp] lemma hnSize_zero : hnSize (0 : I → ℕ)=0 := by simp [hnSize]
lemma hnSize_eq_zero (d : I → ℕ) : hnSize d=0 ↔ d=0 := by
  simp only [hnSize,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies]
  exact ⟨fun h=>funext h,fun h i=>congrFun h i⟩
lemma hnSize_list_sum (l : List (I → ℕ)) : hnSize l.sum=(l.map hnSize).sum := by
  induction l with
  | nil => simp
  | cons d l ih => simp [hnSize_add,ih]
lemma HNComposition.length_le (d : I → ℕ) (l : HNComposition d) : l.val.length ≤ hnSize d := by
  have h := List.length_le_sum_of_one_le (l.val.map hnSize) (by
    intro n hn
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
    have := (hnSize_eq_zero e).not.mpr (l.property.2 e he)
    omega)
  have h' : l.val.length ≤ (l.val.map hnSize).sum := by simpa only [List.length_map] using h
  exact h'.trans_eq ((hnSize_list_sum l.val).symm.trans (congrArg hnSize l.property.1))

instance instFiniteHNComposition (d : I → ℕ) : Finite (HNComposition d) := by
  classical
  let E := {e : I → ℕ // e ≤ d}
  let : Finite E := (Set.finite_Iic d).to_subtype
  have hs : {l : List (I → ℕ) | l.sum=d ∧ ∀ e∈l,e≠0}.Finite := by
    apply ((List.finite_length_le E (hnSize d)).image (List.map Subtype.val)).subset
    intro l hl
    let q : List E := l.attach.map (fun e=>⟨e.val,by
      have := List.le_sum_of_mem e.property
      simpa only [hl.1] using this⟩)
    refine ⟨q,?_,?_⟩
    · change q.length ≤ hnSize d
      simpa only [q,List.length_map,List.length_attach] using HNComposition.length_le d ⟨l,hl⟩
    · simp only [q,List.map_map]
      change l.attach.map (fun x=>x.val)=l
      simp
  exact hs.to_subtype

variable (c η : I → ℝ)

def HNBefore {d : I → ℕ} (l r : HNComposition d) : Prop :=
  polygonArea c η r.val < polygonArea c η l.val ∨
    (polygonArea c η r.val=polygonArea c η l.val ∧ l.val.length < r.val.length)

instance instIsStrictOrderHNCompositionHNBefore (d : I → ℕ) : IsStrictOrder (HNComposition d) (HNBefore c η) where
  irrefl l := by simp [HNBefore]
  trans l r s hl hr := by
    rcases hl with hl|⟨hl,hl'⟩ <;> rcases hr with hr|⟨hr,hr'⟩
    · exact Or.inl (lt_trans hr hl)
    · exact Or.inl (hr ▸ hl)
    · exact Or.inl (hl ▸ hr)
    · exact Or.inr ⟨hr.trans hl,lt_trans hl' hr'⟩

lemma hnBefore_wellFounded (d : I → ℕ) : WellFounded (HNBefore c η (d:=d)) :=
  Set.wellFoundedOn_univ.mp Set.finite_univ.wellFoundedOn

lemma not_hnOrdered_adjacent {l : List (I → ℕ)} (hn : ∀ d∈l,d≠0) (ho : ¬HNOrdered c η l) :
    ∃ p q d e,l=p++[d,e]++q ∧ slope c η d ≤ slope c η e := by
  have h : ¬l.IsChain (fun d e=>slope c η e < slope c η d) := by
    intro h
    exact ho ⟨hn,List.isChain_iff_pairwise.mp h⟩
  clear hn ho
  induction l with
  | nil => exact (h (by simp)).elim
  | cons d l ih =>
    cases l with
    | nil => exact (h (by simp)).elim
    | cons e l =>
      by_cases hde : slope c η e < slope c η d
      · obtain ⟨p,q,u,v,heq,huv⟩:=ih (by
          intro hh
          exact h (List.isChain_cons_cons.mpr ⟨hde,hh⟩))
        exact ⟨d::p,q,u,v,by simp only [List.cons_append,←heq],huv⟩
      · exact ⟨[],l,d,e,rfl,le_of_not_gt hde⟩

lemma hnSize_pair_lt (hc : ∀ i,0 < c i) {p q : List (I → ℕ)} {d e : I → ℕ}
    (hn : ∀ b∈p++[d,e]++q,b≠0) (hde : slope c η d ≤ slope c η e)
    (ha : 0<polygonArea c η (p++[d,e]++q)) :
    hnSize (d+e)<hnSize (p++[d,e]++q).sum := by
  have hd : d≠0 := hn d (by simp)
  have he : e≠0 := hn e (by simp)
  have hpq : p≠[] ∨ q≠[] := by
    by_contra h
    push Not at h
    rcases h with ⟨rfl,rfl⟩
    simp only [List.nil_append,List.append_nil,polygonArea_cons,List.sum_cons,List.sum_nil,
      add_zero,polygonArea_nil,slopeCross_zero_right] at ha
    exact (not_lt_of_ge ((slopeCross_nonpos_iff c η hc hd he).mpr hde)) (by simpa using ha)
  have hsz : 0<hnSize p.sum+hnSize q.sum := by
    rcases hpq with hp|hq
    · obtain ⟨b,l,rfl⟩:=List.exists_cons_of_ne_nil hp
      have hb := (hnSize_eq_zero b).not.mpr (hn b (by simp))
      simp only [List.sum_cons,hnSize_add]
      omega
    · obtain ⟨b,l,rfl⟩:=List.exists_cons_of_ne_nil hq
      have hb := (hnSize_eq_zero b).not.mpr (hn b (by simp))
      simp only [List.sum_cons,hnSize_add]
      omega
  simp only [List.sum_append,List.sum_cons,List.sum_nil,add_zero,hnSize_add]
  omega

lemma slopeCross_of_destabilizing (hc : ∀ i,0 < c i) {d e : I → ℕ} (hd : d≠0)
    (h : slope c η (d+e) < slope c η d) : 0 < slopeCross c η d e := by
  have hm := mass_pos c hc d hd
  have hm' := mass_pos c hc (d+e) (add_ne_zero_left d e hd)
  have h' := (div_lt_div_iff₀ hm' hm).mp h
  rw [mass_add,mass_add] at h'
  unfold slopeCross
  nlinarith

end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNSpanning
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.restrictionB_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleB_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable {A : Type*} [Ring A] [Algebra ℚ A]
variable (c η : I → ℝ) (V : (I → ℕ) → Submodule ℚ A)
omit [Fintype I] in
@[simp] lemma hnWordSpace_singleton (d : I → ℕ) : hnWordSpace V [d]=V d := by simp
omit [Fintype I] in
lemma hnWordSpace_append (l r : List (I → ℕ)) :
    hnWordSpace V (l++r)=hnWordSpace V l*hnWordSpace V r := by simp [hnWordSpace,List.prod_append]

noncomputable def hnOrderedSpan (d : I → ℕ) : Submodule ℚ A :=
  ⨆ (l : List (I → ℕ)) (_ : l.sum=d) (_ : HNOrdered c η l),hnWordSpace V l
lemma hnWordSpace_le {d : I → ℕ} (l : List (I → ℕ)) (hs : l.sum=d) (ho : HNOrdered c η l) :
    hnWordSpace V l  ≤  hnOrderedSpan c η V d :=
  le_iSup_of_le l (le_iSup_of_le hs (le_iSup_of_le ho le_rfl))

variable (hc : ∀ i,0 < c i) (W : (I → ℕ) → Submodule ℚ A)
variable (hV : ∀ d,V d  ≤  W d)
variable (hW : ∀ d e,W d*W e  ≤  W (d+e))
variable (hzero : W 0  ≤  1)
variable (hdec : ∀ d,d≠0 → W d  ≤  V d ⊔
  ⨆ (u : I → ℕ) (v : I → ℕ) (_ : u+v=d) (_ : u≠0) (_ : v≠0)
    (_ : slope c η d < slope c η u),W u*W v)

include hc hV hW hzero hdec in

theorem hn_spanning (d : I → ℕ) : W d  ≤  hnOrderedSpan c η V d := by
  suffices ∀ n (d : I → ℕ),hnSize d=n → W d  ≤  hnOrderedSpan c η V d from this _ d rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d hdn
    have small : ∀ e,hnSize e < hnSize d → W e  ≤  hnOrderedSpan c η V e :=
      fun e he=>ih _ (by omega) e rfl
    have words : ∀ s : HNComposition d,0 < polygonArea c η s.val →
        hnWordSpace V s.val  ≤  hnOrderedSpan c η V d := by
      intro s
      induction s using (hnBefore_wellFounded c η d).induction with
      | h s ihs =>
        intro ha
        by_cases ho : HNOrdered c η s.val
        · exact hnWordSpace_le c η V s.val s.property.1 ho
        obtain ⟨p,q,u,v,hs,huv⟩:=not_hnOrdered_adjacent c η s.property.2 ho
        have hn : ∀ b∈p++[u,v]++q,b≠0 := by simpa only [←hs] using s.property.2
        have hsum : (p++[u,v]++q).sum=d := hs ▸ s.property.1
        have hp : 0 < polygonArea c η (p++[u,v]++q) := hs ▸ ha
        have hdim : hnSize (u+v) < hnSize d :=
          (hnSize_pair_lt c η hc hn huv hp).trans_eq (congrArg hnSize hsum)
        have hmerge : V u*V v  ≤  hnOrderedSpan c η V (u+v) :=
          (mul_le_mul' (hV u) (hV v)).trans ((hW u v).trans (small (u+v) hdim))
        calc
          hnWordSpace V s.val = hnWordSpace V p*(V u*V v)*hnWordSpace V q := by
            rw [hs]; simp only [hnWordSpace_append,hnWordSpace_cons,hnWordSpace_nil,mul_one]
          _  ≤  hnWordSpace V p*hnOrderedSpan c η V (u+v)*hnWordSpace V q := by
            exact mul_le_mul' (mul_le_mul' le_rfl hmerge) le_rfl
          _  ≤  hnOrderedSpan c η V d := by
            unfold hnOrderedSpan
            simp only [Submodule.mul_iSup,Submodule.iSup_mul]
            refine iSup_le fun r=>iSup_le fun hr=>iSup_le fun hor=>?_
            let t : HNComposition d := ⟨p++r++q,by
              constructor
              · simpa only [List.sum_append,hr,List.sum_cons,List.sum_nil,add_zero] using hsum
              · intro b hb
                rcases List.mem_append.mp hb with hb|hb
                · rcases List.mem_append.mp hb with hb|hb
                  · exact hn b (by simp [hb])
                  · exact hor.1 b hb
                · exact hn b (by simp [hb])⟩
            have ht : HNBefore c η t s := by
              have := reorder_progress c η hc p q r (hn u (by simp)) (hn v (by simp)) huv hr hor
              simpa only [HNBefore,t,hs] using this
            have hat : 0 < polygonArea c η t.val := by
              rcases ht with ht|⟨ht,_⟩
              · exact lt_trans ha ht
              · exact ha.trans_eq ht
            have h := ihs t ht hat
            simpa only [t,hnWordSpace_append,hnOrderedSpan] using h
    by_cases hd : d=0
    · subst d
      exact hzero.trans (hnWordSpace_le c η V [] rfl ⟨by simp,by simp⟩)
    apply (hdec d hd).trans
    apply sup_le
    · simpa only [hnWordSpace_singleton] using (hnWordSpace_le c η V (d:=d) [d] (by simp) ⟨by simpa using hd,by simp⟩)
    refine iSup_le fun u=>iSup_le fun v=>iSup_le fun huv=>iSup_le fun hu=>
      iSup_le fun hv=>iSup_le fun hμ=>?_
    have hsize : hnSize u+hnSize v=hnSize d := by rw [←hnSize_add,huv]
    have hu₀ : hnSize u≠0 := (hnSize_eq_zero u).not.mpr hu
    have hv₀ : hnSize v≠0 := (hnSize_eq_zero v).not.mpr hv
    apply (mul_le_mul' (small u (by omega)) (small v (by omega))).trans
    unfold hnOrderedSpan
    simp only [Submodule.mul_iSup,Submodule.iSup_mul]
    refine iSup_le fun r=>iSup_le fun hr=>iSup_le fun hor=>
      iSup_le fun l=>iSup_le fun hl=>iSup_le fun hol=>?_
    let s : HNComposition d := ⟨l++r,by
      constructor
      · simpa only [List.sum_append,hl,hr] using huv
      · intro b hb
        rcases List.mem_append.mp hb with hb|hb
        · exact hol.1 b hb
        · exact hor.1 b hb⟩
    have hp : 0 < polygonArea c η s.val := by
      change 0 < polygonArea c η (l++r)
      rw [polygonArea_append,hl,hr]
      exact add_pos_of_nonneg_of_pos (add_nonneg (polygonArea_nonneg c η hc hol)
        (polygonArea_nonneg c η hc hor))
        (slopeCross_of_destabilizing c η hc hu (by simpa only [huv] using hμ))
    simpa only [s,hnWordSpace_append,hnOrderedSpan] using words s hp

end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_RawGradedAlgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedOne _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

def rawComponent (_a : I → I → ℕ) (d : I → ℕ) := S d
noncomputable instance instAddCommGroupRawComponent (a : I → I → ℕ) (d : I → ℕ) : AddCommGroup (rawComponent a d) :=
  inferInstanceAs (AddCommGroup (S d))
noncomputable instance instModuleRatRawComponent (a : I → I → ℕ) (d : I → ℕ) : Module ℚ (rawComponent a d) :=
  inferInstanceAs (Module ℚ (S d))

noncomputable instance rawGradedMul (a : I → I → ℕ) : GradedMonoid.GMul (rawComponent a) where
  mul f g := shufflePolynomial a f g
noncomputable instance rawGradedOne (a : I → I → ℕ) : GradedMonoid.GOne (rawComponent a) where
  one := (1 : S (0 : I → ℕ))

omit [Fintype I] [DecidableEq I] in
lemma castS_heq {d e : I → ℕ} (h : d=e) (f : S d) : HEq (castS h f) f := by
  subst e
  rfl

lemma raw_one_mul (a : I → I → ℕ) (x : GradedMonoid (rawComponent a)) : 1*x=x := by
  apply Sigma.ext (zero_add _)
  exact (heq_of_eq (shufflePolynomial_unit_left a x.1 x.2)).trans (castS_heq _ _)
lemma raw_mul_one (a : I → I → ℕ) (x : GradedMonoid (rawComponent a)) : x*1=x := by
  apply Sigma.ext (add_zero _)
  exact (heq_of_eq (shufflePolynomial_unit_right a x.1 x.2)).trans (castS_heq _ _)
lemma raw_mul_assoc (a : I → I → ℕ) (x y z : GradedMonoid (rawComponent a)) : x*y*z=x*(y*z) := by
  apply Sigma.ext (add_assoc _ _ _)
  exact (castS_heq (add_assoc x.1 y.1 z.1) _).symm.trans (heq_of_eq (shufflePolynomial_assoc a x.2 y.2 z.2))
noncomputable instance rawGradedMonoid (a : I → I → ℕ) : GradedMonoid.GMonoid (rawComponent a) :=
  gradedMonoidOfLaws (raw_one_mul a) (raw_mul_one a) (raw_mul_assoc a)
noncomputable instance rawGradedRing (a : I → I → ℕ) : DirectSum.GRing (rawComponent a) :=
  gradedRingOfAddLaws (fun _=>shufflePolynomial_zero_right a _ _ _)
    (fun _=>shufflePolynomial_zero_left a _ _ _)
    (fun _ _ _=>shufflePolynomial_add_right a _ _ _)
    (fun _ _ _=>shufflePolynomial_add_left a _ _ _)
lemma raw_smul_mul (a : I → I → ℕ) (r : ℚ) (x y : GradedMonoid (rawComponent a)) :
    (r•x)*y=r•(x*y) := by
  apply Sigma.ext (show x.1+y.1=x.1+y.1 from rfl)
  exact heq_of_eq (shufflePolynomial_smul_left a r x.2 y.2)
lemma raw_mul_smul (a : I → I → ℕ) (r : ℚ) (x y : GradedMonoid (rawComponent a)) :
    x*(r•y)=r•(x*y) := by
  apply Sigma.ext (show x.1+y.1=x.1+y.1 from rfl)
  exact heq_of_eq (shufflePolynomial_smul_right a r x.2 y.2)
noncomputable instance rawGradedAlgebra (a : I → I → ℕ) : DirectSum.GAlgebra ℚ (rawComponent a) :=
  gradedAlgebraOfBilinear (raw_smul_mul a) (raw_mul_smul a)

abbrev RawAlgebra (a : I → I → ℕ) := ⨁ d : I → ℕ,rawComponent a d
noncomputable def rawLof (a : I → I → ℕ) (d : I → ℕ) : S d →ₗ[ℚ] RawAlgebra a :=
  DirectSum.lof ℚ _ (rawComponent a) d
lemma rawLof_mul (a : I → I → ℕ) (d e : I → ℕ) (x : S d) (y : S e) :
    rawLof a d x*rawLof a e y=rawLof a (d+e) (shufflePolynomial a x y) := by
  exact DirectSum.of_mul_of (A:=rawComponent a) x y
omit [DecidableEq I] in
lemma rawLof_cast (a : I → I → ℕ) {d e : I → ℕ} (h : d=e) (x : S d) :
    rawLof a e (castS h x)=rawLof a d x := by subst e; rfl

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)
noncomputable def rawDimensionSpace (d : I → ℕ) : Submodule ℚ (RawAlgebra a) :=
  LinearMap.range (rawLof a d)
noncomputable def rawSectionSpace
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) : Submodule ℚ (RawAlgebra a) :=
  LinearMap.range ((rawLof a d).comp (σ d))
lemma rawSectionSpace_le (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    rawSectionSpace a c η σ d ≤ rawDimensionSpace a d := by
  rintro _ ⟨x,rfl⟩
  exact ⟨σ d x,rfl⟩
lemma rawDimensionSpace_mul (d e : I → ℕ) :
    rawDimensionSpace a d*rawDimensionSpace a e ≤ rawDimensionSpace a (d+e) := by
  apply Submodule.mul_le.mpr
  rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
  exact ⟨shufflePolynomial a x y,(rawLof_mul a d e x y).symm⟩
lemma rawDimensionSpace_zero : rawDimensionSpace a 0 ≤ 1 := by
  rintro _ ⟨x,rfl⟩
  rw [S_zero_eq_scalar x,map_smul]
  change MvPolynomial.constantCoeff x.val • (1 : RawAlgebra a) ∈ (1 : Submodule ℚ _)
  exact Submodule.smul_mem _ _ (Submodule.one_le.mp le_rfl)

variable (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
variable (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ)
include hσ in
lemma rawDimensionSpace_decompose (d : I → ℕ) (_hd : d≠0) :
    rawDimensionSpace a d ≤ rawSectionSpace a c η σ d ⊔
      ⨆ (u : I → ℕ) (v : I → ℕ) (_ : u+v=d) (_ : u≠0) (_ : v≠0)
        (_ : slope c η d < slope c η u),rawDimensionSpace a u*rawDimensionSpace a v := by
  let Q := destabilizingSpace a (slope c η) d
  let U : Submodule ℚ (RawAlgebra a) :=
    ⨆ (u : I → ℕ) (v : I → ℕ) (_ : u+v=d) (_ : u≠0) (_ : v≠0)
      (_ : slope c η d < slope c η u),rawDimensionSpace a u*rawDimensionSpace a v
  have hQ : Q ≤ U.comap (rawLof a d) := by
    apply Submodule.span_le.mpr
    rintro f ⟨u,v,h,x,y,hu,hv,hμ,rfl⟩
    change rawLof a d (dimensionCast h (shufflePolynomial a x y)) ∈ U
    have hc : dimensionCast h (shufflePolynomial a x y)=castS h (shufflePolynomial a x y) := by
      subst d; rfl
    rw [hc,rawLof_cast,←rawLof_mul]
    have hi : rawDimensionSpace a u*rawDimensionSpace a v ≤ U :=
      le_iSup_of_le u (le_iSup_of_le v (le_iSup_of_le h
        (le_iSup_of_le hu (le_iSup_of_le hv (le_iSup_of_le hμ le_rfl)))))
    apply hi
    exact Submodule.mul_mem_mul (show rawLof a u x∈rawDimensionSpace a u from ⟨x,rfl⟩)
      (show rawLof a v y∈rawDimensionSpace a v from ⟨y,rfl⟩)
  rintro _ ⟨f,rfl⟩
  have hm : f-σ d (Q.mkQ f)∈Q := by
    apply (Submodule.Quotient.mk_eq_zero Q).mp
    change Q.mkQ (f-σ d (Q.mkQ f))=0
    rw [map_sub,hσ d,sub_self]
  have hleft : rawLof a d (σ d (Q.mkQ f))∈rawSectionSpace a c η σ d := ⟨Q.mkQ f,rfl⟩
  have hright : rawLof a d (f-σ d (Q.mkQ f))∈U := hQ hm
  have hh := Submodule.add_mem_sup hleft hright
  simpa only [map_sub,add_sub_cancel] using hh

include hσ in

theorem raw_hn_spanning (hc : ∀ i,0 < c i) (d : I → ℕ) :
    rawDimensionSpace a d ≤ hnOrderedSpan c η (rawSectionSpace a c η σ) d :=
  hn_spanning c η (rawSectionSpace a c η σ) hc (rawDimensionSpace a)
    (rawSectionSpace_le a c η σ) (rawDimensionSpace_mul a) (rawDimensionSpace_zero a)
    (rawDimensionSpace_decompose a c η σ hσ) d

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

noncomputable def hnWordMap (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) :
    (l : List (I → ℕ)) → HNTensor a c η l →ₗ[ℚ] RawAlgebra a
  | [] => rawLof a 0
  | d::l => (LinearMap.mul' ℚ (RawAlgebra a)).comp
      (TensorProduct.map ((rawLof a d).comp (σ d)) (hnWordMap σ l))

lemma range_tensor_mul {A M N : Type*} [Ring A] [Algebra ℚ A]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (f : M →ₗ[ℚ] A) (g : N →ₗ[ℚ] A) :
    LinearMap.range ((LinearMap.mul' ℚ A).comp (TensorProduct.map f g))=
      LinearMap.range f*LinearMap.range g := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
      exact Submodule.mul_mem_mul (show f x∈LinearMap.range f from ⟨x,rfl⟩)
        (show g y∈LinearMap.range g from ⟨y,rfl⟩)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · apply Submodule.mul_le.mpr
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    exact ⟨x⊗ₜ[ℚ]y,rfl⟩

lemma rawDimensionSpace_zero_eq : rawDimensionSpace a 0=1 := by
  apply le_antisymm (rawDimensionSpace_zero a)
  apply Submodule.one_le.mpr
  exact ⟨(1 : S (0 : I → ℕ)),rfl⟩
lemma hnWordMap_range (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (l : List (I → ℕ)) :
    LinearMap.range (hnWordMap a c η σ l)=hnWordSpace (rawSectionSpace a c η σ) l := by
  induction l with
  | nil => exact rawDimensionSpace_zero_eq a
  | cons d l ih =>
    change LinearMap.range ((LinearMap.mul' ℚ (RawAlgebra a)).comp
      (TensorProduct.map ((rawLof a d).comp (σ d)) (hnWordMap a c η σ l)))=
      rawSectionSpace a c η σ d*hnWordSpace (rawSectionSpace a c η σ) l
    rw [range_tensor_mul,ih]
    rfl
lemma hnWordSpace_raw_le (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (l : List (I → ℕ)) :
    hnWordSpace (rawSectionSpace a c η σ) l ≤ rawDimensionSpace a l.sum := by
  induction l with
  | nil => simp only [hnWordSpace_nil,List.sum_nil,rawDimensionSpace_zero_eq,le_refl]
  | cons d l ih => exact (mul_le_mul' (rawSectionSpace_le a c η σ d) ih).trans (rawDimensionSpace_mul a d l.sum)

noncomputable def hnExpansionRaw (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    (⨁ l : HNIndex c η d,HNTensor a c η l.val) →ₗ[ℚ] RawAlgebra a :=
  DirectSum.toModule ℚ _ _ (fun l=>hnWordMap a c η σ l.val)

lemma hnExpansionRaw_range (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    LinearMap.range (hnExpansionRaw a c η σ d)=hnOrderedSpan c η (rawSectionSpace a c η σ) d := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using DirectSum.induction_on with
    | zero => simpa only [map_zero] using Submodule.zero_mem (hnOrderedSpan c η (rawSectionSpace a c η σ) d)
    | of l x =>
      have hx : hnWordMap a c η σ l.val x∈hnWordSpace (rawSectionSpace a c η σ) l.val :=
        hnWordMap_range a c η σ l.val ▸ LinearMap.mem_range_self _ x
      change hnExpansionRaw a c η σ d (DirectSum.lof ℚ _ _ l x)∈_
      rw [hnExpansionRaw,DirectSum.toModule_lof]
      exact hnWordSpace_le c η (rawSectionSpace a c η σ) l.val l.property.1 l.property.2 hx
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · refine iSup_le fun l=>iSup_le fun hl=>iSup_le fun ho=>?_
    rw [←hnWordMap_range]
    rintro _ ⟨x,rfl⟩
    exact ⟨DirectSum.lof ℚ _ _ ⟨l,hl,ho⟩ x,DirectSum.toModule_lof ℚ _ _⟩

lemma hnExpansionRaw_mem (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ)
    (x : ⨁ l : HNIndex c η d,HNTensor a c η l.val) :
    hnExpansionRaw a c η σ d x∈rawDimensionSpace a d := by
  have h : hnOrderedSpan c η (rawSectionSpace a c η σ) d ≤ rawDimensionSpace a d := by
    refine iSup_le fun l=>iSup_le fun hl=>iSup_le fun _=>?_
    simpa only [hl] using hnWordSpace_raw_le a c η σ l
  exact h ((hnExpansionRaw_range a c η σ d) ▸ LinearMap.mem_range_self _ x)

noncomputable def hnExpansion (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    (⨁ l : HNIndex c η d,HNTensor a c η l.val) →ₗ[ℚ] rawDimensionSpace a d :=
  (hnExpansionRaw a c η σ d).codRestrict _ (hnExpansionRaw_mem a c η σ d)

theorem hnExpansion_surjective (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
    Function.Surjective (hnExpansion a c η σ d) := by
  intro x
  obtain ⟨y,hy⟩ : x.val∈LinearMap.range (hnExpansionRaw a c η σ d) := by
    rw [hnExpansionRaw_range]
    exact raw_hn_spanning a c η σ hσ hc d x.property
  exact ⟨y,Subtype.ext hy⟩
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNPolynomial
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

lemma hnPolynomial_cons (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (d : I → ℕ) (l : List (I → ℕ)) (x : B a (slope c η) d) (y : HNTensor a c η l) :
    hnPolynomial a c η σ (d::l) (x⊗ₜ[ℚ]y)=shufflePolynomial a (σ d x) (hnPolynomial a c η σ l y) := rfl
lemma hnWordMap_polynomial (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (l : List (I → ℕ)) :
    hnWordMap a c η σ l=(rawLof a l.sum).comp (hnPolynomial a c η σ l) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    apply TensorProduct.ext'
    intro x y
    change rawLof a d (σ d x)*hnWordMap a c η σ l y=rawLof a (d+l.sum) _
    rw [ih,LinearMap.comp_apply,rawLof_mul]
    rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNIndependent
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

lemma hnExpansionRaw_polynomial (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d) (d : I → ℕ) :
    hnExpansionRaw a c η σ d=(rawLof a d).comp (hnPolynomialExpansion a c η σ d) := by
  apply DirectSum.linearMap_ext
  intro l
  apply LinearMap.ext
  intro x
  simp only [hnExpansionRaw,hnPolynomialExpansion,LinearMap.comp_apply,DirectSum.toModule_lof]
  rw [hnWordMap_polynomial,LinearMap.comp_apply,dimensionCast_eq_castS,rawLof_cast]

lemma hnPolynomialExpansion_surjective (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
    Function.Surjective (hnPolynomialExpansion a c η σ d) := by
  intro x
  obtain ⟨y,hy⟩:=hnExpansion_surjective a c η hc σ hσ d ⟨rawLof a d x,⟨x,rfl⟩⟩
  have H : hnExpansionRaw a c η σ d y=rawLof a d x := congrArg Subtype.val hy
  rw [hnExpansionRaw_polynomial,LinearMap.comp_apply] at H
  exact ⟨y,DirectSum.of_injective d H⟩

noncomputable def hnOrderedEquiv (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
    (⨁ l : HNIndex c η d,HNTensor a c η l.val) ≃ₗ[ℚ] S d :=
  LinearEquiv.ofBijective (hnPolynomialExpansion a c η σ d)
    ⟨hnPolynomialExpansion_injective a c η hc σ hσ d,hnPolynomialExpansion_surjective a c η hc σ hσ d⟩
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)

noncomputable def degreeQuotient (k : ℤ) :
    LinearMap.range (componentS d k) →ₗ[ℚ] gradeB a μ d k :=
  ((destabilizingSpace a μ d).mkQ.comp (LinearMap.range (componentS d k)).subtype).codRestrict _ (by
    rintro ⟨f,⟨g,rfl⟩⟩
    exact ⟨(destabilizingSpace a μ d).mkQ g,rfl⟩)
lemma degreeQuotient_surjective (k : ℤ) : Function.Surjective (degreeQuotient a μ d k) := by
  rintro ⟨f,x,rfl⟩
  obtain ⟨g,rfl⟩:=(destabilizingSpace a μ d).mkQ_surjective x
  exact ⟨⟨componentS d k g,⟨g,rfl⟩⟩,rfl⟩

local instance degreeFree (k : ℤ) : Module.Free ℚ (gradeB a μ d k) :=
  Module.Free.of_divisionRing ℚ _
local instance degreeProjective (k : ℤ) : Module.Projective ℚ (gradeB a μ d k) :=
  Module.Projective.of_free

noncomputable def degreeSection (k : ℤ) :
    gradeB a μ d k →ₗ[ℚ] LinearMap.range (componentS d k) :=
  (LinearMap.exists_rightInverse_of_surjective (degreeQuotient a μ d k)
    (LinearMap.range_eq_top.mpr (degreeQuotient_surjective a μ d k))).choose
lemma degreeSection_rightInverse (k : ℤ) (x : gradeB a μ d k) :
    degreeQuotient a μ d k (degreeSection a μ d k x)=x :=
  LinearMap.congr_fun (LinearMap.exists_rightInverse_of_surjective (degreeQuotient a μ d k)
    (LinearMap.range_eq_top.mpr (degreeQuotient_surjective a μ d k))).choose_spec x

noncomputable def gradeBEquiv : (⨁ k : ℤ,gradeB a μ d k) ≃ₗ[ℚ] B a μ d :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (gradeB a μ d)) (gradeB_internal a μ d)
lemma gradeBEquiv_of (k : ℤ) (x : gradeB a μ d k) :
    gradeBEquiv a μ d (DirectSum.lof ℚ ℤ (fun k => ↥(gradeB a μ d k)) k x)=x.val :=
  DirectSum.coeLinearMap_of _ _ _
lemma gradeBEquiv_symm_homogeneous (k : ℤ) (x : gradeB a μ d k) :
    (gradeBEquiv a μ d).symm x.val=DirectSum.lof ℚ ℤ (fun k => ↥(gradeB a μ d k)) k x := by
  apply (gradeBEquiv a μ d).injective
  rw [LinearEquiv.apply_symm_apply,gradeBEquiv_of]

noncomputable def homogeneousSection : B a μ d →ₗ[ℚ] S d :=
  (DirectSum.toModule ℚ _ _ (fun k=>(LinearMap.range (componentS d k)).subtype.comp
    (degreeSection a μ d k))).comp (gradeBEquiv a μ d).symm.toLinearMap
lemma homogeneousSection_on_grade (k : ℤ) (x : gradeB a μ d k) :
    homogeneousSection a μ d x.val=(degreeSection a μ d k x).val := by
  unfold homogeneousSection
  rw [LinearMap.comp_apply,LinearEquiv.coe_coe,gradeBEquiv_symm_homogeneous,DirectSum.toModule_lof]
  rfl
lemma homogeneousSection_rightInverse :
    Function.RightInverse (homogeneousSection a μ d) (destabilizingSpace a μ d).mkQ := by
  have H : (destabilizingSpace a μ d).mkQ.comp
      (DirectSum.toModule ℚ ℤ (S d) (fun k=>(LinearMap.range (componentS d k)).subtype.comp
        (degreeSection a μ d k)))=(gradeBEquiv a μ d).toLinearMap := by
    apply DirectSum.linearMap_ext
    intro k
    apply LinearMap.ext
    intro x
    change (destabilizingSpace a μ d).mkQ
      ((DirectSum.toModule ℚ ℤ (S d) (fun k=>(LinearMap.range (componentS d k)).subtype.comp
        (degreeSection a μ d k))) (DirectSum.lof ℚ ℤ (fun k => ↥(gradeB a μ d k)) k x))=_
    rw [DirectSum.toModule_lof]
    exact (congrArg Subtype.val (degreeSection_rightInverse a μ d k x)).trans (gradeBEquiv_of a μ d k x).symm
  intro x
  exact (LinearMap.congr_fun H ((gradeBEquiv a μ d).symm x)).trans (LinearEquiv.apply_symm_apply _ x)
lemma homogeneousSection_graded (k : ℤ) (x : B a μ d) (hx : x∈gradeB a μ d k) :
    (homogeneousSection a μ d x).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k := by
  rw [homogeneousSection_on_grade a μ d k ⟨x,hx⟩]
  obtain ⟨g,hg⟩:=(degreeSection a μ d k ⟨x,hx⟩).property
  rw [←hg]
  exact componentS_homogeneous d k g
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNHomogeneousBasis
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceZeroUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
lemma dfinsupp_basis_apply {J : Type*} [DecidableEq J] {M : J → Type*} [∀ j,AddCommGroup (M j)]
    [∀ j,Module ℚ (M j)] {K : J → Type*} (b : ∀ j,Module.Basis (K j) ℚ (M j))
    (j : J) (k : K j) : DFinsupp.basis b ⟨j,k⟩=DFinsupp.single j (b j k) := by
  classical
  apply Module.Basis.apply_eq_iff.mpr
  ext ⟨i,l⟩
  by_cases h : i=j
  · subst i
    simp [DFinsupp.basis,Finsupp.single_apply]
  · simp [DFinsupp.basis,h,Ne.symm h]

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

local instance gradeBFinite (d : I → ℕ) (k : ℤ) : Module.Finite ℚ (gradeB a (slope c η) d k) :=
  gradeB_finite a (slope c η) d k

local instance gradeBFree (d : I → ℕ) (k : ℤ) : Module.Free ℚ (gradeB a (slope c η) d k) :=
  Module.Free.of_divisionRing ℚ _

abbrev HomogeneousBIndex (d : I → ℕ) := Σ k : ℤ,Fin (Module.finrank ℚ (gradeB a (slope c η) d k))
noncomputable def homogeneousBBasis (d : I → ℕ) : Module.Basis (HomogeneousBIndex a c η d) ℚ (B a (slope c η) d) :=
  (gradeB_internal a (slope c η) d).collectedBasis (fun k=>Module.finBasis ℚ (gradeB a (slope c η) d k))
lemma homogeneousBBasis_mem (d : I → ℕ) (i : HomogeneousBIndex a c η d) :
    homogeneousBBasis a c η d i∈gradeB a (slope c η) d i.1 :=
  (gradeB_internal a (slope c η) d).collectedBasis_mem _ i

def HNBasisIndex : List (I → ℕ) → Type
  | [] => Unit
  | d::l => HomogeneousBIndex a c η d × HNBasisIndex l
noncomputable def hnTensorBasis : (l : List (I → ℕ)) → Module.Basis (HNBasisIndex a c η l) ℚ (HNTensor a c η l)
  | [] => (Module.Basis.singleton Unit ℚ).map (zeroPolynomialEquiv (I:=I)).symm
  | d::l => (homogeneousBBasis a c η d).tensorProduct (hnTensorBasis l)

def hnBasisDegree : (l : List (I → ℕ)) → HNBasisIndex a c η l → ℤ
  | [],_ => 0
  | d::l,i => i.1.1+hnBasisDegree l i.2-eulerForm a d l.sum

lemma hnTensorBasis_nil (i : Unit) : hnTensorBasis a c η [] i=(1 : S (0 : I → ℕ)) := by
  change ((Module.Basis.singleton Unit ℚ).map (zeroPolynomialEquiv (I:=I)).symm) i=_
  rw [Module.Basis.map_apply,Module.Basis.singleton_apply]
  exact one_smul ℚ (1 : S (0 : I → ℕ))
lemma hnTensorBasis_cons (d : I → ℕ) (l : List (I → ℕ))
    (i : HomogeneousBIndex a c η d) (j : HNBasisIndex a c η l) :
    hnTensorBasis a c η (d::l) (i,j)=homogeneousBBasis a c η d i⊗ₜ[ℚ]hnTensorBasis a c η l j :=
  Module.Basis.tensorProduct_apply _ _ i j

lemma hnTensorBasis_polynomial (l : List (I → ℕ)) (i : HNBasisIndex a c η l) :
    (hnPolynomial a c η (homogeneousSection a (slope c η)) l (hnTensorBasis a c η l i)).val.IsWeightedHomogeneous
      (fun _=>(1:ℤ)) (hnBasisDegree a c η l i) := by
  induction l with
  | nil =>
    have H := hnTensorBasis_nil a c η i
    exact (congrArg (fun f : S (0 : I → ℕ)=>f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) 0) H).mpr
      (MvPolynomial.isWeightedHomogeneous_one ℚ (fun _=>(1:ℤ)))
  | cons d l ih =>
    rcases i with ⟨i,j⟩
    have H := congrArg (hnPolynomial a c η (homogeneousSection a (slope c η)) (d::l))
      (hnTensorBasis_cons a c η d l i j)
    have H' := H.trans (hnPolynomial_cons a c η (homogeneousSection a (slope c η)) d l _ _)
    exact (congrArg (fun f : S (d+l.sum)=>f.val.IsWeightedHomogeneous (fun _=>(1:ℤ))
      (i.1+hnBasisDegree a c η l j-eulerForm a d l.sum)) H').mpr
      (shufflePolynomial_homogeneous a _ _
      (homogeneousSection_graded a (slope c η) d i.1 _ (homogeneousBBasis_mem a c η d i)) (ih j))

noncomputable def hnHomogeneousBasis (hc : ∀ i,0 < c i) (d : I → ℕ) :
    Module.Basis (Σ l : HNIndex c η d,HNBasisIndex a c η l.val) ℚ (S d) :=
  (DFinsupp.basis (fun l : HNIndex c η d=>hnTensorBasis a c η l.val)).map
    (hnOrderedEquiv a c η hc (homogeneousSection a (slope c η))
      (homogeneousSection_rightInverse a (slope c η)) d)

lemma hnHomogeneousBasis_apply (hc : ∀ i,0 < c i) (d : I → ℕ)
    (i : Σ l : HNIndex c η d,HNBasisIndex a c η l.val) :
    hnHomogeneousBasis a c η hc d i=dimensionCast i.1.property.1
      (hnPolynomial a c η (homogeneousSection a (slope c η)) i.1.val (hnTensorBasis a c η i.1.val i.2)) := by
  rcases i with ⟨l,i⟩
  simp only [hnHomogeneousBasis,Module.Basis.map_apply,dfinsupp_basis_apply]
  simp only [hnOrderedEquiv,LinearEquiv.ofBijective_apply,hnPolynomialExpansion,DirectSum.toModule]
  exact DFinsupp.sumAddHom_single _ _ _

lemma hnHomogeneousBasis_degree (hc : ∀ i,0 < c i) (d : I → ℕ)
    (i : Σ l : HNIndex c η d,HNBasisIndex a c η l.val) :
    (hnHomogeneousBasis a c η hc d i).val.IsWeightedHomogeneous (fun _=>(1:ℤ))
      (hnBasisDegree a c η i.1.val i.2) := by
  rw [hnHomogeneousBasis_apply]
  have H := hnTensorBasis_polynomial a c η i.1.val i.2
  generalize hp : hnPolynomial a c η (homogeneousSection a (slope c η)) i.1.val
    (hnTensorBasis a c η i.1.val i.2)=x at H ⊢
  rcases i with ⟨⟨l,hl,ho⟩,i⟩
  dsimp only at *
  subst d
  exact H
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNHilbert
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)

abbrev HNGradedIndex (d : I → ℕ) (k : ℤ) :=
  {i : Σ l : HNIndex c η d,HNBasisIndex a c η l.val // hnBasisDegree a c η i.1.val i.2=k}

lemma hnHomogeneousBasis_component (d : I → ℕ) (k : ℤ)
    (i : Σ l : HNIndex c η d,HNBasisIndex a c η l.val) :
    componentS d k (hnHomogeneousBasis a c η hc d i)=
      if hnBasisDegree a c η i.1.val i.2=k then hnHomogeneousBasis a c η hc d i else 0 := by
  rw [componentS_of_homogeneous _ _ (hnHomogeneousBasis_degree a c η hc d i)]
  simp only [eq_comm]

noncomputable def hnGradedBasis (d : I → ℕ) (k : ℤ) :
    Module.Basis (HNGradedIndex a c η d k) ℚ (LinearMap.range (componentS d k)) :=
  ElementaryPositivity.homogeneousBasisFibre (hnHomogeneousBasis a c η hc d)
    (fun i=>hnBasisDegree a c η i.1.val i.2) (componentS d)
    (hnHomogeneousBasis_component a c η hc d) k

include hc

theorem hnGradedIndex_finite (d : I → ℕ) (k : ℤ) : Finite (HNGradedIndex a c η d k) := by
  let := componentS_range_finite d k
  exact Module.Finite.finite_basis (hnGradedBasis a c η hc d k)

theorem hnHilbert_coefficient (d : I → ℕ) (k : ℤ) :
    Module.finrank ℚ (LinearMap.range (componentS d k))=Nat.card (HNGradedIndex a c η d k) := by
  let := hnGradedIndex_finite a c η hc d k
  let := Fintype.ofFinite (HNGradedIndex a c η d k)
  rw [Module.finrank_eq_card_basis (hnGradedBasis a c η hc d k),Nat.card_eq_fintype_card]
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PackExponentSorting
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.SlopeArithmetic.instFiniteHNComposition _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable

abbrev PackExponent (d : I → ℕ) := (Σ i,Fin (d i)) →₀ ℕ
abbrev SortedPackExponent (d : I → ℕ) := ∀ i,{f : Fin (d i) → ℕ // Monotone f}

def sortPackExponent (d : I → ℕ) (m : PackExponent d) : SortedPackExponent d :=
  fun i=>⟨(fun j=>m ⟨i,j⟩) ∘ Tuple.sort (fun j=>m ⟨i,j⟩),Tuple.monotone_sort _⟩

noncomputable def sortedPackRepresentative (d : I → ℕ) (k : SortedPackExponent d) : PackExponent d :=
  Finsupp.equivFunOnFinite.symm (fun ij=> (k ij.1).val ij.2)

lemma sortPack_representative (d : I → ℕ) (k : SortedPackExponent d) :
    sortPackExponent d (sortedPackRepresentative d k)=k := by
  funext i
  apply Subtype.ext
  exact Tuple.unique_monotone (Tuple.monotone_sort (k i).val) (show Monotone ((k i).val ∘ Equiv.refl _) from (k i).property)

lemma tuple_sorted_comp_perm {n : ℕ} (f : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    (f ∘ σ) ∘ Tuple.sort (f ∘ σ)=f ∘ Tuple.sort f := by
  exact Tuple.unique_monotone (σ:= (Tuple.sort (f ∘ σ)).trans σ)
    (Tuple.monotone_sort (f ∘ σ)) (Tuple.monotone_sort f)

omit [Fintype I] in
lemma packExponent_permute_apply (d : I → ℕ) (g : ∀ i,Equiv.Perm (Fin (d i)))
    (m : PackExponent d) (i : I) (j : Fin (d i)) :
    m.mapDomain (packAction (fun i=>Fin (d i)) g) ⟨i,j⟩=m ⟨i,(g i).symm j⟩ := by
  rw [Finsupp.mapDomain_equiv_apply]
  rfl

omit [Fintype I] in
lemma sortPack_permute (d : I → ℕ) (g : ∀ i,Equiv.Perm (Fin (d i))) (m : PackExponent d) :
    sortPackExponent d (m.mapDomain (packAction (fun i=>Fin (d i)) g))=sortPackExponent d m := by
  funext i
  apply Subtype.ext
  change ((fun j=>m.mapDomain (packAction (fun i=>Fin (d i)) g) ⟨i,j⟩) ∘ Tuple.sort _) = _
  simp only [packExponent_permute_apply]
  exact tuple_sorted_comp_perm (fun j=>m ⟨i,j⟩) (g i).symm

lemma packExponent_of_sorted (d : I → ℕ) (m : PackExponent d) :
    (sortedPackRepresentative d (sortPackExponent d m)).mapDomain
      (packAction (fun i=>Fin (d i)) (fun i=>Tuple.sort (fun j=>m ⟨i,j⟩)))=m := by
  ext ⟨i,j⟩
  rw [packExponent_permute_apply]
  change m ⟨i,Tuple.sort (fun j=>m ⟨i,j⟩) ((Tuple.sort (fun j=>m ⟨i,j⟩)).symm j)⟩=_
  rw [Equiv.apply_symm_apply]

lemma sortPack_fibre_finite (d : I → ℕ) (k : SortedPackExponent d) :
    Set.Finite {m : PackExponent d | sortPackExponent d m=k} := by
  apply (Set.finite_range (fun g : ∀ i,Equiv.Perm (Fin (d i))=>
    (sortedPackRepresentative d k).mapDomain (packAction (fun i=>Fin (d i)) g))).subset
  intro m hm
  refine ⟨fun i=>Tuple.sort (fun j=>m ⟨i,j⟩),?_⟩
  rw [←hm]
  exact packExponent_of_sorted d m

omit [Fintype I] in
lemma packExponent_permute_inverse (d : I → ℕ) (g : ∀ i,Equiv.Perm (Fin (d i))) (m : PackExponent d) :
    (m.mapDomain (packAction (fun i=>Fin (d i)) (fun i=>(g i).symm))).mapDomain
      (packAction (fun i=>Fin (d i)) g)=m := by
  ext ⟨i,j⟩
  simp only [packExponent_permute_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteFibreFinsupp
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open Function
attribute [local instance] Classical.propDecidable
variable {A B : Type*} (p : A → B)

def fibreConstant : Submodule ℚ (A →₀ ℚ) where
  carrier := {f | ∀ a a',p a=p a' → f a=f a'}
  zero_mem' := by intro a a' h; rfl
  add_mem' := by intro f g hf hg a a' h; simp only [Finsupp.add_apply,hf a a' h,hg a a' h]
  smul_mem' := by intro r f hf a a' h; simp only [Finsupp.smul_apply,hf a a' h]

noncomputable def finiteFibrePullback (hp : ∀ b,Set.Finite {a | p a=b}) :
    (B →₀ ℚ) →ₗ[ℚ] (A →₀ ℚ) where
  toFun f := Finsupp.ofSupportFinite (fun a=>f (p a)) (by
    have H:=(f.support.finite_toSet.biUnion (fun b (_ : b∈f.support)=>hp b))
    apply H.subset
    intro a ha
    exact Set.mem_iUnion₂.mpr ⟨p a,Finsupp.mem_support_iff.mpr ha,rfl⟩)
  map_add' f g := by ext a; rfl
  map_smul' r f := by ext a; rfl

@[simp] lemma finiteFibrePullback_apply (hp : ∀ b,Set.Finite {a | p a=b})
    (f : B →₀ ℚ) (a : A) : finiteFibrePullback p hp f a=f (p a) := rfl

noncomputable def fibreConstantEquiv (hp : ∀ b,Set.Finite {a | p a=b})
    (s : B → A) (hs : Function.RightInverse s p) :
    fibreConstant p ≃ₗ[ℚ] (B →₀ ℚ) where
  toFun f := Finsupp.lcomapDomain s hs.injective f.val
  invFun f := ⟨finiteFibrePullback p hp f,by intro a a' h; simp only [finiteFibrePullback_apply,h]⟩
  left_inv f := by
    apply Subtype.ext
    ext a
    exact f.property _ _ (hs (p a))
  right_inv f := by ext b; exact congrArg f (hs b)
  map_add' f g := map_add (Finsupp.lcomapDomain s hs.injective) f.val g.val
  map_smul' r f := map_smul (Finsupp.lcomapDomain s hs.injective) r f.val

noncomputable def fibreConstantBasis (hp : ∀ b,Set.Finite {a | p a=b})
    (s : B → A) (hs : Function.RightInverse s p) :
    Module.Basis B ℚ (fibreConstant p) :=
  (Finsupp.basisSingleOne : Module.Basis B ℚ (B →₀ ℚ)).map (fibreConstantEquiv p hp s hs).symm

lemma fibreConstantBasis_apply (hp : ∀ b,Set.Finite {a | p a=b})
    (s : B → A) (hs : Function.RightInverse s p) (b : B) (a : A) :
    (fibreConstantBasis p hp s hs b).val a=if p a=b then 1 else 0 := by
  classical
  change Finsupp.single b (1:ℚ) (p a)=_
  simp [Finsupp.single_apply,eq_comm]
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PackOrbitBasis
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.degreeZeroB_mk _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.relativeCoeffB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.ShufflePolynomiality
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma packSymmetric_coeff_permute (d : I → ℕ) (f : S d)
    (g : ∀ i,Equiv.Perm (Fin (d i))) (m : PackExponent d) :
    f.val.coeff (m.mapDomain (packAction (fun i=>Fin (d i)) g))=f.val.coeff m := by
  have H:=coeff_rename_mapDomain _ (packAction (fun i=>Fin (d i)) g).injective f.val m
  rw [f.property g] at H
  exact H

omit [DecidableEq I] in
lemma packSymmetric_coeff_sorted (d : I → ℕ) (f : S d) (m : PackExponent d) :
    f.val.coeff m=f.val.coeff (sortedPackRepresentative d (sortPackExponent d m)) := by
  have h:=packSymmetric_coeff_permute d f (fun i=>Tuple.sort (fun j=>m ⟨i,j⟩))
    (sortedPackRepresentative d (sortPackExponent d m))
  rwa [packExponent_of_sorted] at h

omit [DecidableEq I] in
lemma packSymmetric_iff_fibre (d : I → ℕ) (f : MvPolynomial (Σ i,Fin (d i)) ℚ) :
    PackSymmetric d f ↔ AddMonoidAlgebra.coeff f∈fibreConstant (sortPackExponent d) := by
  constructor
  · intro hf m n h
    change f.coeff m=f.coeff n
    rw [packSymmetric_coeff_sorted d ⟨f,hf⟩ m,packSymmetric_coeff_sorted d ⟨f,hf⟩ n,h]
  · intro hf g
    ext m
    have H:=coeff_rename_mapDomain (packAction (fun i=>Fin (d i)) g)
      (packAction (fun i=>Fin (d i)) g).injective f
      (m.mapDomain (packAction (fun i=>Fin (d i)) (fun i=>(g i).symm)))
    rw [packExponent_permute_inverse] at H
    exact H.trans (hf _ _ (sortPack_permute d _ m))

noncomputable def packFibreEquiv (d : I → ℕ) :
    fibreConstant (sortPackExponent d) ≃ₗ[ℚ] S d where
  toFun f := ⟨AddMonoidAlgebra.ofCoeff f.val,(packSymmetric_iff_fibre d (AddMonoidAlgebra.ofCoeff f.val)).mpr f.property⟩
  invFun f := ⟨AddMonoidAlgebra.coeff f.val,(packSymmetric_iff_fibre d f.val).mp f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def packOrbitBasis (d : I → ℕ) : Module.Basis (SortedPackExponent d) ℚ (S d) :=
  (fibreConstantBasis (sortPackExponent d) (sortPack_fibre_finite d)
    (sortedPackRepresentative d) (sortPack_representative d)).map (packFibreEquiv d)

omit [DecidableEq I] in
lemma packOrbitBasis_coeff (d : I → ℕ) (k : SortedPackExponent d) (m : PackExponent d) :
    (packOrbitBasis d k).val.coeff m=if sortPackExponent d m=k then 1 else 0 := by
  have H:=fibreConstantBasis_apply (sortPackExponent d) (sortPack_fibre_finite d)
    (sortedPackRepresentative d) (sortPack_representative d) k m
  by_cases h : sortPackExponent d m=k
  · simp only [ite_eq_left h] at H ⊢; exact H
  · simp only [ite_eq_right h] at H ⊢; exact H

noncomputable def sortedPackDegree (d : I → ℕ) (k : SortedPackExponent d) : ℕ :=
  ∑ i,∑ j,(k i).val j

omit [DecidableEq I] in
lemma packExponent_degree_sort (d : I → ℕ) (m : PackExponent d) :
    sortedPackDegree d (sortPackExponent d m)=m.sum (fun _ n=>n) := by
  unfold sortedPackDegree sortPackExponent
  simp only [Function.comp_apply]
  calc
    _ = ∑ i,∑ j,m ⟨i,j⟩ := Finset.sum_congr rfl (fun i _=> Equiv.sum_comp (Tuple.sort (fun j=>m ⟨i,j⟩)) (fun j=>m ⟨i,j⟩))
    _ = ∑ ij,m ij := (Fintype.sum_sigma _).symm
    _ = _ := (m.sum_fintype (fun _ n=>n) (fun _=>rfl)).symm

omit [DecidableEq I] in
lemma packOrbitBasis_homogeneous (d : I → ℕ) (k : SortedPackExponent d) :
    (packOrbitBasis d k).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) (sortedPackDegree d k) := by
  intro m hm
  have h : sortPackExponent d m=k := by
    by_contra h
    rw [packOrbitBasis_coeff,ite_eq_right h] at hm
    exact hm rfl
  rw [←h,packExponent_degree_sort]
  simp [Finsupp.weight_apply,Finsupp.sum]

omit [DecidableEq I] in
lemma packOrbitBasis_component (d : I → ℕ) (ℓ : ℤ) (k : SortedPackExponent d) :
    componentS d ℓ (packOrbitBasis d k)=
      if (sortedPackDegree d k : ℤ)=ℓ then packOrbitBasis d k else 0 := by
  rw [componentS_of_homogeneous d _ (packOrbitBasis_homogeneous d k)]
  simp only [eq_comm]

omit [DecidableEq I] in
theorem packHilbert_coefficient (d : I → ℕ) (ℓ : ℤ) :
    Module.finrank ℚ (LinearMap.range (componentS d ℓ))=
      Nat.card {k : SortedPackExponent d // (sortedPackDegree d k : ℤ)=ℓ} := by
  let := componentS_range_finite d ℓ
  exact ElementaryPositivity.homogeneousBasis_finrank (packOrbitBasis d) _ _
    (packOrbitBasis_component d) ℓ
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiltrationHomogeneousRank
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]
variable (F G : Submodule ℚ M) (p : Module.End ℚ M)
variable (hp : ∀ x,p (p x)=p x)
variable (hF : ∀ x∈F,p x∈F) (hG : ∀ x∈G,p x∈G)

noncomputable def homogeneousMk : F.comap (LinearMap.range p).subtype →ₗ[ℚ] Grade F G :=
  (mk F G).comp
    ({ toFun := fun x=>⟨x.val.val,x.property⟩
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } : F.comap (LinearMap.range p).subtype →ₗ[ℚ] F)

include hp in
lemma homogeneousMk_range :
    LinearMap.range (homogeneousMk F G p)=LinearMap.range (map F G F G p hF hG) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    refine ⟨mk F G ⟨x.val.val,x.property⟩,?_⟩
    change Submodule.Quotient.mk (⟨p x.val.val,hF _ x.property⟩ : F)=Submodule.Quotient.mk (⟨x.val.val,x.property⟩ : F)
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    obtain ⟨y,hy⟩:=x.val.property
    exact (congrArg p hy).symm.trans ((hp y).trans hy)
  · rintro _ ⟨x,rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | H x => exact ⟨⟨⟨p x.val,⟨x.val,rfl⟩⟩,hF _ x.property⟩,rfl⟩

include hp in
lemma homogeneousMap_finite [Module.Finite ℚ (LinearMap.range p)] :
    Module.Finite ℚ (LinearMap.range (map F G F G p hF hG)) := by
  rw [←homogeneousMk_range F G p hp hF hG]
  exact Module.Finite.range (homogeneousMk F G p)

lemma homogeneousMk_ker :
    LinearMap.ker (homogeneousMk F G p)=
      next (F.comap (LinearMap.range p).subtype) (G.comap (LinearMap.range p).subtype) := by
  ext x
  change Submodule.Quotient.mk (⟨x.val.val,x.property⟩ : F)=0 ↔ _
  exact Submodule.Quotient.mk_eq_zero (next F G)

include hp hF hG in
lemma homogeneousGrade_rank [Module.Finite ℚ (LinearMap.range p)] (hGF : G≤F) :
    Module.finrank ℚ (LinearMap.range (map F G F G p hF hG))+
      Module.finrank ℚ (G.comap (LinearMap.range p).subtype)=
      Module.finrank ℚ (F.comap (LinearMap.range p).subtype) := by
  have H := (homogeneousMk F G p).finrank_range_add_finrank_ker
  rw [homogeneousMk_range F G p hp hF hG,homogeneousMk_ker] at H
  have E := (Submodule.comapSubtypeEquivOfLe
    (Submodule.comap_mono hGF : G.comap (LinearMap.range p).subtype≤F.comap (LinearMap.range p).subtype)).finrank_eq
  exact E ▸ H

include hp in
lemma homogeneousGrade_rank_eq [Module.Finite ℚ (LinearMap.range p)] (hGF : G≤F) :
    Module.finrank ℚ (LinearMap.range (map F G F G p hF hG))=
      Module.finrank ℚ (Grade (F.comap (LinearMap.range p).subtype)
        (G.comap (LinearMap.range p).subtype)) := by
  have H := homogeneousGrade_rank F G p hp hF hG hGF
  have H' := (next (F.comap (LinearMap.range p).subtype)
    (G.comap (LinearMap.range p).subtype)).finrank_quotient_add_finrank
  have E := (Submodule.comapSubtypeEquivOfLe
    (Submodule.comap_mono hGF : G.comap (LinearMap.range p).subtype≤F.comap (LinearMap.range p).subtype)).finrank_eq
  have H'' : Module.finrank ℚ (Grade (F.comap (LinearMap.range p).subtype)
      (G.comap (LinearMap.range p).subtype))+
      Module.finrank ℚ (G.comap (LinearMap.range p).subtype)=
      Module.finrank ℚ (F.comap (LinearMap.range p).subtype) := E ▸ H'
  omega
end ElementaryPositivity.LinearFiltration

namespace ElementaryPositivity
variable {M : Type*} [AddCommGroup M] [Module ℚ M] [Module.Finite ℚ M]
variable (F : ℤ → Submodule ℚ M) (hF : Antitone F)

include hF
lemma finiteFiltration_rank_step (w : ℤ) :
    Module.finrank ℚ (LinearFiltration.Grade (F w) (F (w+1)))+Module.finrank ℚ (F (w+1))=
      Module.finrank ℚ (F w) := by
  have H := (LinearFiltration.next (F w) (F (w+1))).finrank_quotient_add_finrank
  have E := (Submodule.comapSubtypeEquivOfLe (hF (show w≤w+1 by omega))).finrank_eq
  exact E ▸ H

lemma finiteFiltration_rank_sum (L : ℤ) (n : ℕ) :
    (∑ j∈Finset.range n,Module.finrank ℚ (LinearFiltration.Grade (F (L+j)) (F (L+j+1))))+
      Module.finrank ℚ (F (L+n))=Module.finrank ℚ (F L) := by
  induction n with
  | zero =>
    change 0+Module.finrank ℚ (F (L+0))=Module.finrank ℚ (F L)
    rw [add_zero,zero_add]
  | succ n ih =>
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one,←add_assoc,add_assoc]
    rw [finiteFiltration_rank_step F hF (L+n)]
    exact ih

lemma finiteFiltration_rank_total (L : ℤ) (n : ℕ) (hL : F L=⊤) (hU : F (L+n)=⊥) :
    (∑ j∈Finset.range n,Module.finrank ℚ (LinearFiltration.Grade (F (L+j)) (F (L+j+1))))=
      Module.finrank ℚ M := by
  have H := finiteFiltration_rank_sum F hF L n
  rw [hL,hU,finrank_bot,add_zero,finrank_top] at H
  exact H
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_OriginalDegree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)

noncomputable def originalFilteredPiece (d : I → ℕ) (k W : ℤ) :
    Submodule ℚ (gradeB a (slope c η) d k) :=
  (sourceFiltration a c η hc θ d W).comap (gradeB a (slope c η) d k).subtype

lemma originalFilteredPiece_antitone (d : I → ℕ) (k : ℤ) :
    Antitone (originalFilteredPiece a c η hc θ d k) := by
  intro U V h
  exact Submodule.comap_mono (sourceFiltration_antitone a c η hc θ d h)

lemma originalFilteredPiece_lower (d : I → ℕ) (k : ℤ) :
    originalFilteredPiece a c η hc θ d k (-interaction a d d)=⊤ := by
  unfold originalFilteredPiece
  rw [sourceFiltration_lower,Submodule.comap_top]

lemma originalFilteredPiece_upper (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (k W : ℤ) (hW : 2*k+eulerForm a d d<W) :
    originalFilteredPiece a c η hc θ d k W=⊥ := by
  apply bot_unique
  intro x hx
  apply Subtype.ext
  have H := sourceFiltration_upper a c η hc θ d hd hs k W hW
  have hx' : x.val∈gradeB a (slope c η) d k ⊓ sourceFiltration a c η hc θ d W := ⟨x.property,hx⟩
  rw [H] at hx'
  exact hx'

lemma associatedComponent_rank_eq (d : I → ℕ) (k W : ℤ) :
    Module.finrank ℚ (LinearMap.range (associatedComponent a c η hc θ d W k))=
      Module.finrank ℚ (LinearFiltration.Grade (originalFilteredPiece a c η hc θ d k W)
        (originalFilteredPiece a c η hc θ d k (W+1))) := by
  let : Module.Finite ℚ (LinearMap.range (componentB a (slope c η) d k)) := gradeB_finite a (slope c η) d k
  exact LinearFiltration.homogeneousGrade_rank_eq _ _ (componentB a (slope c η) d k)
    (componentB_idempotent a (slope c η) d k)
    (sourceFiltration_component_mem a c η hc θ d W k)
    (sourceFiltration_component_mem a c η hc θ d (W+1) k)
    (sourceFiltration_antitone a c η hc θ d (show W≤W+1 by omega))

theorem sourceHilbert_filtration (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (k : ℤ) (n : ℕ) (hn : 2*k+eulerForm a d d < -interaction a d d+n) :
    (∑ j∈Finset.range n, Module.finrank ℚ
      (LinearMap.range (associatedComponent a c η hc θ d (-interaction a d d+j) k)))=
    Module.finrank ℚ (gradeB a (slope c η) d k) := by
  let := gradeB_finite a (slope c η) d k
  conv_lhs =>
    arg 2
    ext j
    rw [associatedComponent_rank_eq]
  exact finiteFiltration_rank_total (originalFilteredPiece a c η hc θ d k)
    (originalFilteredPiece_antitone a c η hc θ d k) (-interaction a d d) n
    (originalFilteredPiece_lower a c η hc θ d k)
    (originalFilteredPiece_upper a c η hc θ d hd hs k _ hn)
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalOriginalDegree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

omit [DecidableEq I] in
lemma eulerForm_slopeDimensions_symm (d e : slopeDimensions c η hc θ) :
    eulerForm a d.val e.val=eulerForm a e.val d.val := by
  by_cases hd : d.val=0
  · rw [hd]; simp [eulerForm]
  by_cases he : e.val=0
  · rw [he]; simp [eulerForm]
  exact hχ.out _ _ hd he (d.property.resolve_left hd) (e.property.resolve_left he)

omit [DecidableEq I] in
lemma doubleShift_product (d e : slopeDimensions c η hc θ) (m n : ℤ) :
    2*(m+n-eulerForm a d.val e.val)+eulerForm a (d+e).val (d+e).val=
      (2*m+eulerForm a d.val d.val)+(2*n+eulerForm a e.val e.val) := by
  change 2*(m+n-eulerForm a d.val e.val)+eulerForm a (d.val+e.val) (d.val+e.val)=_
  rw [eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,eulerForm_slopeDimensions_symm a c η hc θ e d]
  ring

variable {J : Type*}

omit [DecidableEq I] in
lemma wordPolynomialDegree_shift (w : J → SlopeWeight c η hc θ) (p : J → ℤ) (l : List J) :
    2*wordPolynomialDegree a c η hc θ w p l+
      eulerForm a (wordWeight c η hc θ w l).1.val (wordWeight c η hc θ w l).1.val=
    (l.map (fun i=>2*p i+eulerForm a (w i).1.val (w i).1.val)).sum := by
  induction l with
  | nil => simp [wordPolynomialDegree,wordWeight,eulerForm]
  | cons i l ih =>
    change 2*(p i+wordPolynomialDegree a c η hc θ w p l-
      eulerForm a (w i).1.val (wordWeight c η hc θ w l).1.val)+
      eulerForm a ((w i).1+(wordWeight c η hc θ w l).1).val
        ((w i).1+(wordWeight c η hc θ w l).1).val=_
    rw [doubleShift_product,ih]
    rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalHilbertGrading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma unitalOriginalHomogeneous_range (d : I → ℕ) (W ℓ : ℤ) :
    unitalOriginalHomogeneous a c η hc θ d W ℓ=
      LinearMap.range (unitalAssociatedComponent a c η hc θ d W ℓ) := by
  ext x
  rw [mem_unitalOriginalHomogeneous]
  constructor
  · intro h; exact ⟨x,h⟩
  · rintro ⟨y,rfl⟩
    rw [unitalAssociatedComponent_twice,ite_eq_left rfl]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma unitalOriginalHomogeneous_finite (d : I → ℕ) (W ℓ : ℤ) :
    Module.Finite ℚ (unitalOriginalHomogeneous a c η hc θ d W ℓ) := by
  let : Module.Finite ℚ (LinearMap.range (componentB a (slope c η) d ℓ)) := gradeB_finite a (slope c η) d ℓ
  rw [unitalOriginalHomogeneous_range]
  exact LinearFiltration.homogeneousMap_finite _ _ (componentB a (slope c η) d ℓ)
    (componentB_idempotent a (slope c η) d ℓ)
    (unitalSourceFiltration_component_mem a c η hc θ d W ℓ)
    (unitalSourceFiltration_component_mem a c η hc θ d (W+1) ℓ)

lemma globalOriginalComponent_range (k : SlopeWeight c η hc θ) (ℓ : ℤ) :
    LinearMap.range (globalOriginalComponent a c η hc θ k ℓ)=globalOriginalHomogeneous a c η hc θ k ℓ := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    refine ⟨unitalAssociatedComponent a c η hc θ k.1.val k.2 ℓ
      (DirectSum.component ℚ _ (unitalComponent a c η hc θ) k x),?_,rfl⟩
    rw [unitalOriginalHomogeneous_range]
    exact ⟨_,rfl⟩
  · intro x hx
    exact ⟨x,(globalOriginalComponent_of_mem a c η hc θ hx ℓ).trans (ite_eq_left rfl)⟩

lemma globalOriginalComponent_finite (k : SlopeWeight c η hc θ) (ℓ : ℤ) :
    Module.Finite ℚ (LinearMap.range (globalOriginalComponent a c η hc θ k ℓ)) := by
  rw [globalOriginalComponent_range]
  let := unitalOriginalHomogeneous_finite a c η hc θ k.1.val k.2 ℓ
  exact Module.Finite.map _ _
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def stringPBWGradedBasis (k : SlopeWeight c η hc θ) (m : ℤ) :
    Module.Basis (StringPBWGradedIndex a c η hc θ k m) ℚ
      (LinearMap.range (globalOriginalComponent a c η hc θ k m)) :=
  ElementaryPositivity.homogeneousBasisFibre (globalStringPBWBasis a c η hc θ)
    (stringPBWGrade a c η hc θ) (fun k=>globalOriginalComponent a c η hc θ k.1 k.2)
    (stringPBWBasis_component a c η hc θ) (k,m)

lemma stringPBWGradedIndex_finite (k : SlopeWeight c η hc θ) (m : ℤ) :
    Finite (StringPBWGradedIndex a c η hc θ k m) := by
  let := globalOriginalComponent_finite a c η hc θ k m
  exact Module.Finite.finite_basis (stringPBWGradedBasis a c η hc θ k m)

lemma globalOriginalComponent_rank (k : SlopeWeight c η hc θ) (m : ℤ) :
    Module.finrank ℚ (LinearMap.range (globalOriginalComponent a c η hc θ k m))=
      Module.finrank ℚ (unitalOriginalHomogeneous a c η hc θ k.1.val k.2 m) := by
  rw [globalOriginalComponent_range]
  exact (Submodule.equivMapOfInjective (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k)
    (DirectSum.of_injective k) (unitalOriginalHomogeneous a c η hc θ k.1.val k.2 m)).finrank_eq.symm

theorem stringPBWHilbert_coefficient (k : SlopeWeight c η hc θ) (m : ℤ) :
    Module.finrank ℚ (unitalOriginalHomogeneous a c η hc θ k.1.val k.2 m)=
      Nat.card (StringPBWGradedIndex a c η hc θ k m) := by
  rw [←globalOriginalComponent_rank]
  let := stringPBWGradedIndex_finite a c η hc θ k m
  let := Fintype.ofFinite (StringPBWGradedIndex a c η hc θ k m)
  rw [Module.finrank_eq_card_basis (stringPBWGradedBasis a c η hc θ k m),Nat.card_eq_fintype_card]
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma unitalOriginalNonzero_rank (d : I → ℕ) (hd : d≠0) (W k : ℤ) :
    Module.finrank ℚ (unitalOriginalHomogeneous a c η hc θ d W k)=
      Module.finrank ℚ (LinearMap.range (associatedComponent a c η hc θ d W k)) := by
  rw [unitalOriginalHomogeneous_range]
  let e := unitalGradeNonzeroEquiv a c η hc θ d hd W
  have E : (LinearMap.range (unitalAssociatedComponent a c η hc θ d W k)).map e.toLinearMap=
      LinearMap.range (associatedComponent a c η hc θ d W k) := by
    apply le_antisymm
    · rintro _ ⟨_,⟨y,rfl⟩,rfl⟩
      exact ⟨e y,(unitalAssociatedComponent_nonzero a c η hc θ d hd W k y).symm⟩
    · rintro _ ⟨y,rfl⟩
      refine ⟨unitalAssociatedComponent a c η hc θ d W k (e.symm y),⟨e.symm y,rfl⟩,?_⟩
      exact (unitalAssociatedComponent_nonzero a c η hc θ d hd W k (e.symm y)).trans
        (congrArg (associatedComponent a c η hc θ d W k) (e.apply_symm_apply y))
  exact (e.finrank_map_eq _).symm.trans (congrArg (fun N : Submodule ℚ _=>Module.finrank ℚ N) E)

theorem sourcePBWHilbert_coefficient (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (k : ℤ) (n : ℕ) (hn : 2*k+eulerForm a d d < -interaction a d d+n) :
    Module.finrank ℚ (gradeB a (slope c η) d k)=
      ∑ j∈Finset.range n, Nat.card (StringPBWGradedIndex a c η hc θ
        (⟨d,Or.inr hs⟩,-interaction a d d+j) k) := by
  rw [←sourceHilbert_filtration a c η hc θ d hd hs k n hn]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←unitalOriginalNonzero_rank a c η hc θ d hd]
  exact stringPBWHilbert_coefficient a c η hc θ (⟨d,Or.inr hs⟩,-interaction a d d+j) k
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveStringBounds
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

def slopeStringCutoff (d : I → ℕ) (k : ℤ) : ℕ :=
  (2*k+eulerForm a d d+interaction a d d+1).toNat

omit [DecidableEq I] in
lemma slopeStringCutoff_bound (d : I → ℕ) (k : ℤ) :
    2*k+eulerForm a d d < -interaction a d d+slopeStringCutoff a d k := by
  unfold slopeStringCutoff
  omega

lemma sigmaSubtype_ext {A B : Type*} {p : A → B → Prop} {x y : Σ a,{b // p a b}}
    (h : x.1=y.1) (hval : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨a',b'⟩
  dsimp at h hval
  subst a'
  exact congrArg (Sigma.mk a) (Subtype.ext hval)

noncomputable def slopeStringCutoffEquiv (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) (k : ℤ) :
    SlopeStringCoefficient a c η hc θ d hs k ≃
      Σ j : Fin (slopeStringCutoff a d k),StringPBWGradedIndex a c η hc θ
        (⟨d,Or.inr hs⟩,-interaction a d d+j.val) k where
  toFun i := by
    have H:=slopeStringCoefficient_bounds a c η hc θ d hd hs k i
    have Hn:=slopeStringCutoff_bound a d k
    let j : Fin (slopeStringCutoff a d k):=⟨(i.1+interaction a d d).toNat,by omega⟩
    refine ⟨j,⟨i.2.val,?_⟩⟩
    have E : -interaction a d d+(j.val:ℤ)=i.1 := by dsimp [j]; omega
    rw [E]
    exact i.2.property
  invFun i := ⟨-interaction a d d+i.1.val,i.2⟩
  left_inv i := by
    apply sigmaSubtype_ext
    · dsimp; have H:=slopeStringCoefficient_bounds a c η hc θ d hd hs k i; omega
    · rfl
  right_inv i := by
    apply sigmaSubtype_ext
    · apply Fin.ext
      dsimp
      omega
    · rfl

lemma slopeStringCoefficient_finite (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) (k : ℤ) :
    Finite (SlopeStringCoefficient a c η hc θ d hs k) := by
  let (j : Fin (slopeStringCutoff a d k)) := stringPBWGradedIndex_finite a c η hc θ
    (⟨d,Or.inr hs⟩,-interaction a d d+j.val) k
  exact Finite.of_equiv _ (slopeStringCutoffEquiv a c η hc θ d hd hs k).symm

theorem slopeStringHilbert_coefficient (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) (k : ℤ) :
    Module.finrank ℚ (gradeB a (slope c η) d k)=
      Nat.card (SlopeStringCoefficient a c η hc θ d hs k) := by
  rw [Nat.card_congr (slopeStringCutoffEquiv a c η hc θ d hd hs k)]
  let (j : Fin (slopeStringCutoff a d k)) := stringPBWGradedIndex_finite a c η hc θ
    (⟨d,Or.inr hs⟩,-interaction a d d+j.val) k
  rw [Nat.card_sigma]
  exact (sourcePBWHilbert_coefficient a c η hc θ d hd hs k _ (slopeStringCutoff_bound a d k)).trans
    (Fin.sum_univ_eq_sum_range (fun j=>Nat.card (StringPBWGradedIndex a c η hc θ
      (⟨d,Or.inr hs⟩,-interaction a d d+j) k)) (slopeStringCutoff a d k)).symm
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteStringReordering
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
local instance slopeSymmetricFact (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

abbrev StringBlockIndex (d : I → ℕ) :=
  Σ k : ℤ,SlopeStringCoefficient a c η hc (slope c η d) d rfl k

noncomputable def homogeneousBStringEquiv (d : I → ℕ) (hd : d≠0) :
    HomogeneousBIndex a c η d ≃ StringBlockIndex a c η hc d :=
  Equiv.sigmaCongrRight (fun k=>by
    letI := slopeStringCoefficient_finite a c η hc (slope c η d) d hd rfl k
    exact (Finite.equivFinOfCardEq (slopeStringHilbert_coefficient a c η hc
      (slope c η d) d hd rfl k).symm).symm)

lemma homogeneousBStringEquiv_degree (d : I → ℕ) (hd : d≠0) (i : HomogeneousBIndex a c η d) :
    (homogeneousBStringEquiv a c η hc d hd i).1=i.1 := rfl

def HNStringIndex : List (I → ℕ) → Type u
  | [] => ULift.{u} Unit
  | d::l => StringBlockIndex a c η hc d × HNStringIndex l

def hnStringDegree : (l : List (I → ℕ)) → HNStringIndex a c η hc l → ℤ
  | [],_ => 0
  | d::l,i => i.1.1+hnStringDegree l i.2-eulerForm a d l.sum

noncomputable def hnStringEquiv : (l : List (I → ℕ)) → (∀ d∈l,d≠0) →
    HNBasisIndex a c η l ≃ HNStringIndex a c η hc l
  | [],_ => Equiv.ulift.symm
  | d::l,h => Equiv.prodCongr (homogeneousBStringEquiv a c η hc d (h d (by simp)))
      (hnStringEquiv l (fun e he=>h e (List.mem_cons_of_mem d he)))

lemma hnStringEquiv_degree (l : List (I → ℕ)) (h : ∀ d∈l,d≠0) (i : HNBasisIndex a c η l) :
    hnStringDegree a c η hc l (hnStringEquiv a c η hc l h i)=hnBasisDegree a c η l i := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rcases i with ⟨i,j⟩
    change (homogeneousBStringEquiv a c η hc d _ i).1 +
      hnStringDegree a c η hc l (hnStringEquiv a c η hc l _ j) - eulerForm a d l.sum = _
    rw [homogeneousBStringEquiv_degree, ih]
    rfl

abbrev HNStringCoefficient (d : I → ℕ) (k : ℤ) :=
  {i : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val //
    hnStringDegree a c η hc i.1.val i.2=k}

noncomputable def hnStringCoefficientEquiv (d : I → ℕ) (k : ℤ) :
    HNGradedIndex a c η d k ≃ HNStringCoefficient a c η hc d k :=
  (Equiv.sigmaCongrRight (fun l : HNIndex c η d=>
    hnStringEquiv a c η hc l.val l.property.2.1)).subtypeEquiv (by
      intro i
      exact (congrArg (·=k) (hnStringEquiv_degree a c η hc i.1.val i.1.property.2.1 i.2)).symm.to_iff)

lemma hnStringCoefficient_finite (d : I → ℕ) (k : ℤ) :
    Finite (HNStringCoefficient a c η hc d k) := by
  let := hnGradedIndex_finite a c η hc d k
  exact Finite.of_equiv _ (hnStringCoefficientEquiv a c η hc d k)

theorem finiteStringReordering_coefficient (d : I → ℕ) (k : ℤ) :
    Nat.card {i : SortedPackExponent d // (sortedPackDegree d i : ℤ)=k}=
      Nat.card (HNStringCoefficient a c η hc d k) := by
  rw [←packHilbert_coefficient,hnHilbert_coefficient a c η hc]
  exact Nat.card_congr (hnStringCoefficientEquiv a c η hc d k)
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity
variable {J : Type*} [LinearOrder J] (even : J → Prop)

def OrderedSignedWord := {l : List J // l.Pairwise (fun i j=>i≤j ∧ (i=j → even i))}
def SignedSelection := {m : Multiset J // ∀ i, ¬even i → m.count i≤1}

lemma count_le_one_of_signed_pairwise {l : List J}
    (h : l.Pairwise (fun i j=>i≤j ∧ (i=j → even i))) (i : J) (hi : ¬even i) :
    l.count i≤1 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    obtain ⟨hh,ht⟩:=List.pairwise_cons.mp h
    by_cases e : i=j
    · subst j
      have hn : i∉l := fun hm=>hi ((hh i hm).2 rfl)
      simp [List.count_eq_zero.mpr hn]
    · simpa [List.count_cons,Ne.symm e] using ih ht

lemma signed_pairwise_of_count {l : List J} (h : l.Pairwise (·≤·))
    (hc : ∀ i, ¬even i → l.count i≤1) :
    l.Pairwise (fun i j=>i≤j ∧ (i=j → even i)) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    obtain ⟨hh,ht⟩:=List.pairwise_cons.mp h
    apply List.pairwise_cons.mpr
    constructor
    · intro i hi
      refine ⟨hh i hi,?_⟩
      rintro rfl
      by_contra he
      have H:=hc j he
      have Hp:=List.count_pos_iff.mpr hi
      simp only [List.count_cons_self] at H
      omega
    · apply ih ht
      intro i hi
      have H:=hc i hi
      simp only [List.count_cons] at H
      split_ifs at H <;> omega

noncomputable def signedWordSelectionEquiv : OrderedSignedWord even ≃ SignedSelection even where
  toFun l := ⟨(l.val : Multiset J),by
    intro i hi
    simpa only [Multiset.coe_count] using count_le_one_of_signed_pairwise even l.property i hi⟩
  invFun m := ⟨m.val.sort (·≤·),signed_pairwise_of_count even (m.val.pairwise_sort (·≤·)) (by
    intro i hi
    have H:=m.property i hi
    have E:=congrArg (Multiset.count i) (m.val.sort_eq (·≤·))
    simpa only [Multiset.coe_count] using E.le.trans H)⟩
  left_inv l := by
    apply Subtype.ext
    exact List.Perm.eq_of_pairwise' ((l.val : Multiset J).pairwise_sort (·≤·))
      (l.property.imp (fun h=>h.1)) (Multiset.coe_eq_coe.mp ((l.val : Multiset J).sort_eq (·≤·)))
  right_inv m := Subtype.ext (m.val.sort_eq (·≤·))

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StringReorderingEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ)

def inputShift (d : I → ℕ) : ℤ := ∑ i,(d i:ℤ)*(κ i+1-a i i)
omit [DecidableEq I] in
@[simp] lemma inputShift_zero : inputShift a κ (0 : I → ℕ)=0 := by simp [inputShift]
omit [DecidableEq I] in
lemma inputShift_add (d e : I → ℕ) : inputShift a κ (d+e)=inputShift a κ d+inputShift a κ e := by
  simp [inputShift,add_mul,Finset.sum_add_distrib]

def normalizedEnergy (d : I → ℕ) (k : ℤ) : ℤ := inputShift a κ d-eulerForm a d d-2*k

omit [DecidableEq I] in
lemma normalizedEnergy_product (d e : I → ℕ) (k m : ℤ) :
    normalizedEnergy a κ (d+e) (k+m-eulerForm a d e)=
      normalizedEnergy a κ d k+normalizedEnergy a κ e m+(eulerForm a d e-eulerForm a e d) := by
  simp only [normalizedEnergy,inputShift_add,eulerForm_add_left,eulerForm_add_right]
  ring

variable (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def stringStartParameter (i : GlobalStringIndex a c η hc θ) : ℤ :=
  normalizedEnergy a κ i.1.val.1.val
    (stringBaseDegree a c η hc θ hχ.out i.1.val.1.val i.1.val.2 i.2.2)

lemma stringLetterEnergy (i : GlobalStringIndex a c η hc θ) :
    normalizedEnergy a κ i.1.val.1.val (globalStringPolynomialDegree a c η hc θ i)=
      stringStartParameter a κ c η hc θ i-2*i.2.1 := by
  simp only [stringStartParameter,normalizedEnergy,globalStringPolynomialDegree]
  ring

lemma stringStartParity (i : GlobalStringIndex a c η hc θ) :
    globalColorSign a c η hc θ i.1.val i.1.val=1 ↔ Even (eulerForm a i.1.val.1.val i.1.val.1.val) := by
  by_cases he : Even (eulerForm a i.1.val.1.val i.1.val.1.val)
  · simp [globalColorSign,neg_one_zpow_eq_ite,he]
  · norm_num [globalColorSign,neg_one_zpow_eq_ite,he]

omit [DecidableEq I] hχ in
lemma inputShift_word {J : Type*} (w : J → SlopeWeight c η hc θ) (l : List J) :
    inputShift a κ (wordWeight c η hc θ w l).1.val=(l.map (fun i=>inputShift a κ (w i).1.val)).sum := by
  induction l with
  | nil => simp [wordWeight]
  | cons i l ih =>
    change inputShift a κ ((w i).1.val+(wordWeight c η hc θ w l).1.val)=_
    rw [inputShift_add,ih]
    rfl

lemma stringWordEnergy (l : StringPBWIndex a c η hc θ) :
    normalizedEnergy a κ (stringPBWGrade a c η hc θ l).1.1.val
      (stringPBWGrade a c η hc θ l).2=
      (l.val.map (fun i=>stringStartParameter a κ c η hc θ i-2*i.2.1)).sum := by
  have H:=wordPolynomialDegree_shift a c η hc θ
    (fun i : GlobalStringIndex a c η hc θ=>i.1.val) (globalStringPolynomialDegree a c η hc θ) l.val
  change inputShift a κ (wordWeight c η hc θ _ l.val).1.val-
    eulerForm a (wordWeight c η hc θ _ l.val).1.val (wordWeight c η hc θ _ l.val).1.val-
    2*wordPolynomialDegree a c η hc θ _ (globalStringPolynomialDegree a c η hc θ) l.val=_
  rw [sub_sub,add_comm (eulerForm a _ _),H,inputShift_word]
  have E : ∀ j : List (GlobalStringIndex a c η hc θ),
      (j.map (fun i=>inputShift a κ i.1.val.1.val)).sum -
        (j.map (fun i=>2*globalStringPolynomialDegree a c η hc θ i+
          eulerForm a i.1.val.1.val i.1.val.1.val)).sum =
        (j.map (fun i=>stringStartParameter a κ c η hc θ i-2*i.2.1)).sum := by
    intro j
    induction j with
    | nil => simp
    | cons i j ih =>
      simp only [List.map_cons,List.sum_cons]
      have H := stringLetterEnergy a κ c η hc θ i
      dsimp only [normalizedEnergy] at H
      linear_combination ih + H
  exact E l.val

noncomputable def stringSelectionEquiv :
    StringPBWIndex a c η hc θ ≃
      ElementaryPositivity.SignedSelection (fun i : GlobalStringIndex a c η hc θ=>
        globalColorSign a c η hc θ i.1.val i.1.val=1) :=
  ElementaryPositivity.signedWordSelectionEquiv _
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveUnitRows
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
local instance instDecidableEqGlobalStringIndex : DecidableEq (GlobalStringIndex a c η hc θ) :=
  (globalStringIndexLinearOrder a c η hc θ).toDecidableEq

abbrev SlopeStringStart := Σ k : NonzeroSlopeWeight c η hc θ,
  StringBaseIndex a c η hc θ hχ.out k.val.1.val k.val.2

def stringLetterStartEquiv : GlobalStringIndex a c η hc θ ≃ SlopeStringStart a c η hc θ × ℕ where
  toFun i:=⟨⟨i.1,i.2.2⟩,i.2.1⟩
  invFun i:=⟨i.1.1,i.2,i.1.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

def slopeStartParameter (i : SlopeStringStart a c η hc θ) : ℤ :=
  normalizedEnergy a κ i.1.val.1.val
    (stringBaseDegree a c η hc θ hχ.out i.1.val.1.val i.1.val.2 i.2)

def slopeStartRowType (i : SlopeStringStart a c η hc θ) : ℕ :=
  if Even (eulerForm a i.1.val.1.val i.1.val.1.val) then 1 else 0

lemma slopeStartEven_iff (i : GlobalStringIndex a c η hc θ) :
    globalColorSign a c η hc θ i.1.val i.1.val=1 ↔
      slopeStartRowType a c η hc θ (stringLetterStartEquiv a c η hc θ i).1≠0 := by
  rw [stringStartParity]
  dsimp only [slopeStartRowType,stringLetterStartEquiv]
  split_ifs <;> simp_all

def primitiveCountEquiv : StringPBWIndex a c η hc θ ≃
    CountSelection (fun i : SlopeStringStart a c η hc θ × ℕ=>
      slopeStartRowType a c η hc θ i.1≠0) :=
  ((stringSelectionEquiv a c η hc θ).trans
    (selectionCountEquiv _)).trans
      (countReindex (stringLetterStartEquiv a c η hc θ) _ _ (slopeStartEven_iff a c η hc θ))

def primitiveRowsEquiv : StringPBWIndex a c η hc θ ≃
    SupportedUnitRows (slopeStartRowType a c η hc θ) :=
  (primitiveCountEquiv a c η hc θ).trans (allUnitRowsEquiv _)

lemma primitiveCount_energy (w : StringPBWIndex a c η hc θ) :
    (primitiveCountEquiv a c η hc θ w).val.sum (fun i n=>
      n • (slopeStartParameter a κ c η hc θ i.1-2*(i.2:ℤ)))=
      normalizedEnergy a κ (stringPBWGrade a c η hc θ w).1.1.val
        (stringPBWGrade a c η hc θ w).2 := by
  change (countReindex _ _ _ (slopeStartEven_iff a c η hc θ) _).val.sum _=_
  rw [countReindex_sum]
  change ((stringSelectionEquiv a c η hc θ w).val).toFinsupp.sum _=_
  rw [multiset_count_sum]
  rw [stringWordEnergy]
  rfl

lemma stringWord_dimension (w : List (GlobalStringIndex a c η hc θ)) :
    (w.map (fun i=>i.1.val.1.val)).sum=
      (wordWeight c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val) w).1.val := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [List.map_cons,List.sum_cons,wordWeight,Prod.fst_add,AddSubmonoid.coe_add] using congrArg (i.1.val.1.val+·) ih

lemma primitiveCount_dimension (w : StringPBWIndex a c η hc θ) :
    (primitiveCountEquiv a c η hc θ w).val.sum (fun i n=>n • i.1.1.val.1.val)=
      (stringPBWGrade a c η hc θ w).1.1.val := by
  change (countReindex _ _ _ (slopeStartEven_iff a c η hc θ) _).val.sum _=_
  rw [countReindex_sum]
  change ((stringSelectionEquiv a c η hc θ w).val).toFinsupp.sum _=_
  rw [multiset_count_sum]
  exact stringWord_dimension a c η hc θ w.val

theorem primitiveRows_energy (w : StringPBWIndex a c η hc θ) :
    rowsEnergy (slopeStartRowType a c η hc θ) (slopeStartParameter a κ c η hc θ)
      (primitiveRowsEquiv a c η hc θ w)=
      normalizedEnergy a κ (stringPBWGrade a c η hc θ w).1.1.val
        (stringPBWGrade a c η hc θ w).2 := by
  rw [primitiveRowsEquiv,Equiv.trans_apply,rowsEnergy_equiv]
  exact primitiveCount_energy a κ c η hc θ w

theorem primitiveRows_dimension (w : StringPBWIndex a c η hc θ) :
    rowsDimension (slopeStartRowType a c η hc θ) (fun i=>i.1.val.1.val)
      (primitiveRowsEquiv a c η hc θ w)=(stringPBWGrade a c η hc θ w).1.1.val := by
  rw [primitiveRowsEquiv,Equiv.trans_apply,rowsDimension_equiv]
  exact primitiveCount_dimension a c η hc θ w
end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteReorderingEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
local instance energySlopeSymmetricFact (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

noncomputable def stringBlockEnergy (d : I → ℕ) (i : StringBlockIndex a c η hc d) : ℤ :=
  (i.2.2.val.val.map (fun j=>stringStartParameter a κ c η hc (slope c η d) j-2*j.2.1)).sum

lemma stringBlockEnergy_normalized (d : I → ℕ) (i : StringBlockIndex a c η hc d) :
    stringBlockEnergy a κ c η hc d i=normalizedEnergy a κ d i.1 := by
  have H:=stringWordEnergy a κ c η hc (slope c η d) i.2.2.val
  rw [i.2.2.property] at H
  exact H.symm

noncomputable def hnStringEnergy : (l : List (I → ℕ)) → HNStringIndex a c η hc l → ℤ
  | [],_ => 0
  | d::l,i => stringBlockEnergy a κ c η hc d i.1+hnStringEnergy l i.2+
      (eulerForm a d l.sum-eulerForm a l.sum d)

lemma hnStringEnergy_normalized (l : List (I → ℕ)) (i : HNStringIndex a c η hc l) :
    hnStringEnergy a κ c η hc l i=normalizedEnergy a κ l.sum (hnStringDegree a c η hc l i) := by
  induction l with
  | nil => simp [hnStringEnergy,hnStringDegree,normalizedEnergy,eulerForm]
  | cons d l ih =>
    rcases i with ⟨i,j⟩
    change stringBlockEnergy a κ c η hc d i+hnStringEnergy a κ c η hc l j+
      (eulerForm a d l.sum-eulerForm a l.sum d)=_
    rw [stringBlockEnergy_normalized,ih]
    exact (normalizedEnergy_product a κ d l.sum i.1 (hnStringDegree a c η hc l j)).symm

omit [DecidableEq I] in
lemma normalizedEnergy_injective (d : I → ℕ) : Function.Injective (normalizedEnergy a κ d) := by
  intro x y h
  unfold normalizedEnergy at h
  omega

abbrev OutputEnergyCoefficient (d : I → ℕ) (e : ℤ) :=
  {i : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val // hnStringEnergy a κ c η hc i.1.val i.2=e}

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
universe u

lemma finite_injective_regrade {X : Type*} (f : X → ℤ)
    (hf : ∀k,Finite {x : X // f x=k}) (n : ℤ → ℤ)
    (hn : Function.Injective n) (e : ℤ) : Finite {x : X // n (f x)=e} := by
  classical
  by_cases H : ∃k,n k=e
  · obtain ⟨k,hk⟩:=H
    let := hf k
    let E : {x : X // n (f x)=e} ≃ {x : X // f x=k} :=
      Equiv.subtypeEquivRight (fun _=>by rw [←hk,hn.eq_iff])
    exact Finite.of_equiv _ E.symm
  · let : IsEmpty {x : X // n (f x)=e} := ⟨fun x=>H ⟨f x.val,x.property⟩⟩
    infer_instance

variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

local instance finiteLaurentSlopeFact_r76bd16_1 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
lemma hnStringDegree_nonneg (d : I → ℕ)
    (x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val) :
    0≤hnStringDegree a c η hc x.1.val x.2 := by
  by_contra H
  let k := hnStringDegree a c η hc x.1.val x.2
  have hk : k<0 := lt_of_not_ge H
  let : IsEmpty {i : SortedPackExponent d // (sortedPackDegree d i:ℤ)=k} :=
    ⟨fun i=>by
      have hi:=i.property
      have hn : 0≤(sortedPackDegree d i.val:ℤ) := Int.natCast_nonneg _
      omega⟩
  let := hnStringCoefficient_finite a c η hc d k
  let : Nonempty (HNStringCoefficient a c η hc d k) := ⟨⟨x,rfl⟩⟩
  have hpos : 0<Nat.card (HNStringCoefficient a c η hc d k) := Nat.card_pos
  have he := finiteStringReordering_coefficient a c η hc d k
  simp only [Nat.card_of_isEmpty] at he
  omega

lemma outputEnergy_admissible (d : I → ℕ) :
    EnergyLaurent.Admissible (fun x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val=>
      hnStringEnergy a κ c η hc x.1.val x.2) := by
  constructor
  · refine ⟨inputShift a κ d-eulerForm a d d,fun x=>?_⟩
    dsimp only
    rw [hnStringEnergy_normalized,x.1.property.1]
    have H:=hnStringDegree_nonneg a c η hc d x
    unfold normalizedEnergy
    omega
  · intro e
    let := finite_injective_regrade
      (fun x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val=>
        hnStringDegree a c η hc x.1.val x.2)
      (hnStringCoefficient_finite a c η hc d) (normalizedEnergy a κ d)
      (normalizedEnergy_injective a κ d) e
    let E : OutputEnergyCoefficient a κ c η hc d e ≃
        {x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val //
          normalizedEnergy a κ d (hnStringDegree a c η hc x.1.val x.2)=e} :=
      Equiv.subtypeEquivRight (fun x=>by rw [hnStringEnergy_normalized,x.1.property.1])
    exact Finite.of_equiv _ E.symm

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveBlockRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic UnitSelections
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
local instance blockRowsFact (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

def blockWordEquiv (d : I → ℕ) : StringBlockIndex a c η hc d ≃
    {w : StringPBWIndex a c η hc (slope c η d) //
      (stringPBWGrade a c η hc (slope c η d) w).1.1.val=d} where
  toFun i:=⟨i.2.2.val,congrArg (fun g : SlopeWeight c η hc (slope c η d) × ℤ=>g.1.1.val) i.2.2.property⟩
  invFun w:=⟨(stringPBWGrade a c η hc (slope c η d) w.val).2,
    (stringPBWGrade a c η hc (slope c η d) w.val).1.2,⟨w.val,by
      apply Prod.ext
      · apply Prod.ext
        · exact Subtype.ext w.property
        · rfl
      · rfl⟩⟩
  left_inv i:=by
    rcases i with ⟨k,W,w,hw⟩
    dsimp only
    have hk := congrArg Prod.snd hw
    have hW := congrArg (fun g : SlopeWeight c η hc (slope c η d) × ℤ => g.1.2) hw
    dsimp only at hk hW
    subst k
    subst W
    rfl
  right_inv _:=rfl

abbrev BlockRows (d : I → ℕ) :=
  {r : SupportedUnitRows (slopeStartRowType a c η hc (slope c η d)) //
    rowsDimension (slopeStartRowType a c η hc (slope c η d))
      (fun i=>i.1.val.1.val) r=d}

def blockRowsEquiv (d : I → ℕ) : StringBlockIndex a c η hc d ≃ BlockRows a c η hc d :=
  (blockWordEquiv a c η hc d).trans
    ((primitiveRowsEquiv a c η hc (slope c η d)).subtypeEquiv (fun w=>by
      rw [primitiveRows_dimension]))

def blockRowsEnergy (d : I → ℕ) (r : BlockRows a c η hc d) : ℤ :=
  rowsEnergy (slopeStartRowType a c η hc (slope c η d))
    (slopeStartParameter a κ c η hc (slope c η d)) r.val

lemma blockRowsEquiv_energy (d : I → ℕ) (w : StringBlockIndex a c η hc d) :
    blockRowsEnergy a κ c η hc d (blockRowsEquiv a c η hc d w)=
      stringBlockEnergy a κ c η hc d w := by
  change rowsEnergy _ _ (primitiveRowsEquiv a c η hc (slope c η d) w.2.2.val)=_
  rw [primitiveRows_energy,w.2.2.property,stringBlockEnergy_normalized]

def HNRowsIndex : List (I → ℕ) → Type u
  | []=>ULift.{u} Unit
  | d::l=>BlockRows a c η hc d × HNRowsIndex l

def hnRowsEquiv : (l : List (I → ℕ)) → HNStringIndex a c η hc l ≃ HNRowsIndex a c η hc l
  | []=>Equiv.refl _
  | d::l=>Equiv.prodCongr (blockRowsEquiv a c η hc d) (hnRowsEquiv l)

def hnRowsEnergy : (l : List (I → ℕ)) → HNRowsIndex a c η hc l → ℤ
  | [],_=>0
  | d::l,r=>blockRowsEnergy a κ c η hc d r.1+hnRowsEnergy l r.2+
      (eulerForm a d l.sum-eulerForm a l.sum d)

lemma hnRowsEquiv_energy (l : List (I → ℕ)) (w : HNStringIndex a c η hc l) :
    hnRowsEnergy a κ c η hc l (hnRowsEquiv a c η hc l w)=hnStringEnergy a κ c η hc l w := by
  induction l with
  | nil=>rfl
  | cons d l ih=>
    change blockRowsEnergy a κ c η hc d (blockRowsEquiv a c η hc d w.1)+
      hnRowsEnergy a κ c η hc l (hnRowsEquiv a c η hc l w.2)+_=_
    rw [blockRowsEquiv_energy,ih]
    rfl

def outputRowsEquiv (d : I → ℕ) :
    (Σ l : HNIndex c η d,HNStringIndex a c η hc l.val) ≃
      Σ l : HNIndex c η d,HNRowsIndex a c η hc l.val :=
  Equiv.sigmaCongrRight (fun l=>hnRowsEquiv a c η hc l.val)

lemma outputRows_admissible (d : I → ℕ) : EnergyLaurent.Admissible
    (fun r : Σ l : HNIndex c η d,HNRowsIndex a c η hc l.val=>hnRowsEnergy a κ c η hc r.1.val r.2) :=
  EnergyLaurent.admissible_equiv (outputEnergy_admissible a κ c η hc d)
    (outputRowsEquiv a c η hc d) (fun w=>hnRowsEquiv_energy a κ c η hc w.1.val w.2)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

local instance decoratedFact_r76bd16_1 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
abbrev RowBlock := Σ d : I → ℕ,BlockRows a c η hc d

def rowsDecorate : (l : List (I → ℕ)) → HNRowsIndex a c η hc l → List (RowBlock a c η hc)
  | [],_=>[]
  | d::l,r=>⟨d,r.1⟩::rowsDecorate l r.2

@[simp] lemma rowsDecorate_dim (l : List (I → ℕ)) (r : HNRowsIndex a c η hc l) :
    (rowsDecorate a c η hc l r).map Sigma.fst=l := by
  induction l with
  | nil=>rfl
  | cons d l ih=>simpa only [rowsDecorate,List.map_cons] using congrArg (List.cons d) (ih r.2)

def rowsUndecorate : (l : List (RowBlock a c η hc)) → HNRowsIndex a c η hc (l.map Sigma.fst)
  | []=>⟨()⟩
  | b::l=>(b.2,rowsUndecorate l)

@[simp] lemma rowsDecorate_undecorate (l : List (RowBlock a c η hc)) :
    rowsDecorate a c η hc (l.map Sigma.fst) (rowsUndecorate a c η hc l)=l := by
  induction l with
  | nil=>rfl
  | cons b l ih=>
    change b::rowsDecorate a c η hc (l.map Sigma.fst) (rowsUndecorate a c η hc l)=b::l
    rw [ih]

def rowsCons (d : I → ℕ) (r : BlockRows a c η hc d)
    (x : Σ l : List (I → ℕ),HNRowsIndex a c η hc l) :
    Σ l : List (I → ℕ),HNRowsIndex a c η hc l := ⟨d::x.1,(r,x.2)⟩

lemma rowsUndecorate_decorate (l : List (I → ℕ)) (r : HNRowsIndex a c η hc l) :
    (⟨(rowsDecorate a c η hc l r).map Sigma.fst,
      rowsUndecorate a c η hc (rowsDecorate a c η hc l r)⟩ :
      Σ l : List (I → ℕ),HNRowsIndex a c η hc l)=⟨l,r⟩ := by
  induction l with
  | nil=>
    have H : r=(⟨()⟩ : ULift Unit) := @Subsingleton.elim (ULift Unit) inferInstance r ⟨()⟩
    cases H
    rfl
  | cons d l ih=>exact congrArg (rowsCons a c η hc d r.1) (ih r.2)

abbrev DecoratedHN (d : I → ℕ) :=
  {l : List (RowBlock a c η hc) // (l.map Sigma.fst).sum=d ∧ HNOrdered c η (l.map Sigma.fst)}

def decorateOutput (d : I → ℕ) :
    (Σ l : HNIndex c η d,HNRowsIndex a c η hc l.val) ≃ DecoratedHN a c η hc d where
  toFun x:=⟨rowsDecorate a c η hc x.1.val x.2,by simpa only [rowsDecorate_dim] using x.1.property⟩
  invFun l:=⟨⟨l.val.map Sigma.fst,l.property⟩,rowsUndecorate a c η hc l.val⟩
  left_inv x:=by
    have H:=rowsUndecorate_decorate a c η hc x.1.val x.2
    exact Sigma.ext (Subtype.ext (Sigma.mk.inj H).1) (Sigma.mk.inj H).2
  right_inv l:=Subtype.ext (rowsDecorate_undecorate a c η hc l.val)

def decoratedDimension (l : List (RowBlock a c η hc)) : I → ℕ := (l.map Sigma.fst).sum

def decoratedEnergy : List (RowBlock a c η hc) → ℤ
  | []=>0
  | b::l=>blockRowsEnergy a κ c η hc b.1 b.2+decoratedEnergy l+
    (eulerForm a b.1 (decoratedDimension a c η hc l)-eulerForm a (decoratedDimension a c η hc l) b.1)

lemma decoratedEnergy_rows (l : List (I → ℕ)) (r : HNRowsIndex a c η hc l) :
    decoratedEnergy a κ c η hc (rowsDecorate a c η hc l r)=hnRowsEnergy a κ c η hc l r := by
  induction l with
  | nil=>rfl
  | cons d l ih=>
    simp only [rowsDecorate,decoratedEnergy,decoratedDimension,rowsDecorate_dim,ih,hnRowsEnergy]

lemma decoratedEnergy_admissible (d : I → ℕ) :
    EnergyLaurent.Admissible (fun l : DecoratedHN a c η hc d=>decoratedEnergy a κ c η hc l.val) :=
  EnergyLaurent.admissible_equiv (outputRows_admissible a κ c η hc d)
    (decorateOutput a c η hc d) (fun l=>decoratedEnergy_rows a κ c η hc l.1.val l.2)

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ThresholdWords
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ThresholdWords
noncomputable section
attribute [local instance] Classical.propDecidable
variable {A : Type*} (P : A → Prop) (μ : A → ℝ)

abbrev Word := {l : List A // (∀x∈l,P x) ∧ l.Pairwise (fun x y=>μ y<μ x)}
abbrev High (θ : ℝ) := {l : Word P μ // ∀x∈l.val,θ<μ x}
abbrev Low (θ : ℝ) := {l : Word P μ // ∀x∈l.val,μ x≤θ}

lemma ordered_filter_partition (θ : ℝ) (l : List A)
    (hl : l.Pairwise (fun x y=>μ y<μ x)) :
    l.filter (fun x=>decide (θ<μ x)) ++ l.filter (fun x=>decide (μ x≤θ))=l := by
  induction l with
  | nil=>rfl
  | cons x l ih=>
    have hp:=List.pairwise_cons.mp hl
    by_cases hx : θ<μ x
    · simpa only [List.filter_cons,decide_eq_true hx,decide_eq_false (not_le.mpr hx),
        Bool.false_eq_true,ite_true, if_true,ite_false, if_false,List.cons_append] using congrArg (List.cons x) (ih hp.2)
    · have hx' : μ x≤θ := le_of_not_gt hx
      have hall : ∀y∈l,μ y≤θ := fun y hy=>(hp.1 y hy).le.trans hx'
      have H : l.filter (fun x=>decide (θ<μ x))=[] := by
        simp only [List.filter_eq_nil_iff,decide_eq_true_eq]
        exact fun y hy=>not_lt.mpr (hall y hy)
      have L : l.filter (fun x=>decide (μ x≤θ))=l := by
        apply List.filter_eq_self.mpr
        simpa only [decide_eq_true_eq] using hall
      simp only [List.filter_cons,decide_eq_false hx,decide_eq_true hx',Bool.false_eq_true,ite_true, if_true,ite_false, if_false,H,L,List.nil_append]

def high (θ : ℝ) (l : Word P μ) : High P μ θ :=
  ⟨⟨l.val.filter (fun x=>decide (θ<μ x)),
    ⟨fun x hx=>l.property.1 x (List.mem_of_mem_filter hx),
      l.property.2.sublist List.filter_sublist⟩⟩,
    fun _ hx=>of_decide_eq_true (List.mem_filter.mp hx).2⟩

def low (θ : ℝ) (l : Word P μ) : Low P μ θ :=
  ⟨⟨l.val.filter (fun x=>decide (μ x≤θ)),
    ⟨fun x hx=>l.property.1 x (List.mem_of_mem_filter hx),
      l.property.2.sublist List.filter_sublist⟩⟩,
    fun _ hx=>of_decide_eq_true (List.mem_filter.mp hx).2⟩

def merge (θ : ℝ) (l : High P μ θ) (r : Low P μ θ) : Word P μ :=
  ⟨l.val.val++r.val.val,⟨fun x hx=>by
    rcases List.mem_append.mp hx with hx|hx
    · exact l.val.property.1 x hx
    · exact r.val.property.1 x hx,
    List.pairwise_append.mpr ⟨l.val.property.2,r.val.property.2,
      fun x hx y hy=>(r.property y hy).trans_lt (l.property x hx)⟩⟩⟩

@[simp] lemma merge_high_low (θ : ℝ) (l : Word P μ) :
    merge P μ θ (high P μ θ l) (low P μ θ l)=l :=
  Subtype.ext (ordered_filter_partition μ θ l.val l.property.2)

@[simp] lemma high_merge (θ : ℝ) (l : High P μ θ) (r : Low P μ θ) :
    high P μ θ (merge P μ θ l r)=l := by
  apply Subtype.ext
  apply Subtype.ext
  change (l.val.val++r.val.val).filter (fun x=>decide (θ<μ x))=l.val.val
  rw [List.filter_append]
  have H : l.val.val.filter (fun x=>decide (θ<μ x))=l.val.val := by
    apply List.filter_eq_self.mpr
    simpa only [decide_eq_true_eq] using l.property
  have L : r.val.val.filter (fun x=>decide (θ<μ x))=[] := by
    simp only [List.filter_eq_nil_iff,decide_eq_true_eq]
    exact fun x hx=>not_lt.mpr (r.property x hx)
  rw [H,L,List.append_nil]

@[simp] lemma low_merge (θ : ℝ) (l : High P μ θ) (r : Low P μ θ) :
    low P μ θ (merge P μ θ l r)=r := by
  apply Subtype.ext
  apply Subtype.ext
  change (l.val.val++r.val.val).filter (fun x=>decide (μ x≤θ))=r.val.val
  rw [List.filter_append]
  have H : l.val.val.filter (fun x=>decide (μ x≤θ))=[] := by
    simp only [List.filter_eq_nil_iff,decide_eq_true_eq]
    exact fun x hx=>not_le.mpr (l.property x hx)
  have L : r.val.val.filter (fun x=>decide (μ x≤θ))=r.val.val := by
    apply List.filter_eq_self.mpr
    simpa only [decide_eq_true_eq] using r.property
  rw [H,L,List.nil_append]

end
end ElementaryPositivity.ThresholdWords

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

abbrev LowHNWord (θ : ℝ) := ThresholdWords.Low
  (fun b : RowBlock a c η hc=>b.1≠0) (fun b=>slope c η b.1) θ

lemma hnOrdered_map_iff (l : List (RowBlock a c η hc)) :
    HNOrdered c η (l.map Sigma.fst) ↔
      (∀ b∈l,b.1≠0) ∧ l.Pairwise (fun b e=>slope c η e.1 < slope c η b.1) := by
  simp only [HNOrdered,List.forall_mem_map,List.pairwise_map]

abbrev LowHNIndex (θ : ℝ) (d : I → ℕ) :=
  {w : LowHNWord a c η hc θ // decoratedDimension a c η hc w.val.val=d}

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.EnergyLaurent
noncomputable section
lemma admissible_injective {A B : Type*} {e : A → ℤ} {f : B → ℤ}
    (he : Admissible e) (g : B → A) (hg : Function.Injective g)
    (hf : ∀b,e (g b)=f b) : Admissible f := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    exact ⟨K,fun b=>by rw [←hf]; exact hK (g b)⟩
  · intro E
    let := he.2 E
    exact Finite.of_injective (fun b : {b // f b=E}=>
      (⟨g b.val,by rw [hf,b.property]⟩ : {a // e a=E}))
      (fun x y H=>Subtype.ext (hg (congrArg Subtype.val H)))
end
end ElementaryPositivity.EnergyLaurent

namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

abbrev lowEnergy (θ : ℝ) (d : I → ℕ) (w : LowHNIndex a c η hc θ d) :=
  decoratedEnergy a κ c η hc w.val.val.val

def lowDecorated (θ : ℝ) (d : I → ℕ) (w : LowHNIndex a c η hc θ d) : DecoratedHN a c η hc d :=
  ⟨w.val.val.val,⟨w.property,(hnOrdered_map_iff a c η hc _).mpr w.val.val.property⟩⟩

lemma lowEnergy_admissible (θ : ℝ) (d : I → ℕ) : Admissible (lowEnergy a κ c η hc θ d) :=
  admissible_injective (decoratedEnergy_admissible a κ c η hc d) (lowDecorated a c η hc θ d)
    (fun _ _ H=>Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : DecoratedHN a c η hc d=>z.val) H)))) (fun _=>rfl)

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_StringStripSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I → ℕ)) (k : S → ℤ)
variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
variable (he : ∀d,Admissible (stringEnergy a dim k d))

include hτ he in
omit [Fintype I] [DecidableEq I] in
lemma shiftedString_admissible (d : I → ℕ) :
    Admissible (stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d) :=
  admissible_injective (admissible_shift (he d) (2*τ d)) id Function.injective_id
    (fun x=>(stringEnergy_shift a t dim τ hτ k d x).symm)

include hτ he in
omit [Fintype I] [DecidableEq I] in
lemma stripEnergy_admissible (d : I → ℕ) : Admissible (stripEnergy a t dim k d) :=
  admissible_injective (shiftedString_admissible a t dim k τ hτ he d)
    (stripInsert a t dim d) (stripInsert_injective a t dim d) (stripInsert_energy a t dim k d)

def stripSeries (d : I → ℕ) : LaurentSeries ℚ :=
  series _ (stripEnergy_admissible a t dim k τ hτ he d)

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_WeightedPushTwist
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus RawShuffle PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
local instance instRingTorus_1 : Ring (Torus v Ω) := Torus.instRing v Ω

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open WallUnits PowerSeries
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StringPositiveFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WallUnits WeightedTorusSeries
open PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D)

def stringSeries (d : I→ℕ) : LaurentSeries ℚ := series _ (he d)

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_StringBackshift
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WallUnits WeightedTorusSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
variable (he : ∀d,Admissible (stringEnergy a dim k d))

omit [Fintype I] [DecidableEq I] in
include hτ in
lemma stringEnergy_backshift (d : I→ℕ) (x : StringCounts a dim d) :
    stringEnergy a dim (fun s=>k s-2*(t s:ℤ)) d x=
      stringEnergy a dim k d x-2*τ d := by
  have H:=stringEnergy_shift a t dim τ hτ (fun s=>k s-2*(t s:ℤ)) d x
  have hk : (fun s=>k s-2*(t s:ℤ)+2*(t s:ℤ))=k := by funext s; ring
  rw [hk] at H
  omega

omit [Fintype I] [DecidableEq I] in
include hτ he in
lemma backshiftString_admissible (d : I→ℕ) :
    Admissible (stringEnergy a dim (fun s=>k s-2*(t s:ℤ)) d) :=
  admissible_injective (admissible_shift (he d) (-(2*τ d))) id Function.injective_id
    (fun x=>by simpa only [sub_eq_add_neg,id_eq,Equiv.refl_apply] using
      (stringEnergy_backshift a t dim k τ hτ d x).symm)

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNZeroRows
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

def lowFromRow (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (r : BlockRows a c η hc d) : LowHNIndex a c η hc θ d :=
  ⟨⟨⟨[⟨d,r⟩],by simp [hd]⟩,by simp [hs]⟩,by simp [decoratedDimension]⟩

lemma lowFromRow_injective (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) :
    Function.Injective (lowFromRow a c η hc θ d hd hs) := by
  intro r s H
  have H':=congrArg (fun x : LowHNIndex a c η hc θ d=>x.val.val.val) H
  simpa only [lowFromRow,List.cons.injEq,and_true,Sigma.mk.inj_iff,heq_eq_eq,true_and] using H'

lemma lowFromRow_energy (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (r : BlockRows a c η hc d) :
    lowEnergy a κ c η hc θ d (lowFromRow a c η hc θ d hd hs r)=blockRowsEnergy a κ c η hc d r := by
  simp [lowEnergy,lowFromRow,decoratedEnergy,decoratedDimension,eulerForm]

lemma blockRowsEnergy_admissible (d : I → ℕ) (hd : d≠0) :
    Admissible (blockRowsEnergy a κ c η hc d) :=
  admissible_injective (lowEnergy_admissible a κ c η hc (slope c η d) d)
    (lowFromRow a c η hc (slope c η d) d hd rfl)
    (lowFromRow_injective a c η hc (slope c η d) d hd rfl)
    (lowFromRow_energy a κ c η hc (slope c η d) d hd rfl)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance instFactSlopeEulerSymmetric (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

abbrev PrimitiveCounts (θ : ℝ) (d : I → ℕ) :=
  DimensionCounts (fun x : SlopeStringStart a c η hc θ × ℕ=>slopeStartRowType a c η hc θ x.1≠0)
    (fun x=>x.1.1.val.1.val) d

def primitiveCountsEnergy (θ : ℝ) (d : I → ℕ) (x : PrimitiveCounts a c η hc θ d) : ℤ :=
  countEnergy _ (fun x=>slopeStartParameter a κ c η hc θ x.1-2*(x.2:ℤ)) x.val

lemma primitiveCounts_onSlope (θ : ℝ) (d : I → ℕ) (x : PrimitiveCounts a c η hc θ d) :
    OnSlopeOrZero c η θ d := by
  rw [←x.property]
  exact countDimension_mem _ _ (slopeDimensions c η hc θ) (fun x=>x.1.1.val.1.property) x.val

def primitiveCountsRows (d : I → ℕ) :
    PrimitiveCounts a c η hc (slope c η d) d ≃ BlockRows a c η hc d :=
  (allUnitRowsEquiv (slopeStartRowType a c η hc (slope c η d))).subtypeEquiv
    (fun x=>by rw [rowsDimension_equiv]; rfl)

lemma primitiveCountsRows_energy (d : I → ℕ) (x : PrimitiveCounts a c η hc (slope c η d) d) :
    blockRowsEnergy a κ c η hc d (primitiveCountsRows a c η hc d x)=
      primitiveCountsEnergy a κ c η hc (slope c η d) d x := by
  change rowsEnergy _ _ (allUnitRowsEquiv _ x.val)=_
  rw [rowsEnergy_equiv]
  rfl

lemma primitiveCountsEnergy_admissible (θ : ℝ) (d : I → ℕ) :
    Admissible (primitiveCountsEnergy a κ c η hc θ d) := by
  classical
  by_cases hd : d=0
  · subst d
    let := dimensionCounts_zero_subsingleton
      (fun x : SlopeStringStart a c η hc θ × ℕ=>slopeStartRowType a c η hc θ x.1≠0)
      (fun x=>x.1.1.val.1.val) (fun x=>x.1.1.property)
    refine ⟨⟨0,fun x=>?_⟩,fun E=>inferInstance⟩
    change countEnergy _ _ x.val≤0
    rw [dimensionCounts_zero_energy _ _ (fun x=>x.1.1.property)]
  · by_cases h : Nonempty (PrimitiveCounts a c η hc θ d)
    · have hs : slope c η d=θ := (primitiveCounts_onSlope a c η hc θ d h.some).resolve_left hd
      subst θ
      exact admissible_injective (blockRowsEnergy_admissible a κ c η hc d hd)
        (primitiveCountsRows a c η hc d) (primitiveCountsRows a c η hc d).injective
        (primitiveCountsRows_energy a κ c η hc d)
    · let : IsEmpty (PrimitiveCounts a c η hc θ d) := not_nonempty_iff.mp h
      exact ⟨⟨0,fun x=>isEmptyElim x⟩,fun _=>inferInstance⟩

def primitiveCountsSeries (θ : ℝ) (d : I → ℕ) : LaurentSeries ℚ :=
  series _ (primitiveCountsEnergy_admissible a κ c η hc θ d)

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WeightedInverseAdjoint
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus RawShuffle PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
local instance instRingTorus_2 : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end


