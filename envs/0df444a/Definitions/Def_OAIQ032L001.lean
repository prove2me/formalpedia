-- Prove2me | Definitions.Def_OAIQ032L001
-- name    : OAIQ032L001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:42:08.69328+00:00
-- url     : https://prove2.me/theorems/1edc7e1a-53eb-4c01-98ee-2e1dbb5dc36b
-- title:
--   Definitions bundle OAIQ032L001 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 29 definitions, 1 inductive type or structure, 4 instances and 33 theorems. The definitions and types are `OAI.Lech.AlternatingCech.connectingSortedDecEq`, `OAI.Lech.AlternatingCech.faceSliceSortedDecEq`, `OAI.Lech.AlternatingCech.familyEquiv`, `OAI.Lech.AlternatingCech.familyMap`, `OAI.Lech.ArtinReesLength.colength`, `OAI.Lech.ArtinReesLength.induced`, `OAI.Lech.AwayCover.Total`, `OAI.Lech.AwayCover.denominator`, `OAI.Lech.BicomplexTotal.Diagonal`, `OAI.Lech.BicomplexTotal.Double`, `OAI.Lech.BicomplexTotal.Row`, `OAI.Lech.BicomplexTotal.degreeMap`, `OAI.Lech.BicomplexTotal.functor`, `OAI.Lech.BicomplexTotal.intoSingle`, `OAI.Lech.BicomplexTotal.singleZero`, `OAI.Lech.BicomplexTotal.splitting`, `OAI.Lech.BicomplexTotal.totalSingleZero`, `OAI.Lech.BinaryChange.transform`, `OAI.Lech.DoubleCech.emptyIndex`, `OAI.Lech.FactorDescent.R`, `OAI.Lech.FieldLift.liftElement`, `OAI.Lech.FieldLift.powLift`, `OAI.Lech.FieldPartialLift.Lifts`, `OAI.Lech.FieldPartialLift.Lifts.union`, `OAI.Lech.FiniteComplex.dropTop`, `OAI.Lech.FiniteComplex.dropTopXIso`, `OAI.Lech.FiniteComplex.topInclusion`, `OAI.Lech.FiniteComplex.topShortComplex`, `OAI.Lech.FiniteComplex.topSplitting`, `OAI.Lech.ProductLaurent.Exponent`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ArbitraryCoefficientField`, `Multiplicity_FieldNilpotentLift`, `Multiplicity_FilteredFractionReesDenominatorTheory`, `Multiplicity_FiniteComplexTopInclusion`, `Multiplicity_LechConnectingIso`, `Multiplicity_NativeDescentCanonicalAlg`, `Multiplicity_PrimeFiltrationSupport`, `Multiplicity_PrimitiveChartFaithfullyFlat`, `Multiplicity_PrincipalCoverRegularRegularMap`, `Multiplicity_ProductSourceCoverAllowedEmpty`, `Multiplicity_ProductSourceCoverFaceSlice`, `Multiplicity_ProductSourceCoverOrdinaryPositive`, `Multiplicity_TotalExact`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L010`, `OAIQ032L011`, `OAIQ032L014` and `OAIQ032L015`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FieldNilpotentLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial IntermediateField
namespace Lech.FieldLift
universe u v
variable {k : Type u} {A : Type v} [Field k] [CommRing A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]
  (J : Ideal A) (hJ : J^p=⊥) (f : k →+* A ⧸ J)
include hJ

lemma pow_eq_of_quotient_eq {x y : A} (h : Ideal.Quotient.mk J x=Ideal.Quotient.mk J y) :
    x^p=y^p := by
  have hh := Ideal.pow_mem_pow (Ideal.Quotient.eq.mp h) p
  rw [hJ,Ideal.mem_bot] at hh
  rw [sub_pow_char] at hh
  exact sub_eq_zero.mp hh

omit hJ in
def liftElement (a : k) : A := (Ideal.Quotient.mk_surjective (f a)).choose
omit hJ in
lemma liftElement_spec (a : k) : Ideal.Quotient.mk J (liftElement J f a)=f a :=
  (Ideal.Quotient.mk_surjective (f a)).choose_spec

 
def powLift : k →+* A where
  toFun a := (liftElement J f a)^p
  map_one' := by
    calc
      (liftElement J f 1)^p=(1:A)^p := pow_eq_of_quotient_eq p J hJ (by rw [liftElement_spec,map_one,map_one])
      _=1 := one_pow p
  map_mul' a b := by
    rw [← mul_pow]
    apply pow_eq_of_quotient_eq p J hJ
    simp only [map_mul,liftElement_spec]
  map_zero' := by
    calc
      (liftElement J f 0)^p=(0:A)^p := pow_eq_of_quotient_eq p J hJ (by rw [liftElement_spec,map_zero,map_zero])
      _=0 := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' a b := by
    rw [← add_pow_char]
    apply pow_eq_of_quotient_eq p J hJ
    simp only [map_add,liftElement_spec]

omit [CharP k p] in
lemma powLift_mod (a : k) : Ideal.Quotient.mk J (powLift p J hJ f a)=f (a^p) := by
  change Ideal.Quotient.mk J ((liftElement J f a)^p)=_
  rw [map_pow,liftElement_spec,map_pow]

end Lech.FieldLift

namespace Lech.FieldPartialLift
variable (F E A : Type*) [Field F] [Field E] [CommRing A] [Algebra F E] [Algebra F A]
 
structure Lifts where
  carrier : IntermediateField F E
  emb : carrier →ₐ[F] A
variable {F E A}
namespace Lifts
instance instPartialOrder : PartialOrder (Lifts F E A) where
  le L₁ L₂ := ∃ h : L₁.carrier ≤ L₂.carrier, ∀ x, L₂.emb (inclusion h x)=L₁.emb x
  le_refl L := ⟨le_rfl,by simp⟩
  le_trans L₁ L₂ L₃ := by
    rintro ⟨h₁₂,h₁₂'⟩ ⟨h₂₃,h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃,fun x => ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃,h₂₃',h₁₂']
  le_antisymm := by
    rintro ⟨L₁,e₁⟩ ⟨L₂,e₂⟩ ⟨h₁₂,h₁₂'⟩ ⟨h₂₁,h₂₁'⟩
    obtain rfl : L₁=L₂ := h₁₂.antisymm h₂₁
    congr
    exact AlgHom.ext h₂₁'
noncomputable instance instOrderBot : OrderBot (Lifts F E A) where
  bot := ⟨⊥,(Algebra.ofId F A).comp (botEquiv F E)⟩
  bot_le L := ⟨bot_le,fun x => by
    obtain ⟨x,rfl⟩ := (botEquiv F E).symm.surjective x
    simp_rw [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
    exact L.emb.commutes x⟩

variable (c : Set (Lifts F E A)) (hc : IsChain (· ≤ ·) c)
noncomputable def union : Lifts F E A :=
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  have hc := hc.insert fun _ _ _ => .inl bot_le
  have dir : Directed (· ≤ ·) t := hc.directedOn.directed_val.mono_comp _ fun _ _ h => h.1
  ⟨iSup t, (Subalgebra.iSupLift (toSubalgebra <| t ·) dir (·.val.emb) (fun i j h =>
    AlgHom.ext fun x => (hc.total i.2 j.2).elim (fun hij => (hij.snd x).symm) fun hji => by
      rw [AlgHom.comp_apply, ← inclusion]
      dsimp only [coe_type_toSubalgebra]
      rw [← hji.snd (inclusion h x), inclusion_inclusion, inclusion_self, AlgHom.id_apply x])
    _ le_rfl).comp
      (Subalgebra.equivOfEq _ _ <| toSubalgebra_iSup_of_directed dir)⟩

lemma le_union {σ : Lifts F E A} (hσ : σ ∈ c) : σ ≤ union c hc := by
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  refine ⟨le_iSup t ⟨σ,Or.inr hσ⟩,fun x => ?_⟩
  dsimp only [union,AlgHom.comp_apply]
  have hc' := hc.insert fun _ _ _ => .inl bot_le
  have dir : Directed (· ≤ ·) t := hc'.directedOn.directed_val.mono_comp _ fun _ _ h => h.1
  have compatible (i j : ↑(insert ⊥ c)) (h : (t i).toSubalgebra ≤ (t j).toSubalgebra) :
      i.val.emb = j.val.emb.comp (Subalgebra.inclusion h) := by
    apply AlgHom.ext
    intro x
    exact (hc'.total i.2 j.2).elim (fun hij => (hij.snd x).symm) (fun hji => by
      rw [AlgHom.comp_apply, ← inclusion]
      rw [← hji.snd (inclusion h x), inclusion_inclusion, inclusion_self, AlgHom.id_apply x])
  exact Subalgebra.iSupLift_inclusion (K := (toSubalgebra <| t ·)) (f := fun i => i.val.emb)
    (dir := dir) (hf := compatible) (hT := le_rfl)
    (i:=⟨σ,Or.inr hσ⟩) x (le_iSup (toSubalgebra <| t ·) ⟨σ,Or.inr hσ⟩)
end Lifts
end Lech.FieldPartialLift

namespace Lech.FieldPartialLift
open Lifts
variable {F E A Q : Type*} [Field F] [Field E] [CommRing A] [CommRing Q]
  [Algebra F E] [Algebra F A] [Algebra F Q]
  (p : ℕ) [Fact p.Prime] [CharP E p]
  (f : E →ₐ[F] Q) (t : A →ₐ[F] Q)
lemma extend_root (φ : Lifts F E A)
    (hφ : ∀ y : φ.carrier,t (φ.emb y)=f y)
    (a : E) (ha : a ∉ φ.carrier) (c : F) (hc : algebraMap F E c=a^p)
    (x : A) (hx : t x=f a) (hxp : x^p=algebraMap F A c) :
    ∃ ψ : Lifts F E A,φ < ψ ∧ ∀ y : ψ.carrier,t (ψ.emb y)=f y := by
  let L := φ.carrier
  let : Algebra L A := φ.emb.toAlgebra
  let : Algebra L Q := (f.comp L.val).toAlgebra
  let g : L[X] := X^p-C (algebraMap F L c)
  have hirr : Irreducible g := by
    apply (X_pow_sub_C_irreducible_iff_of_prime (Fact.out : p.Prime)).mpr
    intro b hb
    apply ha
    have hbE := congrArg (algebraMap L E) hb
    have he : (b:E)^p=a^p := by
      change (b:E)^p=algebraMap F E c at hbE
      exact hbE.trans hc
    have hb' : (b:E)=a := (frobenius E p).injective he
    exact hb' ▸ b.2
  have hzero : aeval a g=0 := by
    simp only [g,map_sub,map_pow,aeval_X,aeval_C]
    change a^p-algebraMap F E c=0
    rw [hc,sub_self]
  have hm : g.Monic := monic_X_pow_sub_C (algebraMap F L c) (Fact.out : p.Prime).ne_zero
  have haI : IsIntegral L a := ⟨g,hm,hzero⟩
  have hmin : minpoly L a=g := (minpoly.eq_of_irreducible_of_monic hirr hzero hm).symm
  let pb := IntermediateField.adjoin.powerBasis haI
  have hxpoly : aeval x (minpoly L pb.gen)=0 := by
    rw [IntermediateField.adjoin.powerBasis_gen,IntermediateField.minpoly_gen,hmin]
    simp only [g,map_sub,map_pow,aeval_X,aeval_C]
    change x^p-φ.emb (algebraMap F L c)=0
    rw [φ.emb.commutes c,hxp,sub_self]
  let b := pb.lift x hxpoly
  let ψ : Lifts F E A := ⟨L⟮a⟯.restrictScalars F,b.restrictScalars F⟩
  refine ⟨ψ,?_,?_⟩
  · apply lt_iff_le_not_ge.mpr
    have hL : φ ≤ ψ := ⟨by
      change L ≤ L⟮a⟯.restrictScalars F
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]
      exact le_sup_left,fun y => b.commutes y⟩
    refine ⟨hL,?_⟩
    intro hh
    exact ha (hh.1 (IntermediateField.subset_adjoin L {a} (Set.mem_singleton a)))
  · let tL : A →ₐ[L] Q := {t.toRingHom with commutes' := hφ}
    let fL : E →ₐ[L] Q := {f.toRingHom with commutes' := fun _ => rfl}
    have he : tL.comp b=fL.comp L⟮a⟯.val := by
      apply pb.algHom_ext
      rw [AlgHom.comp_apply,PowerBasis.lift_gen]
      exact hx
    intro y
    exact AlgHom.congr_fun he y
end Lech.FieldPartialLift

namespace Lech.FieldPartialLift
open Lifts
variable {F E A Q : Type*} [Field F] [Field E] [CommRing A] [CommRing Q]
  [Algebra F E] [Algebra F A] [Algebra F Q]
  (p : ℕ) [Fact p.Prime] [CharP E p]
  (f : E →ₐ[F] Q) (t : A →ₐ[F] Q)
lemma bot_compatible : ∀ y : (⊥ : Lifts F E A).carrier,t ((⊥ : Lifts F E A).emb y)=f y := by
  intro y
  obtain ⟨a,rfl⟩ := (IntermediateField.botEquiv F E).symm.surjective y
  change t (((Algebra.ofId F A).comp (botEquiv F E)) ((botEquiv F E).symm a))=_
  simp only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
  rw [show ((botEquiv F E).symm a : E)=algebraMap F E a from rfl]
  exact (t.commutes a).trans (f.commutes a).symm

lemma mem_union (c : Set (Lifts F E A)) (hc : IsChain (· ≤ ·) c)
    (y : E) (hy : y ∈ (Lifts.union c hc).carrier) :
    ∃ φ ∈ insert ⊥ c,y ∈ φ.carrier := by
  let T (i : ↑(insert ⊥ c)) := i.val.carrier
  have hc' := hc.insert (fun _ _ _ => Or.inl (bot_le : (⊥ : Lifts F E A) ≤ _))
  have hd : Directed (· ≤ ·) T := hc'.directedOn.directed_val.mono_comp _ fun _ _ h => h.1
  change y ∈ ⨆ i,T i at hy
  rw [← SetLike.mem_coe,IntermediateField.coe_iSup_of_directed hd,Set.mem_iUnion] at hy
  obtain ⟨i,hi⟩ := hy
  exact ⟨i.val,i.2,hi⟩

lemma compatible_of_mem {φ ψ : Lifts F E A} (h : φ ≤ ψ)
    (hφ : ∀ z : φ.carrier,t (φ.emb z)=f z) (y : ψ.carrier) (hy : (y:E) ∈ φ.carrier) :
    t (ψ.emb y)=f y := by
  let z : φ.carrier := ⟨y,hy⟩
  have hz : inclusion h.1 z=y := rfl
  rw [← hz,h.2]
  exact hφ z

lemma union_compatible (c : Set (Lifts F E A)) (hc : IsChain (· ≤ ·) c)
    (H : ∀ φ ∈ c, ∀ y : φ.carrier,t (φ.emb y)=f y) :
    ∀ y : (Lifts.union c hc).carrier,t ((Lifts.union c hc).emb y)=f y := by
  intro y
  obtain ⟨φ,hφ,hy⟩ := mem_union c hc y y.2
  have hle : φ ≤ Lifts.union c hc := by
    rcases hφ with rfl | he
    · exact bot_le
    · exact Lifts.le_union c hc he
  have hiC : ∀ z : φ.carrier,t (φ.emb z)=f z := by
    rcases hφ with rfl | he
    · exact bot_compatible f t
    · exact H _ he
  exact compatible_of_mem f t hle hiC y hy

lemma exists_lift_of_roots
    (H : ∀ a : E,∃ c : F,algebraMap F E c=a^p ∧
      ∃ x : A,t x=f a ∧ x^p=algebraMap F A c) :
    ∃ g : E →ₐ[F] A,t.comp g=f := by
  obtain ⟨φ,hφ⟩ := zorn_le₀ {φ : Lifts F E A | ∀ y : φ.carrier,t (φ.emb y)=f y}
    (fun c hC hc => ⟨Lifts.union c hc,union_compatible f t c hc hC,
      fun σ hσ => Lifts.le_union c hc hσ⟩)
  have hcompat := hφ.1
  have htop : φ.carrier=⊤ := by
    by_contra hn
    obtain ⟨a,_,ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hn)
    obtain ⟨c,hc,x,hx,hxp⟩ := H a
    obtain ⟨ψ,hlt,hψ⟩ := extend_root p f t φ hcompat a ha c hc x hx hxp
    exact (not_lt_of_ge (hφ.2 hψ hlt.le)) hlt
  let e : φ.carrier ≃ₐ[F] E := (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  refine ⟨φ.emb.comp e.symm.toAlgHom,?_⟩
  ext a
  exact hcompat (e.symm a)
end Lech.FieldPartialLift

namespace Lech.FieldLift
variable {k A : Type*} [Field k] [CommRing A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]
  (J : Ideal A) (hJ : J^p=⊥) (f : k →+* A ⧸ J)
include p hJ
 

theorem exists_lift : ∃ g : k →+* A,(Ideal.Quotient.mk J).comp g=f := by
  let F := (frobenius k p).fieldRange
  let e : k ≃+* F := (frobenius k p).rangeRestrictFieldEquiv
  let τ : F →+* A := (powLift p J hJ f).comp e.symm.toRingHom
  let : Algebra F A := τ.toAlgebra
  let : Algebra F (A ⧸ J) := (f.comp (frobenius k p).fieldRange.subtype).toAlgebra
  let t : A →ₐ[F] A ⧸ J := {Ideal.Quotient.mk J with
    commutes' := fun c => by
      change Ideal.Quotient.mk J (powLift p J hJ f (e.symm c))=f (c:k)
      rw [powLift_mod]
      exact congrArg f ((frobenius k p).rangeRestrictFieldEquiv_apply_symm_apply c) }
  let f' : k →ₐ[F] A ⧸ J := {f with commutes' := fun _ => rfl}
  obtain ⟨g,hg⟩ := FieldPartialLift.exists_lift_of_roots p f' t (fun a => by
    refine ⟨e a,rfl,liftElement J f a,liftElement_spec J f a,?_⟩
    change (liftElement J f a)^p=powLift p J hJ f (e.symm (e a))
    rw [e.symm_apply_apply]
    rfl)
  exact ⟨g.toRingHom,congrArg AlgHom.toRingHom hg⟩
end Lech.FieldLift

namespace Lech.FieldLift
variable {k A Q : Type*} [Field k] [CommRing A] [CommRing Q]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]
 
theorem exists_lift_surjective (t : A →+* Q) (ht : Function.Surjective t)
    (hker : (RingHom.ker t)^p=⊥) (f : k →+* Q) :
    ∃ g : k →+* A,t.comp g=f := by
  let e := RingHom.quotientKerEquivOfSurjective ht
  obtain ⟨g,hg⟩ := exists_lift p (RingHom.ker t) hker (e.symm.toRingHom.comp f)
  refine ⟨g,?_⟩
  apply RingHom.ext
  intro x
  have hh := RingHom.congr_fun hg x
  have hh' := congrArg e hh
  simpa [e] using hh'
end Lech.FieldLift

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ArbitraryCoefficientField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ArbitraryCoefficientField
variable {k R : Type*} [Field k] [CommRing R]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP R p] (I : Ideal R) [I.IsMaximal]

lemma power_strictMono : StrictMono (fun n : ℕ => p^n) :=
  pow_right_strictMono₀ (Nat.Prime.one_lt (Fact.out : p.Prime))

omit [CharP R p] [I.IsMaximal] in
lemma transition_ker (n : ℕ) :
    (RingHom.ker (Ideal.Quotient.factorPow I
      ((power_strictMono p).monotone (Nat.le_succ n))))^p=⊥ := by
  rw [Ideal.Quotient.factor_ker,← Ideal.map_pow,← pow_mul,← pow_succ]
  exact Ideal.map_quotient_self _

end Lech.ArbitraryCoefficientField

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
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

noncomputable def topInclusion : (single C (ComplexShape.up ℤ) n).obj (F.X n) ⟶ F :=
  mkHomFromSingle (𝟙 _) (by
    intro i hi
    have hi' : n + 1 = i := hi
    exact (hn i (by omega)).eq_of_tgt _ _)

instance topInclusion_mono : Mono (topInclusion F n hn) := by
  apply mono_of_mono_f
  intro i
  by_cases hi : i = n
  · subst i
    dsimp [topInclusion]
    rw [mkHomFromSingle_f, Category.comp_id]
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hi).mono _

noncomputable def dropTop : CochainComplex C ℤ := cokernel (topInclusion F n hn)

noncomputable def topShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (topInclusion F n hn) (cokernel.π _) (cokernel.condition _)

lemma topShortExact : (topShortComplex F n hn).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := topInclusion_mono F n hn
  epi_g := inferInstanceAs (Epi (cokernel.π (topInclusion F n hn)))

lemma topShortExact_eval (i : ℤ) :
    ((topShortComplex F n hn).map (eval C (ComplexShape.up ℤ) i)).ShortExact :=
  (topShortExact F n hn).map_of_exact _

lemma topInclusion_f_isIso : IsIso ((topInclusion F n hn).f n) := by
  dsimp [topInclusion]
  rw [mkHomFromSingle_f, Category.comp_id]
  infer_instance

lemma dropTop_X_top : IsZero ((dropTop F n hn).X n) := by
  apply (topShortExact_eval F n hn n).isIso_f_iff.mp
  exact topInclusion_f_isIso F n hn

lemma dropTop_π_isIso (i : ℤ) (hi : i ≠ n) :
    IsIso ((cokernel.π (topInclusion F n hn)).f i) := by
  apply (topShortExact_eval F n hn i).isIso_g_iff.mpr
  exact isZero_single_obj_X (ComplexShape.up ℤ) n (F.X n) i hi

noncomputable def dropTopXIso (i : ℤ) (hi : i ≠ n) :
    F.X i ≅ (dropTop F n hn).X i := by
  exact @asIso _ _ _ _ ((cokernel.π (topInclusion F n hn)).f i)
    (dropTop_π_isIso F n hn i hi)

noncomputable def topSplitting (i : ℤ) :
    ((topShortComplex F n hn).map (eval C (ComplexShape.up ℤ) i)).Splitting := by
  let S := (topShortComplex F n hn).map (eval C (ComplexShape.up ℤ) i)
  have hS : S.ShortExact := topShortExact_eval F n hn i
  by_cases hi : i = n
  · subst i
    haveI : IsIso S.f := topInclusion_f_isIso F n hn
    exact ShortComplex.Splitting.ofExactOfRetraction S hS.exact (inv S.f)
      (by simp) hS.epi_g
  · haveI : IsIso S.g := dropTop_π_isIso F n hn i hi
    exact ShortComplex.Splitting.ofExactOfSection S hS.exact (inv S.g)
      (by simp) hS.mono_f

omit hn in
lemma isZero_of_X (hF : ∀ i, IsZero (F.X i)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  exact (hF i).eq_of_src _ _


end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
end Lech.FiniteComplex


namespace Lech.BicomplexTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
abbrev Row := CochainComplex (ModuleCat.{u} R) ℤ
abbrev Double := CochainComplex (Row (R := R)) ℤ
abbrev functor : Double (R := R) ⥤ Row (R := R) :=
  totalFunctor (ModuleCat.{u} R) (.up ℤ) (.up ℤ) (.up ℤ)
variable {F G H : Double (R := R)}
def degreeMap (a : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    ((functor (R := R)).obj F).X i ⟶ ((functor (R := R)).obj G).X i :=
  totalDesc F (fun p q hpq => (a p).f q ≫ ιTotal G (.up ℤ) p q i hpq)
@[reassoc (attr := simp)] lemma ι_degreeMap (a : ∀ j, F.X j ⟶ G.X j)
    (p q i : ℤ) (hpq : p+q=i) :
    ιTotal F (.up ℤ) p q i hpq ≫ degreeMap a i =
      (a p).f q ≫ ιTotal G (.up ℤ) p q i hpq := by
  apply ι_totalDesc
lemma degreeMap_id (i : ℤ) : degreeMap (fun j => 𝟙 (F.X j)) i = 𝟙 _ := by
  apply total.hom_ext
  intro p q hpq
  change _ = ιTotal F (.up ℤ) p q i hpq ≫ 𝟙 ((total F (.up ℤ)).X i)
  simp
lemma degreeMap_comp (a : ∀ j, F.X j ⟶ G.X j) (b : ∀ j, G.X j ⟶ H.X j) (i : ℤ) :
    degreeMap (fun j => a j ≫ b j) i=degreeMap a i ≫ degreeMap b i := by
  apply total.hom_ext
  intro p q hpq
  exact (ι_degreeMap (fun j => a j ≫ b j) p q i hpq).trans
    ((Category.assoc _ _ _).trans
      ((congrArg ((a p).f q ≫ ·) (ι_degreeMap b p q i hpq).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ degreeMap b i) (ι_degreeMap a p q i hpq).symm).trans
            (Category.assoc _ _ _)))))
lemma degreeMap_add (a b : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    degreeMap (fun j => a j+b j) i=degreeMap a i+degreeMap b i := by
  apply total.hom_ext
  intro p q hpq
  exact (ι_degreeMap (fun j => a j + b j) p q i hpq).trans
    ((Preadditive.add_comp _ _ _ _ _ _).trans
      ((congrArg₂ (· + ·) (ι_degreeMap a p q i hpq).symm
        (ι_degreeMap b p q i hpq).symm).trans (Preadditive.comp_add _ _ _ _ _ _).symm))
lemma map_f (f : F ⟶ G) (i : ℤ) :
    ((functor (R := R)).map f).f i=degreeMap f.f i := by
  apply total.hom_ext
  intro p q hpq
  exact (ιTotal_map F G f (.up ℤ) p q i hpq).trans (ι_degreeMap f.f p q i hpq).symm
instance instAdditiveDoubleRowFunctor : (functor (R := R)).Additive where
  map_add {F G} f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    change ((functor (R := R)).map (f+g)).f i=((functor (R := R)).map f).f i+((functor (R := R)).map g).f i
    simp only [map_f]
    exact degreeMap_add f.f g.f i
 
def splitting (S : ShortComplex (Double (R := R)))
    (s : ∀ j, (S.map (eval (Row (R := R)) (.up ℤ) j)).Splitting) (i : ℤ) :
    ((S.map (functor (R := R))).map (eval (ModuleCat.{u} R) (.up ℤ) i)).Splitting where
  r := degreeMap (fun j => (s j).r) i
  s := degreeMap (fun j => (s j).s) i
  f_r := by
    change ((functor (R := R)).map S.f).f i ≫ degreeMap (fun j => (s j).r) i = 𝟙 _
    erw [map_f,←degreeMap_comp]
    erw [show (fun j => S.f.f j ≫ (s j).r)=(fun j => 𝟙 (S.X₁.X j)) from
      funext (fun j => (s j).f_r),degreeMap_id]
  s_g := by
    change degreeMap (fun j => (s j).s) i ≫ ((functor (R := R)).map S.g).f i = 𝟙 _
    erw [map_f,←degreeMap_comp]
    erw [show (fun j => (s j).s ≫ S.g.f j)=(fun j => 𝟙 (S.X₃.X j)) from
      funext (fun j => (s j).s_g),degreeMap_id]
  id := by
    change degreeMap (fun j => (s j).r) i ≫ ((functor (R := R)).map S.f).f i + ((functor (R := R)).map S.g).f i ≫ degreeMap (fun j => (s j).s) i = 𝟙 _
    erw [map_f,map_f,←degreeMap_comp,←degreeMap_comp,←degreeMap_add]
    erw [show (fun j => (show S.X₂.X j ⟶ S.X₁.X j from (s j).r) ≫ S.f.f j + S.g.f j ≫ (show S.X₃.X j ⟶ S.X₂.X j from (s j).s))=
      (fun j => 𝟙 (S.X₂.X j)) from funext (fun j => (s j).id),degreeMap_id]
end Lech.BicomplexTotal

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
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


namespace Lech.FiniteCoverCech
open scoped BigOperators
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w}
lemma delete_insert_zero {n : ℕ} (j : ι) (a : Fin n → ι) :
    Fin.cons j a ∘ (0:Fin (n+1)).succAbove=a := by funext i;simp
lemma delete_insert_succ {n : ℕ} (j : ι) (a : Fin (n+1) → ι) (i : Fin (n+1)) :
    Fin.cons j a ∘ i.succ.succAbove=Fin.cons j (a ∘ i.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp [Fin.succ_succAbove_succ]

variable [Fintype ι] [DecidableEq ι]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
variable (q : ι → R) (hq : Ideal.span (Set.range q)=⊤)
  (hclear : ∀ (s : Finset ι) (j : ι) (x : M), x∈F (insert j s) → ∃ m : ℕ,q j^m • x∈F s)
include hq in
omit [DecidableEq ι] in
lemma partition (N : ℕ) : ∃ c : ι → R,∑ j,c j*(q j)^N=1 := by
  have hp : Ideal.span (Set.range (fun j => q j^N))=⊤ := by
    simpa only [←Set.range_comp,Function.comp_def] using (Ideal.span_pow_eq_top (Set.range q) hq N)
  have hm := (Ideal.eq_top_iff_one _).mp hp
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm
  exact ⟨c,hc⟩
end Lech.FiniteCoverCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrincipalCoverRegularRegularMap
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


namespace Lech.ProductLaurent
open AddMonoidAlgebra Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev Exponent := Fin n →₀ ℤ
end Lech.ProductLaurent


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


namespace Lech.AlternatingCech
open scoped BigOperators
open Set
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
local instance faceSliceSortedDecEq : DecidableEq ι := Classical.decEq ι
end Lech.AlternatingCech


namespace Lech.BicomplexTotal

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable (F : Row (R := R))
abbrev singleZero := (single (Row (R := R)) (.up ℤ) 0).obj F
abbrev totalSingleZero := total (singleZero F) (.up ℤ)
def intoSingle (i : ℤ) : F.X i ⟶ (totalSingleZero F).X i :=
  (singleObjXSelf (.up ℤ) 0 F).inv.f i ≫ ιTotal (singleZero F) (.up ℤ) 0 i i (by simp)
lemma single_d₁ (p q j : ℤ) : d₁ (singleZero F) (.up ℤ) p q j=0 := by
  by_cases h : (p+1)+q=j
  · rw [d₁_eq _ _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl) q j h]
    simp
  · rw [d₁_eq_zero' _ _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl) q j h]
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


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
local instance connectingSortedDecEq : DecidableEq ι := Classical.decEq ι
end Lech.AlternatingCech


namespace Lech.DoubleCech


open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
def emptyIndex : powersetCard ι 0 := ⟨∅,Finset.card_empty⟩
omit [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ] in
lemma zeroIndex_eq (s : powersetCard ι 0) : s=emptyIndex := by
  apply Subtype.ext
  exact Finset.card_eq_zero.mp s.property


end Lech.DoubleCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverAllowedEmpty
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


namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]
variable (N : Type u) [AddCommGroup N] [Module R N]
variable {ι : Type}
variable (F : Finset ι → Submodule R M) (G : Finset ι → Submodule R N)
variable (φ : M →ₗ[R] N) (hφ : Function.Injective φ) (hFG : ∀ s,(F s).map φ=G s)
def familyMap (s : Finset ι) : F s →ₗ[R] G s :=
  (φ.comp (F s).subtype).codRestrict (G s) (fun x => hFG s ▸ Submodule.mem_map.mpr ⟨x,x.property,rfl⟩)
include hφ in
lemma familyMap_injective (s : Finset ι) : Function.Injective (familyMap R M N F G φ hFG s) := by
  intro x y h
  apply Subtype.ext
  exact hφ (congrArg Subtype.val h)
lemma familyMap_surjective (s : Finset ι) : Function.Surjective (familyMap R M N F G φ hFG s) := by
  rintro ⟨y,hy⟩
  obtain ⟨x,hx,rfl⟩ := Submodule.mem_map.mp ((hFG s).symm ▸ hy)
  exact ⟨⟨x,hx⟩,rfl⟩
def familyEquiv (s : Finset ι) : F s ≃ₗ[R] G s :=
  LinearEquiv.ofBijective (familyMap R M N F G φ hFG s)
    ⟨familyMap_injective R M N F G φ hφ hFG s,familyMap_surjective R M N F G φ hFG s⟩
end Lech.AlternatingCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverOrdinaryPositive
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


namespace Lech.AwayCover
universe u w
variable {R : Type u} [CommRing R]

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (q : ι → R)
def denominator (s : Finset ι) : R := ∏ i∈s,q i
omit [Fintype ι] in
lemma denominator_dvd {s v : Finset ι} (h : s ⊆ v) : denominator q s ∣ denominator q v := by
  refine ⟨denominator q (v\s),?_⟩
  simpa only [denominator,mul_comm] using (Finset.prod_sdiff (f := q) h).symm
abbrev Total := Localization.Away (denominator q Finset.univ)
end Lech.AwayCover


end
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

def transform (f : B[X]) (n : ℕ) (t : B) : B[X] :=
  ∑ k ∈ Finset.range (n+1), C (f.coeff k)*(C t*Polynomial.X+1)^k*Polynomial.X^(n-k)

end Lech.BinaryChange


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
variable (f : A[X])
  (n : ℕ)
  (hn : f.natDegree≤n)
  (t : B)
  (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))

abbrev R := B ⊗[A] T
end Lech.FactorDescent


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimeFiltrationSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ArtinReesLength
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (I : Ideal R) (N : Submodule R M)
abbrev induced (n : ℕ) : Submodule R N := (I^n • (⊤ : Submodule R M)).comap N.subtype
end Lech.ArtinReesLength

namespace Lech.ArtinReesLength
open scoped TensorProduct
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def colength (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  (Module.length R (M ⧸ I ^ n • (⊤ : Submodule R M))).toNat

open Filter
open scoped Topology
end Lech.ArtinReesLength

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalExact
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
abbrev Diagonal (k : ℤ) := (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) ⁻¹' {k}

end Lech.BicomplexTotal

end

end OAI
end


