-- Prove2me | Definitions.Def_Sensitivity213981Formal_LabelOrdinary
-- name    : Sensitivity213981Formal_LabelOrdinary
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:36:39.786821+00:00
-- url     : https://prove2.me/theorems/0086390e-a113-4d92-945e-2b5d17861d4e
-- title:
--   Label Ordinary — sensitivity certificate definitions
-- statement:
--   The definitions for Label Ordinary in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity10007Labeling.ZL.ordinary_localProbability_le`, `Sensitivity10007Labeling.ZL.ordinary_row_degree_lt`, `Sensitivity10007Labeling.ZL.card_powersetCard_containing_le`, `Sensitivity10007Labeling.ZL.ordinary_row_product_bound`, `Sensitivity10007Labeling.ZL.RowCounting.smallSubsets_card_le`, `Sensitivity10007Labeling.ZL.ordinaryIndex_incidence_le`, `Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.ordinaryFamily_load_le`, `Sensitivity10007Labeling.ZL.RowCounting.rowGood_card_le_smallSubsets`, `Sensitivity10007Labeling.ZL.RowCounting.rowGood_card_le`, `Sensitivity10007Labeling.ZL.RowCounting.tangent_product_cancel`, `Sensitivity10007Labeling.ZL.internalEdges_card_eq_sum`, `Sensitivity10007Labeling.ZL.RowCounting.balanced_product_le`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; LabelOrdinary.lean, lines 1–551.

import Definitions.Def_Sensitivity213981Formal_LabelCard
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace Sensitivity213981Formal
section
/- Reassembled from supplied accepted Prove2me source proofs. See provenance.json. -/


namespace Sensitivity10007Labeling


/- Source: Sol_Paley11987Verified_CompactLabeling_ordinaryFamily_load_le.lean -/
set_option autoImplicit false
set_option Elab.async false
section z0

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]











theorem internalEdges_card_eq_sum (R : V → V → Prop) (S : Finset V) :
    (internalEdges R S).card = ∑ x ∈ S, (outOn R S x).card := by
  simp only [internalEdges, outOn, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]

theorem ordinary_degree_sum (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x)) (S : Finset V) :
    ∑ x ∈ S, (outOn R S x).card = S.card.choose 2 := by
  rw [← internalEdges_card_eq_sum, _root_.Sensitivity213981Formal.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges R hloop htour]



















end
end ZL
end
end z0

section z1

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL.RowCounting
noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω]





theorem smallSubsets_card_le (R : Finset Ω) (q : ℕ) :
    (smallSubsets R q).card ≤  rowPatterns q R.card := by
  let f : (smallSubsets R q) →
      (Σ j : Fin (q + 1), R.powersetCard j.val) := fun s =>
    ⟨⟨s.val.card, by
        have hs := (Finset.mem_filter.mp s.property).2
        omega⟩,
      ⟨s.val, Finset.mem_powersetCard.mpr
        ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp s.property).1, rfl⟩⟩⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact congrArg
      (fun z : (Σ j : Fin (q + 1), R.powersetCard j.val) =>
        (z.2 : Finset Ω)) h
  have hc := Fintype.card_le_of_injective f hf
  calc
    (smallSubsets R q).card ≤ 
        Fintype.card (Σ j : Fin (q + 1), R.powersetCard j.val) := by
      simpa only [Fintype.card_coe] using hc
    _ = ∑ j : Fin (q + 1), Fintype.card (R.powersetCard j.val) :=
      Fintype.card_sigma
    _ = rowPatterns q R.card := by
      simp only [rowPatterns, Fintype.card_coe, Finset.card_powersetCard]





theorem rowGood_card_le_smallSubsets
    (R : ι → Finset Ω) (q : ι → ℕ) (c : Ω → Fin 2) :
    (rowGood R q c).card ≤ 
      2 ^ (Fintype.card Ω - (rowUnion R).card) *
        ∏ i, (smallSubsets (R i) (q i)).card := by
  let S := rowUnion R
  let encode : (rowGood R q c) →
      ((Sᶜ : Finset Ω) → Fin 2) ×
        ((i : ι) → smallSubsets (R i) (q i)) := fun a =>
    ⟨fun e => a.val e.val,
      fun i =>
        ⟨(R i).filter (fun e => a.val e ≠ c e),
          Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
              (Finset.mem_filter.mp a.property).2 i⟩⟩⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    funext e
    by_cases he : e ∈ S
    · obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
      have hs := congrArg
        (fun z : ((Sᶜ : Finset Ω) → Fin 2) ×
            ((i : ι) → smallSubsets (R i) (q i)) =>
          (z.2 i : Finset Ω)) hab
      have hm := (Finset.ext_iff.mp hs) e
      simp only [encode, Finset.mem_filter, hei, true_and] at hm
      apply Fin.ext
      have ha := (a.val e).isLt
      have hb := (b.val e).isLt
      have hc := (c e).isLt
      have hm' : ((a.val e).val ≠ (c e).val) ↔
          ((b.val e).val ≠ (c e).val) := by
        simpa only [ne_eq, Fin.ext_iff] using hm
      omega
    · exact congrArg
        (fun z : ((Sᶜ : Finset Ω) → Fin 2) ×
            ((i : ι) → smallSubsets (R i) (q i)) =>
          z.1 ⟨e, Finset.mem_compl.mpr he⟩) hab
  have hc := Fintype.card_le_of_injective encode hencode
  simpa [S, Fintype.card_pi, Finset.card_compl] using hc

theorem rowGood_card_le
    (R : ι → Finset Ω) (q : ι → ℕ) (c : Ω → Fin 2) :
    (rowGood R q c).card ≤ 
      2 ^ (Fintype.card Ω - (rowUnion R).card) *
        ∏ i, rowPatterns (q i) (R i).card := by
  refine (rowGood_card_le_smallSubsets R q c).trans ?_
  apply Nat.mul_le_mul_left
  exact Finset.prod_le_prod' (fun i _ => smallSubsets_card_le (R i) (q i))

theorem tangent_product_cancel (n a b M N P : ℕ)
    (hb : b ≤  n) (hM : 0 <  M) (hN : 0 <  N)
    (hprod : P * M ^ (a * n + b) * N ^ (a * n) ≤ 
      M ^ ((a + 1) * n) * N ^ (a * n + b)) :
    P ≤  M ^ (n - b) * N ^ b := by
  have he : (a + 1) * n = (a * n + b) + (n - b) := by
    calc
      (a + 1) * n = a * n + n := by ring
      _ = (a * n + b) + (n - b) := by omega
  let C := M ^ (a * n + b) * N ^ (a * n)
  have hC : 0 <  C := Nat.mul_pos (pow_pos hM _) (pow_pos hN _)
  have hr : M ^ ((a + 1) * n) * N ^ (a * n + b) =
      (M ^ (n - b) * N ^ b) * C := by
    rw [he, pow_add, pow_add]
    dsimp only [C]
    ring
  have hh : P * C ≤  (M ^ (n - b) * N ^ b) * C := by
    simpa only [C, mul_assoc, hr] using hprod
  by_contra hn
  have hlt : M ^ (n - b) * N ^ b <  P := Nat.lt_of_not_ge hn
  have hc := Nat.mul_lt_mul_of_pos_right hlt hC
  exact (not_lt_of_ge hh) hc

theorem balanced_product_le (d F : ι → ℕ) (a b M N : ℕ)
    (hb : b ≤  Fintype.card ι) (hM : 0 <  M) (hN : 0 <  N)
    (hs : ∑ i, d i = a * Fintype.card ι + b)
    (ht : ∀ i, F i * M ^ (d i) * N ^ a ≤  M ^ (a + 1) * N ^ (d i)) :
    ∏ i, F i ≤  M ^ (Fintype.card ι - b) * N ^ b := by
  apply tangent_product_cancel (Fintype.card ι) a b M N (∏ i, F i) hb hM hN
  have hp := Finset.prod_le_prod' (s := Finset.univ) (fun i _ => ht i)
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, hs] at hp
  simpa only [mul_comm a, mul_comm (a + 1)] using hp

end
end ZL.RowCounting
end
end z1

section z9

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

namespace SupportedFamily
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
variable (F : SupportedFamily V D)





theorem globalBad_card (d : D) :
    Fintype.card {ell : V → Fin 2 // F.bad d ell} =
      Fintype.card (F.LocalBad d) * 2 ^ (Fintype.card V - (F.support d).card) := by
  rw [Fintype.card_congr (F.globalBadEquiv d)]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_coe,Finset.card_compl]

theorem localBad_card_le_of_global (d : D) (B : ℕ)
    (h : Fintype.card {ell : V → Fin 2 // F.bad d ell} ≤ 
      B * 2 ^ (Fintype.card V - (F.support d).card)) :
    Fintype.card (F.LocalBad d) ≤  B := by
  rw [F.globalBad_card] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

theorem localProbability_le_of_global (d : D) (B : ℕ)
    (h : Fintype.card {ell : V → Fin 2 // F.bad d ell} ≤ 
      B * 2 ^ (Fintype.card V - (F.support d).card)) :
    F.localProbability d ≤  (B : ℚ) / 2 ^ (F.support d).card := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast F.localBad_card_le_of_global d B h)
    (by positivity)
end SupportedFamily

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

open RowCounting



theorem outgoingRow_card (A : Finset V) (i : V) :
    (outgoingRow R A i).card = (outOn R A i).card := by
  apply Finset.card_image_of_injective
  intro x y h
  exact congrArg Prod.snd h

theorem outgoingRow_filter_card (A : Finset V) (i : V)
    (P : V × V → Prop) [DecidablePred P] :
    ((outgoingRow R A i).filter P).card =
      (A.filter (fun j => R i j ∧ P (i,j))).card := by
  rw [outgoingRow,Finset.filter_image,Finset.card_image_of_injective]
  · rw [outOn,Finset.filter_filter]
  · intro x y h
    exact congrArg Prod.snd h



theorem ordinaryRows_union (A : Finset V) :
    rowUnion (ordinaryRows R A) = internalEdges R A := by
  ext e
  simp only [rowUnion,Finset.mem_biUnion,Finset.mem_univ,true_and,
    ordinaryRows,outgoingRow,Finset.mem_image,outOn,Finset.mem_filter,
    internalEdges,Finset.mem_product]
  constructor
  · rintro ⟨i,j,⟨hj,hij⟩,he⟩
    subst e
    exact ⟨⟨i.property,hj⟩,hij⟩
  · rintro ⟨⟨hi,hj⟩,hij⟩
    exact ⟨⟨e.1,hi⟩,e.2,⟨hj,hij⟩,rfl⟩





theorem ordinaryAssignments_count (A : Finset V) (q : ℕ) :
    (ordinaryAssignments R A q).card ≤ 
      2 ^ A.card *
        (∏ i : A, rowPatterns q (outOn R A i.val).card) *
          2 ^ (Fintype.card (V × V) - (internalEdges R A).card) := by
  let encoded : Finset ((V × V) → Fin 2) :=
    Finset.univ.biUnion fun c : A → Fin 2 =>
      rowGood (ordinaryRows R A) (fun _ => q) (headColor A c)
  have hsub : ordinaryAssignments R A q ⊆ encoded := by
    intro ell hell
    obtain ⟨c,hc⟩ := (Finset.mem_filter.mp hell).2
    apply Finset.mem_biUnion.mpr
    refine ⟨(fun x => c x.val),Finset.mem_univ _,?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i
    rw [ordinaryRows,outgoingRow_filter_card]
    convert hc i.val i.property using 1
    congr 1
    unfold mismatch
    apply Finset.filter_congr
    intro x hx
    simp only [headColor,dif_pos hx]
  have hg (c : A → Fin 2) :
      (rowGood (ordinaryRows R A) (fun _ => q) (headColor A c)).card ≤ 
        2 ^ (Fintype.card (V × V) - (internalEdges R A).card) *
          ∏ i : A, rowPatterns q (outOn R A i.val).card := by
    have h := rowGood_card_le (ordinaryRows R A) (fun _ => q) (headColor A c)
    simpa only [ordinaryRows_union,ordinaryRows,outgoingRow_card] using h
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_biUnion_le.trans
  calc
    (∑ c : A → Fin 2, (rowGood (ordinaryRows R A) (fun _ => q) (headColor A c)).card) ≤ 
      ∑ _c : A → Fin 2, 2 ^ (Fintype.card (V × V) - (internalEdges R A).card) *
        ∏ i : A, rowPatterns q (outOn R A i.val).card := Finset.sum_le_sum fun c _ => hg c
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_coe,
        Fintype.card_fin,Nat.nsmul_eq_mul]
      ring

end
end ZL
end
end z9

section z13

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

theorem ordinary_localProbability_le (F : SupportedFamily (V × V) D) (d : D)
    (R : V → V → Prop) (A : Finset V) (q : ℕ)
    (hs : F.support d = internalEdges R A)
    (hb : ∀ ell, F.bad d ell ↔ OrdinaryBad R ell A q) :
    F.localProbability d ≤ 
      ((2 ^ A.card * ∏ i : A, rowPatterns q (outOn R A i.val).card : ℕ) : ℚ) /
        2 ^ (internalEdges R A).card := by
  rw [← hs]
  apply F.localProbability_le_of_global
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hb),hs]
  simpa only [Fintype.card_subtype,ordinaryAssignments] using ordinaryAssignments_count R A q













end
end ZL
end
end z13

section z15

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]





theorem ordinary_row_degree_lt (R : V → V → Prop) (hloop : ∀ x, ¬ R x x)
    (A : Finset V) (x : A) : (outOn R A x.val).card <  A.card := by
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨x.val,x.property,hloop x.val⟩)











end
end ZL
end
end z15

section z18

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [DecidableEq V]



theorem card_powersetCard_containing_le (S T : Finset V) (a : ℕ) :
    ((S.powersetCard a).filter (fun A => T ⊆ A)).card ≤ 
      S.card.choose (a-T.card) := by
  let F := (S.powersetCard a).filter (fun A => T ⊆ A)
  have hinj : Set.InjOn (fun A : Finset V => A \ T) (F : Set (Finset V)) := by
    intro A hA B hB he
    have hAT := (Finset.mem_filter.mp hA).2
    have hBT := (Finset.mem_filter.mp hB).2
    have hh := congrArg (fun C : Finset V => T ∪ C) he
    simpa only [Finset.union_sdiff_of_subset hAT,Finset.union_sdiff_of_subset hBT] using hh
  have hsub : F.image (fun A => A \ T) ⊆ S.powersetCard (a-T.card) := by
    intro B hB
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hA,hT⟩ := Finset.mem_filter.mp hA
    obtain ⟨hAS,hcard⟩ := Finset.mem_powersetCard.mp hA
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset.trans hAS,?_⟩
    rw [Finset.card_sdiff_of_subset hT,hcard]
  calc
    F.card = (F.image (fun A => A \ T)).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤  (S.powersetCard (a-T.card)).card := Finset.card_le_card hsub
    _ = _ := Finset.card_powersetCard _ _



end
end ZL
end
end z18

section z19

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ordinary_row_product_bound (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A : Finset V) (q a lo rem L H : ℕ) (hA : A.card=a)
    (hrem : rem ≤  a) (hL : 0 <  L) (hH : 0 <  H)
    (hdegree : lo*a+rem=a.choose 2)
    (htan : ∀ d <  a, rowPatterns q d * L^d * H^lo ≤  L^(lo+1)*H^d) :
    (∏ x : A, rowPatterns q (outOn R A x.val).card) ≤  L^(a-rem)*H^rem := by
  have hsum : (∑ x : A, (outOn R A x.val).card) = lo*Fintype.card A+rem := by
    rw [Finset.sum_coe_sort (s := A) (f := fun x : V => (outOn R A x).card),
      ordinary_degree_sum R hloop htour,Fintype.card_coe,hA,hdegree]
  have hh := balanced_product_le (fun x : A => (outOn R A x.val).card)
    (fun x : A => rowPatterns q (outOn R A x.val).card) lo rem L H
    (by simpa only [Fintype.card_coe,hA] using hrem) hL hH hsum
    (fun x => htan _ (by simpa only [hA] using ordinary_row_degree_lt R hloop A x))
  simpa only [Fintype.card_coe,hA] using hh

theorem ordinaryIndex_incidence_le (R : V → V → Prop) (a : ℕ)
    (x y : V) (hxy : x ≠ y) :
    ((Finset.univ : Finset (OrdinaryIndex V a)).filter
      (fun I => (x,y) ∈ internalEdges R I.val)).card ≤ 
      (Fintype.card V).choose (a-2) := by
  let G := ((Finset.univ : Finset V).powersetCard a).filter (fun A => {x,y} ⊆ A)
  have hi : ((Finset.univ : Finset (OrdinaryIndex V a)).filter
      (fun I => (x,y) ∈ internalEdges R I.val)).card ≤  G.card := by
    apply Finset.card_le_card_of_injOn (fun I : OrdinaryIndex V a => I.val)
    · intro I hI
      have he := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hI).2).1
      exact Finset.mem_filter.mpr ⟨I.property,by
        simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using he⟩
    · intro I hI J hJ he
      exact Subtype.ext he
  have hg := card_powersetCard_containing_le (Finset.univ : Finset V) {x,y} a
  exact hi.trans (by simpa only [G,Finset.card_univ,Finset.card_pair hxy] using hg)

theorem _root_.Sensitivity213981Formal.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.ordinaryFamily_load_le (R : V → V → Prop) (n : ℕ)
    (hn : Fintype.card V=n)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (q a lo rem L H : ℕ) (lam : ℚ) (hlam : 0 ≤  lam)
    (hrem : rem ≤  a) (hL : 0 <  L) (hH : 0 <  H)
    (hdegree : lo*a+rem=a.choose 2)
    (htan : ∀ d <  a, rowPatterns q d * L^d * H^lo ≤  L^(lo+1)*H^d)
    (x y : V) :
    (∑ I ∈ Finset.univ.filter (fun I => (x,y) ∈ (ordinaryFamily R q a).support I),
      (ordinaryFamily R q a).localProbability I * lam^(a.choose 2)) / 2 ≤ 
      (n.choose (a-2) : ℚ) *
        ((2 : ℚ)^a * (L^(a-rem)*H^rem : ℕ) / (2 : ℚ)^(a.choose 2)) *
        lam^(a.choose 2) / 2 := by
  let P : ℚ := (2 : ℚ)^a * (L^(a-rem)*H^rem : ℕ) / (2 : ℚ)^(a.choose 2)
  have hP : 0 ≤  P := by dsimp [P]; positivity
  have hp (I : OrdinaryIndex V a) : (ordinaryFamily R q a).localProbability I ≤  P := by
    have hA := (Finset.mem_powersetCard.mp I.property).2
    have hcard := _root_.Sensitivity213981Formal.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges R hloop htour I.val
    have hlocal := ordinary_localProbability_le (ordinaryFamily R q a) I R I.val q rfl (fun _ => Iff.rfl)
    rw [hcard,hA] at hlocal
    apply hlocal.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hprod := ordinary_row_product_bound R hloop htour I.val q a lo rem L H
      hA hrem hL hH hdegree htan
    have hh := Nat.mul_le_mul_left (2^a) hprod
    exact_mod_cast hh
  by_cases hR : R x y
  · have hxy : x ≠ y := by rintro rfl; exact hloop x hR
    have hc := ordinaryIndex_incidence_le R a x y hxy
    rw [hn] at hc
    rw [← Finset.sum_mul]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam _)
    calc
      (∑ I ∈ Finset.univ.filter (fun I => (x,y) ∈ (ordinaryFamily R q a).support I),
        (ordinaryFamily R q a).localProbability I) ≤ 
          ∑ _I ∈ Finset.univ.filter (fun I => (x,y) ∈ (ordinaryFamily R q a).support I), P :=
        Finset.sum_le_sum fun I _ => hp I
      _ = (((Finset.univ : Finset (OrdinaryIndex V a)).filter
          (fun I => (x,y) ∈ internalEdges R I.val)).card : ℚ)*P := by
        simp only [Finset.sum_const,nsmul_eq_mul,ordinaryFamily]
        congr 2 <;> ext I <;> simp
      _ ≤  (n.choose (a-2) : ℚ)*P := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hP
  · have hempty : (Finset.univ.filter (fun I : OrdinaryIndex V a =>
        (x,y) ∈ (ordinaryFamily R q a).support I)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro I _ hi
      exact hR (Finset.mem_filter.mp hi).2
    rw [hempty,Finset.sum_empty,zero_div]
    positivity

end
end ZL
end
end z19

end Sensitivity10007Labeling

end
end Sensitivity213981Formal


