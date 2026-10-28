-- Prove2me | Definitions.Def_Sensitivity213981Formal_MarkedTwoRows
-- name    : Sensitivity213981Formal_MarkedTwoRows
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:08:06.950549+00:00
-- url     : https://prove2.me/theorems/1ec98959-9dfc-4dbb-961c-52d3a512c862
-- title:
--   Marked Two Rows — sensitivity certificate definitions
-- statement:
--   The definitions for Marked Two Rows in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRefinedMarked.assignments_count`, `ThreeBoundRefinedMarked.localProbability_le`, `ThreeBoundRefinedMarked.rowBudget`, `ThreeBoundRefinedMarked.headFactor`, `ThreeBoundRefinedMarked.two_marker_product`, `ThreeBoundRefinedMarked.good_row_bound`, `ThreeBoundRefinedMarked.pattern_product_le`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MarkedTwoRows.lean, lines 1–132.

import Definitions.Def_Sensitivity213981Formal_LabelMarked
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
/- Two marked rows retain the failure already spent on their internal arc. -/

set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace ThreeBoundRefinedMarked
open Sensitivity10007Labeling ZL ZL.RowCounting
open scoped Classical BigOperators
noncomputable section
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

def rowBudget (R : V→V→Prop) (A M : Finset V) (q : ℕ) : A⊕M→ℕ :=
  Sum.elim (fun x=>q-(outOn R M x.val).card)
    (fun y=>q+1-(outOn R M y.val).card)

theorem good_row_bound (R : V→V→Prop) (ell : V×V→Fin 2)
    (A M P : Finset V) (q B : ℕ) (color : V→Fin 2)
    (h : MarkedGood R ell A M P q B color) (i : A⊕M) :
    ((markedRows R A M i).filter (fun e=>ell e≠color e.2)).card≤ rowBudget R A M q i := by
  cases i with
  | inl i =>
    rw [markedRows,Sum.elim_inl,outgoingRow_filter_card]
    change (mismatch R ell A color i.val).card≤ q-(outOn R M i.val).card
    exact Nat.le_sub_of_add_le (h.1 i.val i.property)
  | inr i =>
    rw [markedRows,Sum.elim_inr,outgoingRow_filter_card]
    change (mismatch R ell A color i.val).card≤ q+1-(outOn R M i.val).card
    have hh:=h.2.1 i.val i.property
    split_ifs at hh <;> omega

theorem assignments_count (R : V→V→Prop) (A M P : Finset V) (q B : ℕ) :
    (markedAssignments R A M P q B).card≤ 
      2^A.card*(∏i:A⊕M,rowPatterns (rowBudget R A M q i) (markedRows R A M i).card)*
        2^(Fintype.card (V×V)-(markedSupport R A M).card) := by
  let encoded : Finset ((V×V)→Fin 2):=Finset.univ.biUnion fun c:A→Fin 2=>
    rowGood (markedRows R A M) (rowBudget R A M q) (headColor A c)
  have hsub : markedAssignments R A M P q B⊆encoded := by
    intro ell hell
    obtain ⟨c,hc⟩:=(Finset.mem_filter.mp hell).2
    apply Finset.mem_biUnion.mpr
    refine ⟨(fun x=>c x.val),Finset.mem_univ _,?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i
    have hh:=good_row_bound R ell A M P q B c hc i
    convert hh using 1
    congr 1
    apply Finset.filter_congr
    intro e he
    have hey:e.2∈A := by
      cases i with
      | inl i =>
        obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp he
        exact (Finset.mem_filter.mp hj).1
      | inr i =>
        obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp he
        exact (Finset.mem_filter.mp hj).1
    simp only [headColor,dif_pos hey]
  have hg (c:A→Fin 2) :
      (rowGood (markedRows R A M) (rowBudget R A M q) (headColor A c)).card≤ 
        2^(Fintype.card (V×V)-(markedSupport R A M).card)*
          ∏i:A⊕M,rowPatterns (rowBudget R A M q i) (markedRows R A M i).card := by
    simpa only [markedRows_union] using rowGood_card_le
      (markedRows R A M) (rowBudget R A M q) (headColor A c)
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_biUnion_le.trans
  calc
    (∑c:A→Fin 2,(rowGood (markedRows R A M) (rowBudget R A M q) (headColor A c)).card)≤ 
        ∑_c:A→Fin 2,2^(Fintype.card (V×V)-(markedSupport R A M).card)*
          ∏i:A⊕M,rowPatterns (rowBudget R A M q i) (markedRows R A M i).card :=
      Finset.sum_le_sum fun c _=>hg c
    _=_ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_coe,
        Fintype.card_fin,Nat.nsmul_eq_mul]
      ring

theorem localProbability_le (F : SupportedFamily (V×V) D) (d:D)
    (R : V→V→Prop) (A M P : Finset V) (q B : ℕ)
    (hs:F.support d=markedSupport R A M)
    (hb:∀ell,F.bad d ell↔MarkedBad R ell A M P q B) :
    F.localProbability d≤ 
      ((2^A.card*∏i:A⊕M,rowPatterns (rowBudget R A M q i)
        (markedRows R A M i).card : ℕ):ℚ)/2^(markedSupport R A M).card := by
  rw [←hs]
  apply F.localProbability_le_of_global
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hb),hs]
  simpa only [Fintype.card_subtype,markedAssignments] using assignments_count R A M P q B

def headFactor (q a:ℕ):ℕ := rowPatterns q a*rowPatterns (q+1) a

theorem two_marker_product (R : V→V→Prop)
    (hloop:∀x,¬R x x) (htour:∀x y,x≠y→(R x y↔¬R y x))
    (A M:Finset V) (q:ℕ) (hm:M.card=2) :
    (∏y:M,rowPatterns (q+1-(outOn R M y.val).card) (outOn R A y.val).card)≤ 
      headFactor q A.card := by
  rw [Finset.prod_coe_sort (s:=M) (f:=fun y:V=>
    rowPatterns (q+1-(outOn R M y).card) (outOn R A y).card)]
  obtain ⟨x,y,hxy,rfl⟩:=Finset.card_eq_two.mp hm
  have hprod : (∏z∈({x,y}:Finset V),
      rowPatterns (q+1-(outOn R {x,y} z).card) (outOn R A z).card)=
      rowPatterns (q+1-(outOn R {x,y} x).card) (outOn R A x).card*
      rowPatterns (q+1-(outOn R {x,y} y).card) (outOn R A y).card := by
    rw [Finset.prod_pair hxy]
  rw [hprod]
  have hxle : (outOn R A x).card≤ A.card:=Finset.card_le_card (Finset.filter_subset _ _)
  have hyle : (outOn R A y).card≤ A.card:=Finset.card_le_card (Finset.filter_subset _ _)
  by_cases hr:R x y
  · have hn:¬R y x:=(htour x y hxy).mp hr
    have hx:(outOn R {x,y} x).card=1:=by simp [outOn,Finset.filter_insert,Finset.filter_singleton,hloop,hr]
    have hy:(outOn R {x,y} y).card=0:=by simp [outOn,Finset.filter_insert,Finset.filter_singleton,hloop,hn]
    rw [hx,hy,Nat.add_sub_cancel,Nat.sub_zero]
    exact Nat.mul_le_mul (rowPatterns_mono_degree _ _ _ hxle) (rowPatterns_mono_degree _ _ _ hyle)
  · have hr':R y x:=(htour y x hxy.symm).mpr hr
    have hx:(outOn R {x,y} x).card=0:=by simp [outOn,Finset.filter_insert,Finset.filter_singleton,hloop,hr]
    have hy:(outOn R {x,y} y).card=1:=by simp [outOn,Finset.filter_insert,Finset.filter_singleton,hloop,hr']
    rw [hx,hy,Nat.add_sub_cancel,Nat.sub_zero]
    simpa only [headFactor,mul_comm] using
      (Nat.mul_le_mul (rowPatterns_mono_degree (q+1) _ A.card hxle)
        (rowPatterns_mono_degree q _ A.card hyle))

theorem pattern_product_le (R : V→V→Prop)
    (hloop:∀x,¬R x x) (htour:∀x y,x≠y→(R x y↔¬R y x))
    (A M:Finset V) (q:ℕ) (hm:M.card=2) :
    (∏i:A⊕M,rowPatterns (rowBudget R A M q i) (markedRows R A M i).card)≤ 
      (∏x:A,rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card)*
        headFactor q A.card := by
  rw [Fintype.prod_sum_type]
  simp only [rowBudget,markedRows,Sum.elim_inl,Sum.elim_inr,outgoingRow_card]
  exact Nat.mul_le_mul_left _ (two_marker_product R hloop htour A M q hm)

end
end ThreeBoundRefinedMarked


end
end Sensitivity213981Formal


