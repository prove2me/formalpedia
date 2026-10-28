-- Prove2me | Definitions.Def_Sensitivity213981Formal_LabelMarked
-- name    : Sensitivity213981Formal_LabelMarked
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:39:02.798818+00:00
-- url     : https://prove2.me/theorems/dfe050dd-74b1-4f2e-b8c8-d48405c551fa
-- title:
--   Label Marked — sensitivity certificate definitions
-- statement:
--   The definitions for Label Marked in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity10007Labeling.ZL.markedAssignments_count`, `Sensitivity10007Labeling.ZL.crossEdges_card`, `Sensitivity10007Labeling.ZL.markedSupport_card_add`, `Sensitivity10007Labeling.ZL.powersetCard_outOn`, `Sensitivity10007Labeling.ZL.marked_localProbability_le`, `Sensitivity10007Labeling.ZL.rowPatterns_zero`, `Sensitivity10007Labeling.ZL.rowPatterns_mono_degree`, `Sensitivity10007Labeling.ZL.marked_pattern_product_le`, `Sensitivity10007Labeling.ZL.orientation_weight_sum_le`, `Sensitivity10007Labeling.ZL.second_moment_all`, `Sensitivity10007Labeling.ZL.orientationWeight_nonneg`, `Sensitivity10007Labeling.ZL.tangent_ordinary_product`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; LabelMarked.lean, lines 1–1056.

import Definitions.Def_Sensitivity213981Formal_LabelOrdinary
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


/- Source: Sol_Paley11987Verified_CompactLabeling_markedFamily_load_le.lean -/
set_option autoImplicit false
set_option Elab.async false
section z0

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]









theorem incidence_swap (R : V → V → Prop) (S T : Finset V) :
    ∑ x ∈ S, (outOn R T x).card = ∑ y ∈ T, (inOn R S y).card := by
  simp only [outOn, inOn, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem first_moment_all (R : V → V → Prop) (D : ℕ)
    (hin : ∀ y, (inOn R Finset.univ y).card = D) (M : Finset V) :
    ∑ x : V, (outOn R M x).card = M.card * D := by
  rw [incidence_swap]
  simp_rw [hin]
  simp

theorem first_moment_external (R : V → V → Prop) (D : ℕ)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (hin : ∀ y, (inOn R Finset.univ y).card = D) (M : Finset V) :
    (∑ x ∈ Mᶜ, (outOn R M x).card) + M.card.choose 2 = M.card * D := by
  rw [← ordinary_degree_sum R hloop htour M]
  rw [Finset.sum_compl_add_sum]
  exact first_moment_all R D hin M

theorem powersetCard_outOn (R : V → V → Prop) (M : Finset V) (x : V) (k : ℕ) :
    (outOn R M x).powersetCard k =
      (M.powersetCard k).filter fun P => ∀ y ∈ P, R x y := by
  ext P
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hsub,hcard⟩
    exact ⟨⟨fun y hy => (Finset.mem_filter.mp (hsub hy)).1,hcard⟩,
      fun y hy => (Finset.mem_filter.mp (hsub hy)).2⟩
  · rintro ⟨⟨hsub,hcard⟩,hall⟩
    exact ⟨fun y hy => Finset.mem_filter.mpr ⟨hsub hy,hall y hy⟩,hcard⟩

theorem second_moment_all (R : V → V → Prop) (c : ℕ)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R z x ∧ R z y).card = c)
    (M : Finset V) :
    ∑ x : V, ((outOn R M x).card.choose 2) = M.card.choose 2 * c := by
  have hpair (P : Finset V) (hP : P ∈ M.powersetCard 2) :
      (Finset.univ.filter fun z => ∀ y ∈ P, R z y).card = c := by
    have hcard := (Finset.mem_powersetCard.mp hP).2
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hcard
    simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
      forall_eq] using hcommon x y hxy
  calc
    ∑ x : V, ((outOn R M x).card.choose 2) =
        ∑ x : V, ((M.powersetCard 2).filter fun P => ∀ y ∈ P, R x y).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.card_powersetCard, powersetCard_outOn]
    _ = ∑ P ∈ M.powersetCard 2,
        (Finset.univ.filter fun z => ∀ y ∈ P, R z y).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ = ∑ _P ∈ M.powersetCard 2, c := Finset.sum_congr rfl hpair
    _ = M.card.choose 2 * c := by simp











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





end SupportedFamily

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

open RowCounting



end
end ZL
end
end z9

section z10

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [DecidableEq V]





theorem weightedSubsets_insert (S : Finset V) (w : V → ℚ) (x : V)
    (hx : x ∉ S) (a : ℕ) :
    weightedSubsets (insert x S) w (a+1) =
      weightedSubsets S w (a+1) + w x * weightedSubsets S w a := by
  have hnot (A : Finset V) (hA : A ∈ S.powersetCard a) : x ∉ A :=
    fun h => hx ((Finset.mem_powersetCard.mp hA).1 h)
  have hdis : Disjoint (S.powersetCard (a+1))
      ((S.powersetCard a).image (insert x)) := by
    apply Finset.disjoint_left.mpr
    intro A hA hB
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hB
    exact hx ((Finset.mem_powersetCard.mp hA).1 (Finset.mem_insert_self x B))
  have hinj : Set.InjOn (fun A : Finset V => insert x A) (S.powersetCard a : Set (Finset V)) := by
    intro A hA B hB he
    have herase := congrArg (fun C : Finset V => C.erase x) he
    simpa only [Finset.erase_insert (hnot A hA),Finset.erase_insert (hnot B hB)] using herase
  unfold weightedSubsets
  rw [Finset.powersetCard_succ_insert hx, Finset.sum_union hdis, Finset.sum_image hinj]
  congr 1
  calc
    ∑ A ∈ S.powersetCard a, ∏ y ∈ insert x A, w y =
        ∑ A ∈ S.powersetCard a, w x * ∏ y ∈ A, w y :=
      Finset.sum_congr rfl fun A hA => Finset.prod_insert (hnot A hA)
    _ = w x * ∑ A ∈ S.powersetCard a, ∏ y ∈ A, w y := (Finset.mul_sum ..).symm

theorem factorial_mul_weightedSubsets_le (S : Finset V) (w : V → ℚ)
    (hw : ∀ x, 0 ≤  w x) : ∀ a : ℕ,
    (a.factorial : ℚ) * weightedSubsets S w a ≤  (∑ x ∈ S, w x)^a := by
  induction S using Finset.induction_on with
  | empty =>
    intro a
    cases a with
    | zero => simp [weightedSubsets]
    | succ a =>
      have he : (∅ : Finset V).powersetCard (a+1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [weightedSubsets, he]
  | @insert x S hx ih =>
    intro a
    cases a with
    | zero => simp [weightedSubsets]
    | succ a =>
      have hsum : (0 : ℚ) ≤  ∑ y ∈ S, w y := Finset.sum_nonneg fun y _ => hw y
      have hfirst := ih (a+1)
      have hsecond := mul_le_mul_of_nonneg_left (ih a)
        (mul_nonneg (Nat.cast_nonneg (a+1)) (hw x))
      have hpower := pow_add_mul_le_add_pow hsum
        (add_nonneg (mul_nonneg (by norm_num) hsum) (hw x)) (a+1)
      rw [weightedSubsets_insert S w x hx, Finset.sum_insert hx]
      calc
        ((a+1).factorial : ℚ) *
            (weightedSubsets S w (a+1) + w x * weightedSubsets S w a) =
            ((a+1).factorial : ℚ) * weightedSubsets S w (a+1) +
              (a+1 : ℕ) * w x * ((a.factorial : ℚ) * weightedSubsets S w a) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        _ ≤  (∑ y ∈ S, w y)^(a+1) +
              (a+1 : ℕ) * w x * (∑ y ∈ S, w y)^a := add_le_add hfirst hsecond
        _ ≤  (w x + ∑ y ∈ S, w y)^(a+1) := by
          simpa only [Nat.add_sub_cancel, add_comm, mul_comm, mul_left_comm,
            mul_assoc] using hpower

theorem weightedSubsets_le (S : Finset V) (w : V → ℚ)
    (hw : ∀ x, 0 ≤  w x) (a : ℕ) (W : ℚ) (hW : ∑ x ∈ S, w x ≤  W) :
    weightedSubsets S w a ≤  W^a / a.factorial := by
  have hfac : (0 : ℚ) <  a.factorial := by exact_mod_cast Nat.factorial_pos a
  apply (le_div_iff₀ hfac).mpr
  have hpow : (∑ x ∈ S, w x)^a ≤  W^a :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun x _ => hw x) hW a
  simpa only [mul_comm] using (factorial_mul_weightedSubsets_le S w hw a).trans hpow

theorem quadratic_weight_sum_le (S : Finset V) (f : V → ℕ)
    (w : ℕ → ℚ) (α β γ W₁ W₂ : ℚ)
    (hw : ∀ x ∈ S, w (f x) ≤  α + β * f x + γ * (f x).choose 2)
    (hγ : 0 ≤  γ) (h₁ : ∑ x ∈ S, (f x : ℚ) = W₁)
    (h₂ : ∑ x ∈ S, ((f x).choose 2 : ℚ) ≤  W₂) :
    ∑ x ∈ S, w (f x) ≤  α * S.card + β * W₁ + γ * W₂ := by
  calc
    ∑ x ∈ S, w (f x) ≤  ∑ x ∈ S, (α + β * f x + γ * (f x).choose 2) :=
      Finset.sum_le_sum hw
    _ = α * S.card + β * W₁ + γ * (∑ x ∈ S, ((f x).choose 2 : ℚ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, h₁]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤  α * S.card + β * W₁ + γ * W₂ := by
      have h := mul_le_mul_of_nonneg_left h₂ hγ
      linarith

end
end ZL
end
end z10

section z11

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)



theorem markedRows_union (A M : Finset V) :
    rowUnion (markedRows R A M) = markedSupport R A M := by
  ext e
  simp only [rowUnion,Finset.mem_biUnion,Finset.mem_univ,true_and,
    markedSupport,Finset.mem_union,internalEdges,crossEdges,Finset.mem_filter,
    Finset.mem_product]
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | inl i =>
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
      subst e
      exact Or.inl ⟨⟨i.property,(Finset.mem_filter.mp hj).1⟩,(Finset.mem_filter.mp hj).2⟩
    | inr i =>
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
      subst e
      exact Or.inr ⟨⟨i.property,(Finset.mem_filter.mp hj).1⟩,(Finset.mem_filter.mp hj).2⟩
  · rintro (⟨⟨hi,hj⟩,hij⟩ | ⟨⟨hi,hj⟩,hij⟩)
    · refine ⟨Sum.inl ⟨e.1,hi⟩,?_⟩
      exact Finset.mem_image.mpr ⟨e.2,Finset.mem_filter.mpr ⟨hj,hij⟩,rfl⟩
    · refine ⟨Sum.inr ⟨e.1,hi⟩,?_⟩
      exact Finset.mem_image.mpr ⟨e.2,Finset.mem_filter.mpr ⟨hj,hij⟩,rfl⟩



theorem markedGood_row_bound (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) (color : V → Fin 2)
    (h : MarkedGood R ell A M P q B color) (i : A ⊕ M) :
    (((markedRows R A M i).filter (fun e => ell e ≠ color e.2)).card) ≤ 
      markedRowBudget R A M P q B i := by
  cases i with
  | inl i =>
    rw [markedRows,Sum.elim_inl,outgoingRow_filter_card]
    change (mismatch R ell A color i.val).card ≤  q - (outOn R M i.val).card
    exact Nat.le_sub_of_add_le (h.1 i.val i.property)
  | inr i =>
    rw [markedRows,Sum.elim_inr,outgoingRow_filter_card]
    change (mismatch R ell A color i.val).card ≤ 
      if B=0 then 0 else q+1
    by_cases hB : B=0
    · rw [if_pos hB]
      have hs : (mismatch R ell A color i.val).card ≤ 
          ∑ y ∈ M, (mismatch R ell A color y).card :=
        Finset.single_le_sum (f := fun y => (mismatch R ell A color y).card)
          (fun _ _ => Nat.zero_le _) i.property
      exact hs.trans (hB ▸ h.2.2)
    · rw [if_neg hB]
      have hh := h.2.1 i.val i.property
      split_ifs at hh <;> omega



theorem markedAssignments_count (A M P : Finset V) (q B : ℕ) :
    (markedAssignments R A M P q B).card ≤ 
      2 ^ A.card *
        (∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
          (markedRows R A M i).card) *
        2 ^ (Fintype.card (V × V) - (markedSupport R A M).card) := by
  let encoded : Finset ((V × V) → Fin 2) :=
    Finset.univ.biUnion fun c : A → Fin 2 =>
      rowGood (markedRows R A M) (markedRowBudget R A M P q B) (headColor A c)
  have hsub : markedAssignments R A M P q B ⊆ encoded := by
    intro ell hell
    obtain ⟨c,hc⟩ := (Finset.mem_filter.mp hell).2
    apply Finset.mem_biUnion.mpr
    refine ⟨(fun x => c x.val),Finset.mem_univ _,?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i
    have hh := markedGood_row_bound R ell A M P q B c hc i
    convert hh using 1
    congr 1
    apply Finset.filter_congr
    intro e he
    have hey : e.2 ∈ A := by
      cases i with
      | inl i =>
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
        exact (Finset.mem_filter.mp hj).1
      | inr i =>
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
        exact (Finset.mem_filter.mp hj).1
    simp only [headColor,dif_pos hey]
  have hg (c : A → Fin 2) :
      (rowGood (markedRows R A M) (markedRowBudget R A M P q B) (headColor A c)).card ≤ 
        2 ^ (Fintype.card (V × V) - (markedSupport R A M).card) *
          ∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
            (markedRows R A M i).card := by
    simpa only [markedRows_union] using rowGood_card_le
      (markedRows R A M) (markedRowBudget R A M P q B) (headColor A c)
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_biUnion_le.trans
  calc
    (∑ c : A → Fin 2,
      (rowGood (markedRows R A M) (markedRowBudget R A M P q B) (headColor A c)).card) ≤ 
      ∑ _c : A → Fin 2, 2 ^ (Fintype.card (V × V) - (markedSupport R A M).card) *
        ∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
          (markedRows R A M i).card := Finset.sum_le_sum fun c _ => hg c
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_coe,
        Fintype.card_fin,Nat.nsmul_eq_mul]
      ring

theorem crossEdges_card (A M : Finset V) :
    (crossEdges R M A).card = ∑ x ∈ A, (inOn R M x).card := by
  calc
    (crossEdges R M A).card = ∑ y ∈ M, (outOn R A y).card := by
      simp only [crossEdges,outOn,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
    _ = _ := incidence_swap R M A

theorem markedSupport_card_add
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M : Finset V) (hdis : Disjoint A M) :
    (markedSupport R A M).card + ∑ x ∈ A, (outOn R M x).card =
      A.card.choose 2 + M.card * A.card := by
  have hedge : Disjoint (internalEdges R A) (crossEdges R M A) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
      (Finset.mem_product.mp (Finset.mem_filter.mp hf).1).1
  have hsum (x : V) (hx : x ∈ A) :
      (inOn R M x).card + (outOn R M x).card = M.card := by
    have hn : x ∉ M := Finset.disjoint_left.mp hdis hx
    have hd : Disjoint (inOn R M x) (outOn R M x) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      have hne : x ≠ y := fun he => hn (he ▸ (Finset.mem_filter.mp hy).1)
      exact (htour y x hne.symm).mp (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2
    have hu : inOn R M x ∪ outOn R M x = M := by
      ext y
      simp only [Finset.mem_union,inOn,outOn,Finset.mem_filter]
      constructor
      · tauto
      · intro hy
        have hne : x ≠ y := fun he => hn (he ▸ hy)
        by_cases h : R x y
        · exact Or.inr ⟨hy,h⟩
        · exact Or.inl ⟨hy,(htour y x hne.symm).mpr h⟩
    rw [← Finset.card_union_of_disjoint hd,hu]
  rw [markedSupport,Finset.card_union_of_disjoint hedge,_root_.Sensitivity213981Formal.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges R hloop htour,
    crossEdges_card,add_assoc,← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl hsum]
  simp only [Finset.sum_const,Nat.nsmul_eq_mul]
  ring

end
end ZL
end
end z11

section z13

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]



theorem marked_localProbability_le (F : SupportedFamily (V × V) D) (d : D)
    (R : V → V → Prop) (A M P : Finset V) (q B : ℕ)
    (hs : F.support d = markedSupport R A M)
    (hb : ∀ ell, F.bad d ell ↔ MarkedBad R ell A M P q B) :
    F.localProbability d ≤ 
      ((2 ^ A.card * ∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
          (markedRows R A M i).card : ℕ) : ℚ) /
        2 ^ (markedSupport R A M).card := by
  rw [← hs]
  apply F.localProbability_le_of_global
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hb),hs]
  simpa only [Fintype.card_subtype,markedAssignments] using markedAssignments_count R A M P q B



theorem rowPatterns_zero (d : ℕ) : rowPatterns 0 d = 1 := by
  simp [rowPatterns]

theorem rowPatterns_mono_degree (q d e : ℕ) (h : d ≤  e) :
    rowPatterns q d ≤  rowPatterns q e :=
  Finset.sum_le_sum fun i _ => Nat.choose_le_choose i.val h



theorem marked_pattern_product_le (R : V → V → Prop)
    (A M P : Finset V) (q B : ℕ) :
    (∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
      (markedRows R A M i).card) ≤ 
      (∏ x : A, rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card) *
        headErrorFactor q A.card M.card B := by
  rw [Fintype.prod_sum_type]
  simp only [markedRowBudget,markedRows,Sum.elim_inl,Sum.elim_inr,outgoingRow_card]
  apply Nat.mul_le_mul_left
  by_cases hB : B=0
  · simp only [headErrorFactor,if_pos hB,rowPatterns_zero,Finset.prod_const_one,le_refl]
  · simp only [headErrorFactor,if_neg hB]
    calc
      (∏ y : M, rowPatterns (q+1) (outOn R A y.val).card) ≤ 
          ∏ _y : M, rowPatterns (q+1) A.card :=
        Finset.prod_le_prod' fun y _ => rowPatterns_mono_degree _ _ _
          (Finset.card_le_card (Finset.filter_subset _ _))
      _ = (rowPatterns (q+1) A.card)^M.card := by simp

end
end ZL
end
end z13

section z14

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem orientation_weight_sum_le (R : V → V → Prop) (D c : ℕ)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (hin : ∀ y, (inOn R Finset.univ y).card = D)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R z x ∧ R z y).card = c)
    (M : Finset V) (w : ℕ → ℚ) (α β γ : ℚ)
    (hγ : 0 ≤  γ)
    (hpoly : ∀ f ≤  M.card, w f ≤  α + β * f + γ * f.choose 2) :
    ∑ x ∈ Mᶜ, w (outOn R M x).card ≤ 
      α * (Fintype.card V - M.card) +
      β * ((M.card : ℚ) * D - M.card.choose 2) +
      γ * (M.card.choose 2 : ℚ) * c := by
  have h₁nat := first_moment_external R D hloop htour hin M
  have h₁ : ∑ x ∈ Mᶜ, ((outOn R M x).card : ℚ) =
      (M.card : ℚ) * D - M.card.choose 2 := by
    have hh : (∑ x ∈ Mᶜ, ((outOn R M x).card : ℚ)) + M.card.choose 2 =
        (M.card : ℚ) * D := by exact_mod_cast h₁nat
    linarith
  have h₂nat : ∑ x ∈ Mᶜ, (outOn R M x).card.choose 2 ≤  M.card.choose 2 * c := by
    have hs := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Mᶜ)
      (fun x _ _ => Nat.zero_le ((outOn R M x).card.choose 2))
    exact hs.trans_eq (second_moment_all R c hcommon M)
  have h₂ : ∑ x ∈ Mᶜ, ((outOn R M x).card.choose 2 : ℚ) ≤ 
      (M.card.choose 2 : ℚ) * c := by exact_mod_cast h₂nat
  have hh := quadratic_weight_sum_le Mᶜ (fun x => (outOn R M x).card) w α β γ
    ((M.card : ℚ)*D-M.card.choose 2) ((M.card.choose 2 : ℚ)*c)
    (fun x _ => hpoly _ (Finset.card_le_card (Finset.filter_subset _ _))) hγ h₁ h₂
  simpa only [Finset.card_compl,Nat.cast_sub (Finset.card_le_univ M),mul_assoc] using hh

end
end ZL
end
end z14

section z15

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]



theorem orientationWeight_nonneg (q : ℕ) (C : ℕ → ℚ)
    (hC : ∀ t ≤  q, 0 ≤  C t) (f : ℕ) : 0 ≤  orientationWeight q C f := by
  unfold orientationWeight
  split_ifs with hf
  · exact mul_nonneg (by positivity) (hC _ (Nat.sub_le ..))
  · exact le_rfl

theorem tangent_ordinary_product (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M : Finset V) (q : ℕ) (u : ℚ) (C : ℕ → ℚ)
    (hu : 0 ≤  u) (hC : ∀ t ≤  q, 0 ≤  C t)
    (htan : ∀ d <  A.card, ∀ t ≤  q, (rowPatterns t d : ℚ) ≤  C t * u^d) :
    (∏ x : A, (rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card : ℚ)) ≤ 
      u^(A.card.choose 2) * ∏ x : A, C (q-(outOn R M x.val).card) := by
  have hsum : (∑ x : A, (outOn R A x.val).card) = A.card.choose 2 := by
    rw [Finset.sum_coe_sort (s := A) (f := fun x : V => (outOn R A x).card)]
    exact ordinary_degree_sum R hloop htour A
  calc
    (∏ x : A, (rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card : ℚ)) ≤ 
        ∏ x : A, C (q-(outOn R M x.val).card) * u^(outOn R A x.val).card :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun x _ =>
        htan _ (ordinary_row_degree_lt R hloop A x) _ (Nat.sub_le ..))
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hsum,mul_comm]

theorem orientationWeight_product (R : V → V → Prop)
    (A M : Finset V) (q : ℕ) (C : ℕ → ℚ)
    (hadm : ∀ x ∈ A, (outOn R M x).card ≤  q) :
    (∏ x : A, orientationWeight q C (outOn R M x.val).card) =
      (2 : ℚ)^(∑ x ∈ A, (outOn R M x).card) *
        ∏ x : A, C (q-(outOn R M x.val).card) := by
  simp only [orientationWeight,if_pos (hadm _ (Subtype.property _)),
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_coe_sort (s := A) (f := fun x : V => (outOn R M x).card)]

theorem SupportedFamily.localProbability_eq_zero_of_impossible
    (F : SupportedFamily (V × V) D) (d : D) (h : ∀ ell, ¬ F.bad d ell) :
    F.localProbability d = 0 := by
  letI : IsEmpty (F.LocalBad d) := ⟨fun u => h _ u.property⟩
  simp [SupportedFamily.localProbability]

theorem marked_localProbability_eq_zero_of_degree
    (F : SupportedFamily (V × V) D) (d : D)
    (R : V → V → Prop) (A M P : Finset V) (q B : ℕ)
    (hb : ∀ ell, F.bad d ell ↔ MarkedBad R ell A M P q B)
    (x : V) (hx : x ∈ A) (hq : q <  (outOn R M x).card) :
    F.localProbability d = 0 := by
  apply F.localProbability_eq_zero_of_impossible
  intro ell hell
  obtain ⟨color,hcolor⟩ := (hb ell).mp hell
  have hh := hcolor.1 x hx
  omega

theorem marked_localProbability_weighted_le
    (F : SupportedFamily (V × V) D) (d : D)
    (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M P : Finset V) (q B : ℕ) (hdis : Disjoint A M)
    (hs : F.support d = markedSupport R A M)
    (hb : ∀ ell, F.bad d ell ↔ MarkedBad R ell A M P q B)
    (u : ℚ) (C : ℕ → ℚ) (hu : 0 ≤  u) (hC : ∀ t ≤  q, 0 ≤  C t)
    (htan : ∀ k <  A.card, ∀ t ≤  q, (rowPatterns t k : ℚ) ≤  C t * u^k) :
    F.localProbability d ≤ 
      ((2 : ℚ)^A.card * headErrorFactor q A.card M.card B * u^(A.card.choose 2) /
        (2 : ℚ)^(A.card.choose 2 + M.card * A.card)) *
      ∏ x ∈ A, orientationWeight q C (outOn R M x).card := by
  by_cases hadm : ∀ x ∈ A, (outOn R M x).card ≤  q
  · let H : ℚ := ∏ x : A,
      (rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card : ℚ)
    let CP : ℚ := ∏ x : A, C (q-(outOn R M x.val).card)
    have hcount : F.localProbability d ≤ 
        (2 : ℚ)^A.card * (H * headErrorFactor q A.card M.card B) /
          (2 : ℚ)^(markedSupport R A M).card := by
      apply (marked_localProbability_le F d R A M P q B hs hb).trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := Nat.mul_le_mul_left (2^A.card) (marked_pattern_product_le R A M P q B)
      have hh' : ((2^A.card * ∏ i : A ⊕ M,
          rowPatterns (markedRowBudget R A M P q B i) (markedRows R A M i).card : ℕ) : ℚ) ≤ 
          ((2^A.card * ((∏ x : A, rowPatterns (q-(outOn R M x.val).card)
            (outOn R A x.val).card) * headErrorFactor q A.card M.card B) : ℕ) : ℚ) := by
        exact_mod_cast hh
      simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_prod,H] using hh'
    have htanprod : H ≤  u^(A.card.choose 2) * CP :=
      tangent_ordinary_product R hloop htour A M q u C hu hC htan
    have hprodw : (∏ x ∈ A, orientationWeight q C (outOn R M x).card) =
        (2 : ℚ)^(∑ x ∈ A, (outOn R M x).card) * CP := by
      have hp := orientationWeight_product R A M q C hadm
      rw [Finset.prod_coe_sort (s := A)
        (f := fun x : V => orientationWeight q C (outOn R M x).card)] at hp
      exact hp
    have hsupport := markedSupport_card_add R hloop htour A M hdis
    have hpow : (2 : ℚ)^(A.card.choose 2 + M.card*A.card) =
        (2 : ℚ)^(markedSupport R A M).card *
          (2 : ℚ)^(∑ x ∈ A, (outOn R M x).card) := by
      rw [← pow_add,hsupport]
    calc
      F.localProbability d ≤ 
          (2 : ℚ)^A.card * (H * headErrorFactor q A.card M.card B) /
            (2 : ℚ)^(markedSupport R A M).card := hcount
      _ ≤  (2 : ℚ)^A.card *
          ((u^(A.card.choose 2) * CP) * headErrorFactor q A.card M.card B) /
            (2 : ℚ)^(markedSupport R A M).card := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right htanprod (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by
        rw [hprodw,hpow]
        field_simp <;> ring
  · push_neg at hadm
    obtain ⟨x,hx,hq⟩ := hadm
    rw [marked_localProbability_eq_zero_of_degree F d R A M P q B hb x hx hq]
    apply mul_nonneg
    · positivity
    · exact Finset.prod_nonneg fun z _ => orientationWeight_nonneg q C hC _

end
end ZL
end
end z15

section z17

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
































theorem markedIndex_cardA (a m : ℕ) (I : MarkedIndex V a m) : I.2.val.card = a :=
  (Finset.mem_powersetCard.mp I.2.property).2

theorem markedIndex_cardM (a m : ℕ) (I : MarkedIndex V a m) : I.1.val.card = m :=
  (Finset.mem_powersetCard.mp I.1.property).2

theorem markedIndex_disjoint (a m : ℕ) (I : MarkedIndex V a m) :
    Disjoint I.2.val I.1.val := by
  apply Finset.disjoint_left.mpr
  intro x hx hm
  exact Finset.mem_compl.mp ((Finset.mem_powersetCard.mp I.2.property).1 hx) hm









end
end ZL
end
end z17

section z18

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [DecidableEq V]





end
end ZL
end
end z18

section z20

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]







end
end ZL
end
end z20

section z21

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V : Type*} [Fintype V] [DecidableEq V]







end
end ZL
end
end z21

end Sensitivity10007Labeling

end
end Sensitivity213981Formal


