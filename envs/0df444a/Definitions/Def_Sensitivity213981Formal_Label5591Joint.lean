-- Prove2me | Definitions.Def_Sensitivity213981Formal_Label5591Joint
-- name    : Sensitivity213981Formal_Label5591Joint
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:23:30.731488+00:00
-- url     : https://prove2.me/theorems/66fe6d09-b8b2-4c32-8b76-fdaa060e5aa7
-- title:
--   Label5591 Joint — sensitivity certificate definitions
-- statement:
--   The definitions for Label5591 Joint in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.Caps.family`, `Sensitivity5591Labeling.Caps.exponent`, `Sensitivity5591Labeling.Caps.lowerExponent`, `Sensitivity5591Labeling.Caps.ceiling`, `Sensitivity5591Labeling.Caps.JointExclusions`, `Sensitivity5591Labeling.Caps.family_support_bounds`, `Sensitivity5591Labeling.Caps.FamilyKind`, `Sensitivity5591Labeling.Caps.family_coordinate_load`, `Sensitivity5591Labeling.Caps.Description`, `Sensitivity5591Labeling.Caps.family_ceiling_sum`, `Sensitivity5591Labeling.Caps.exists_joint_exclusions`, `Sensitivity5591Labeling.Caps.descriptionFintype`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Label5591Joint.lean, lines 1–174.

import Definitions.Def_Sensitivity213981Formal_Label5591Loads
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_PerfectDominatorFamily
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
/- One label avoids all 24 exact bad-event families needed at order 5591. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Sensitivity5591Labeling.Caps
open Sensitivity10007Labeling ZL ZL.RowCounting
open scoped Classical BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev FamilyKind := Fin 9 ⊕ (Fin 12 ⊕ (Bool ⊕ Unit))

def Description (R : V → V → Prop) : FamilyKind → Type _
  | .inl q => OrdinaryIndex V (ordinaryA q)
  | .inr (.inl i) => MarkedIndex V (marked i).a (marked i).m
  | .inr (.inr (.inl false)) => SourceIndex R 19
  | .inr (.inr (.inl true)) => DominatorIndex R 17
  | .inr (.inr (.inr _)) => MarkedIndex V 15 3

instance descriptionFintype (R : V → V → Prop) (t : FamilyKind) : Fintype (Description R t) := by
  rcases t with q | i | b | u
  · exact ordinaryIndexFintype (ordinaryA q)
  · exact markedIndexFintype (marked i).a (marked i).m
  · cases b
    · exact sourceIndexFintype R 19
    · exact dominatorIndexFintype R 17
  · exact markedIndexFintype 15 3

def family (R : V → V → Prop) : (t : FamilyKind) → SupportedFamily (V × V) (Description R t)
  | .inl q => ordinaryFamily R q.val (ordinaryA q)
  | .inr (.inl i) => markedFamily R (marked i).q (marked i).a (marked i).m (marked i).B
  | .inr (.inr (.inl false)) => sourceFamily R 19
  | .inr (.inr (.inl true)) => dominatorFamily R 17
  | .inr (.inr (.inr _)) => ThreeBoundPerfectFamily.family R 15 3

def exponent : FamilyKind → ℕ
  | .inl q => (ordinaryA q).choose 2
  | .inr (.inl i) => (marked i).a.choose 2+(marked i).m*(marked i).a
  | .inr (.inr (.inl false)) => 190
  | .inr (.inr (.inl true)) => 170
  | .inr (.inr (.inr _)) => 150

def lowerExponent : FamilyKind → ℕ
  | .inl q => (ordinaryA q).choose 2
  | .inr (.inl i) => (marked i).a.choose 2
  | .inr (.inr (.inl false)) => 190
  | .inr (.inr (.inl true)) => 170
  | .inr (.inr (.inr _)) => 105

def ceiling : FamilyKind → ℚ
  | .inl q => ordinaryCeiling q
  | .inr (.inl i) => markedCeiling i
  | .inr (.inr (.inl false)) => sourceCeiling
  | .inr (.inr (.inl true)) => dominatorCeiling
  | .inr (.inr (.inr _)) => perfectCeiling

structure JointExclusions (R : V → V → Prop) (ell : V × V → Fin 2) : Prop where
  ordinary : ∀ (q : Fin 9) (I : OrdinaryIndex V (ordinaryA q)),
    ¬ (ordinaryFamily R q.val (ordinaryA q)).bad I ell
  marked : ∀ (i : Fin 12) (I : MarkedIndex V (marked i).a (marked i).m),
    ¬ (markedFamily R (marked i).q (marked i).a (marked i).m (marked i).B).bad I ell
  source : ∀ I : SourceIndex R 19, ¬ (sourceFamily R 19).bad I ell
  dominator : ∀ I : DominatorIndex R 17, ¬ (dominatorFamily R 17).bad I ell
  perfect : ∀ I : MarkedIndex V 15 3, ¬ (ThreeBoundPerfectFamily.family R 15 3).bad I ell

theorem family_support_bounds (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (t : FamilyKind) (d : Description R t) :
    0 <  lowerExponent t ∧ lowerExponent t ≤  ((family R t).support d).card ∧
      ((family R t).support d).card ≤  exponent t ∧ exponent t ≤  2*lowerExponent t := by
  rcases t with q | i | b | u
  · have hS := ordinaryFamily_support_bounds R hloop htour q.val (ordinaryA q) d
    exact ⟨Nat.choose_pos (elementary_ordinary q).1,hS.symm.le,hS.le,by dsimp [exponent,lowerExponent]; omega⟩
  · obtain ⟨_,hE,hM,_⟩ := marked_data i
    obtain ⟨hS,hS'⟩ := markedFamily_support_bounds R hloop htour
      (marked i).q (marked i).a (marked i).m (marked i).B d
    exact ⟨hE,hS,hS',hM⟩
  · cases b
    · have hS := sourceFamily_support_bounds R hloop htour 19 d
      have he : (19).choose 2+19 = 190 := by decide
      rw [he] at hS
      exact ⟨by decide,hS.symm.le,hS.le,by decide⟩
    · have hS := dominatorFamily_support_bounds R hloop htour 17 d
      have he : (17).choose 2+2*17 = 170 := by decide
      rw [he] at hS
      exact ⟨by decide,hS.symm.le,hS.le,by decide⟩
  · cases u
    have hS := markedFamily_support_bounds R hloop htour 0 15 3 0 d
    have hlo : (15).choose 2 = 105 := by decide
    have hhi : (15).choose 2+3*15 = 150 := by decide
    rw [hlo] at hS
    exact ⟨by decide,hS.1,hS.2,by decide⟩

theorem family_coordinate_load (R : V → V → Prop) (hn : Fintype.card V = N)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (hout : ∀ x, (outOn R Finset.univ x).card = degree)
    (hin : ∀ x, (inOn R Finset.univ x).card = degree)
    (hcommonIn : ∀ x y, x ≠ y → (Finset.univ.filter fun z => R z x ∧ R z y).card = common)
    (hcommonOut : ∀ x y, x ≠ y → (Finset.univ.filter fun z => R x z ∧ R y z).card = common)
    (htrans : ∀ x y u v, R x y → R u v →
      ∃ e : V ≃ V, e x = u ∧ e y = v ∧ ∀ a b, R (e a) (e b) ↔ R a b)
    (htriple : ∀ M : Finset V, M.card = 3 → (dominatedBy R M).card ≤  800)
    (t : FamilyKind) (e : V × V) :
    (∑ d ∈ Finset.univ.filter (fun d => e ∈ (family R t).support d),
      (family R t).localProbability d * lam^exponent t)/2 ≤  ceiling t := by
  have hlam : 0 ≤  lam := le_trans (by norm_num) basic_constants.2.2.2.1.le
  rcases t with q | i | b | u
  · exact ordinary_coordinate_load R hn hloop htour q e
  · exact marked_coordinate_load R hn hloop htour hin hcommonIn htrans i e
  · cases b
    · have h := sourceFamily_load_le R hloop htour degree common 19 (by decide)
        hout hcommonIn lam hlam e
      have he : (19).choose 2+19 = 190 := by decide
      rw [he] at h
      have hh : (∑ I ∈ Finset.univ.filter (fun I => e ∈ (sourceFamily R 19).support I),
          (sourceFamily R 19).localProbability I * lam^190)/2 ≤  sourceLoad := by
        simpa only [sourceLoad,Nat.cast_add,Nat.cast_mul] using h
      exact hh.trans source_load
    · have h := dominatorFamily_load_le R hloop htour degree common 17 (by decide)
        hin hcommonIn hcommonOut lam hlam e
      have he : (17).choose 2+2*17 = 170 := by decide
      rw [he] at h
      have hh : (∑ I ∈ Finset.univ.filter (fun I => e ∈ (dominatorFamily R 17).support I),
          (dominatorFamily R 17).localProbability I * lam^170)/2 ≤  dominatorLoad := by
        simpa only [dominatorLoad,Nat.cast_add,Nat.cast_mul] using h
      exact hh.trans dominator_load
  · have h := ThreeBoundPerfectFamily.coordinate_load R hloop htour htrans 15 3 800
      htriple lam hlam e
    have he : (15).choose 2+3*15 = 150 := by decide
    rw [he,hn] at h
    exact h.trans perfect_load

theorem family_ceiling_sum : ∑ t : FamilyKind, ceiling t ≤  1-1/lam := by
  have h := total_load
  simpa only [Fintype.sum_sum_type,Fintype.sum_bool,Fintype.sum_unique,ceiling] using
    (show (∑ q : Fin 9, ordinaryCeiling q)+((∑ i : Fin 12, markedCeiling i)+
      ((dominatorCeiling+sourceCeiling)+perfectCeiling)) ≤  1-1/lam by linarith)

theorem exists_joint_exclusions (R : V → V → Prop) (hn : Fintype.card V = N)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (hout : ∀ x, (outOn R Finset.univ x).card = degree)
    (hin : ∀ x, (inOn R Finset.univ x).card = degree)
    (hcommonIn : ∀ x y, x ≠ y → (Finset.univ.filter fun z => R z x ∧ R z y).card = common)
    (hcommonOut : ∀ x y, x ≠ y → (Finset.univ.filter fun z => R x z ∧ R y z).card = common)
    (htrans : ∀ x y u v, R x y → R u v →
      ∃ e : V ≃ V, e x = u ∧ e y = v ∧ ∀ a b, R (e a) (e b) ↔ R a b)
    (htriple : ∀ M : Finset V, M.card = 3 → (dominatedBy R M).card ≤  800) :
    ∃ ell : V × V → Fin 2, JointExclusions R ell := by
  have hb := family_support_bounds R hloop htour
  obtain ⟨ell,hell⟩ := SupportedFamily.exists_avoiding_families
    (family R) exponent ceiling lam basic_constants.2.2.2.1
    (fun t d => Finset.card_pos.mp (lt_of_lt_of_le (hb t d).1 (hb t d).2.1))
    (fun t d => (hb t d).2.2.1)
    (fun t d => activity_small_of_support (lowerExponent t) _ (exponent t) lam
      (hb t d).1 (hb t d).2.1 (hb t d).2.2.2
      basic_constants.2.2.2.1.le basic_constants.2.2.2.2)
    (family_coordinate_load R hn hloop htour hout hin hcommonIn hcommonOut htrans htriple)
    family_ceiling_sum
  exact ⟨ell,⟨(fun q d => hell (.inl q) d),
    (fun i d => hell (.inr (.inl i)) d),
    (fun d => hell (.inr (.inr (.inl false))) d),
    (fun d => hell (.inr (.inr (.inl true))) d),
    (fun d => hell (.inr (.inr (.inr ()))) d)⟩⟩

end
end Sensitivity5591Labeling.Caps



end
end Sensitivity213981Formal


