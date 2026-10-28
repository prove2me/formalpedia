-- Prove2me | Definitions.Def_Sensitivity213981Formal_LabelExists
-- name    : Sensitivity213981Formal_LabelExists
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:46:32.324315+00:00
-- url     : https://prove2.me/theorems/9c7857ea-bb1c-4e5c-bcf3-610baf104a3a
-- title:
--   Label Exists — sensitivity certificate definitions
-- statement:
--   The definitions for Label Exists in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity10007Labeling.CompactAtomicLLL.conditional_probability_bound`, `Sensitivity10007Labeling.CompactAtomicLLL.exists_avoiding`, `Sensitivity10007Labeling.SensitivityLabelCache12607.SensitivityLLL.weighted_bernoulli_finset`, `Sensitivity10007Labeling.SensitivityLabelCache12607.SensitivityLLL.one_step_bound`, `Sensitivity10007Labeling.CompactAtomicLLL.product_lower_of_coordinate_load`, `Sensitivity10007Labeling.CompactAtomicLLL.exists_avoiding_of_coordinate_load`, `Sensitivity10007Labeling.ZL.SupportedFamily.complement_atom_support`, `Sensitivity10007Labeling.ZL.SupportedFamily.complement_atom_value`, `Sensitivity10007Labeling.ZL.SupportedFamily.avoids_all_iff`, `Sensitivity10007Labeling.ZL.SupportedFamily.coordinate_total`, `Sensitivity10007Labeling.ZL.SupportedFamily.coordinate_conflict_half`, `Sensitivity10007Labeling.ZL.SupportedFamily.exists_joint_avoidance`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; LabelExists.lean, lines 1–1009.

import Definitions.Def_Sensitivity213981Formal_LabelLoads
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


/- Source: Sol_Paley11987Verified_CompactLabeling11987_exists_joint_exclusions.lean -/
set_option autoImplicit false
set_option Elab.async false
section z2

section

namespace SensitivityLabelCache12607

set_option maxHeartbeats 8000000
open scoped BigOperators

namespace SensitivityLLL

variable {ι : Type*} [DecidableEq ι]

theorem product_step_bound (Z : Finset ι → ℚ) (w : ι → ℚ)
    (hw : ∀ i, 0 ≤  w i) (B A : Finset ι)
    (hstep : ∀ T ⊆ A, ∀ i ∈ A, i ∉ T →
      w i*Z (B ∪ T) ≤  Z (B ∪ insert i T)) :
    (∏ i ∈ A, w i)*Z B ≤  Z (B ∪ A) := by
  revert hstep
  induction A using Finset.induction_on with
  | empty => intro _; simp
  | @insert a A ha ih =>
    intro hstep
    have hchain : (∏ i ∈ A, w i)*Z B ≤  Z (B ∪ A) := by
      apply ih
      intro T hT i hi hnot
      exact hstep T (hT.trans (Finset.subset_insert _ _)) i
        (Finset.mem_insert_of_mem hi) hnot
    have hlast := hstep A (Finset.subset_insert _ _) a (Finset.mem_insert_self _ _) ha
    calc
      (∏ i ∈ insert a A, w i)*Z B = w a*((∏ i ∈ A, w i)*Z B) := by
        rw [Finset.prod_insert ha]
        ring
      _ ≤  w a*Z (B ∪ A) := mul_le_mul_of_nonneg_left hchain (hw a)
      _ ≤  Z (B ∪ insert a A) := hlast

theorem one_step_bound (Z : Finset ι → ℚ) (p x : ι → ℚ) (N : ι → Finset ι)
    (hZ : ∀ S, 0 ≤  Z S) (hx0 : ∀ i, 0 ≤  x i) (hx1 : ∀ i, x i <  1)
    (hp : ∀ i, p i ≤  x i*(∏ j ∈ N i, (1-x j)))
    (hLoss : ∀ S i, i ∉ S → Z S-Z (insert i S) ≤  p i*Z (S \ N i)) :
    ∀ S i, i ∉ S → (1-x i)*Z S ≤  Z (insert i S) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro i hi
    let A := S ∩ N i
    let B := S \ N i
    have hBA : B ∪ A = S := Finset.sdiff_union_inter S (N i)
    have hw0 (j : ι) : 0 ≤  1-x j := sub_nonneg.mpr (le_of_lt (hx1 j))
    have hchain : (∏ j ∈ A, (1-x j))*Z B ≤  Z S := by
      have hh := product_step_bound Z (fun j => 1-x j) hw0 B A (by
        intro T hT j hj hnot
        have hjS : j ∈ S := (Finset.mem_inter.mp hj).1
        have hjN : j ∈ N i := (Finset.mem_inter.mp hj).2
        have hnotB : j ∉ B := fun h => (Finset.mem_sdiff.mp h).2 hjN
        have hnotBT : j ∉ B ∪ T := by
          intro h
          exact (Finset.mem_union.mp h).elim hnotB hnot
        have hsub : B ∪ T ⊆ S := by
          apply Finset.union_subset
          · exact Finset.sdiff_subset
          · exact hT.trans Finset.inter_subset_left
        have hproper : B ∪ T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
          intro heq
          exact hnotBT (heq.symm ▸ hjS)⟩
        have hlocal := ih (B ∪ T) hproper j hnotBT
        simpa only [Finset.union_insert] using hlocal)
      simpa only [hBA] using hh
    have hprod : (∏ j ∈ N i, (1-x j)) ≤  ∏ j ∈ A, (1-x j) := by
      apply Finset.prod_le_prod_of_subset_of_le_one Finset.inter_subset_right
      · intro j _
        exact hw0 j
      · intro j _ _
        linarith [hx0 j]
    have hPi : p i ≤  x i*(∏ j ∈ A, (1-x j)) :=
      (hp i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
    have hbad : p i*Z B ≤  x i*Z S := by
      calc
        _ ≤  (x i*(∏ j ∈ A, (1-x j)))*Z B :=
          mul_le_mul_of_nonneg_right hPi (hZ B)
        _ = x i*((∏ j ∈ A, (1-x j))*Z B) := by ring
        _ ≤  x i*Z S := mul_le_mul_of_nonneg_left hchain (hx0 i)
    have hloss := hLoss S i hi
    change Z S-Z (insert i S) ≤  p i*Z B at hloss
    nlinarith

theorem positive_of_loss (Z : Finset ι → ℚ) (p x : ι → ℚ) (N : ι → Finset ι)
    (hZ : ∀ S, 0 ≤  Z S) (hEmpty : 0 <  Z ∅)
    (hx0 : ∀ i, 0 ≤  x i) (hx1 : ∀ i, x i <  1)
    (hp : ∀ i, p i ≤  x i*(∏ j ∈ N i, (1-x j)))
    (hLoss : ∀ S i, i ∉ S → Z S-Z (insert i S) ≤  p i*Z (S \ N i)) :
    ∀ S, 0 <  Z S := by
  intro S
  have hstep := one_step_bound Z p x N hZ hx0 hx1 hp hLoss
  have hchain : (∏ i ∈ S, (1-x i))*Z ∅ ≤  Z S := by
    have hh := product_step_bound Z (fun i => 1-x i)
      (fun i => sub_nonneg.mpr (le_of_lt (hx1 i))) ∅ S (by
        intro T _ i _ hnot
        simpa only [Finset.empty_union] using hstep T i hnot)
    simpa only [Finset.empty_union] using hh
  have hprod : 0 <  ∏ i ∈ S, (1-x i) :=
    Finset.prod_pos (fun i _ => sub_pos.mpr (hx1 i))
  exact (mul_pos hprod hEmpty).trans_le hchain

noncomputable section
open scoped Classical

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]



theorem mem_avoid (bad : ι → Finset Ω) (S : Finset ι) (ω : Ω) :
    ω ∈ avoid bad S ↔ ∀ i ∈ S, ω ∉ bad i := by
  simp only [avoid,Finset.mem_filter,Finset.mem_univ,true_and]

theorem avoid_empty (bad : ι → Finset Ω) : avoid bad ∅ = Finset.univ := by
  ext ω
  simp [avoid]

theorem avoid_insert (bad : ι → Finset Ω) (S : Finset ι) (i : ι) :
    avoid bad (insert i S) = avoid bad S \ bad i := by
  ext ω
  simp [avoid,and_comm,and_left_comm,and_assoc]

theorem avoid_antitone (bad : ι → Finset Ω) {S T : Finset ι} (hST : S ⊆ T) :
    avoid bad T ⊆ avoid bad S := by
  intro ω hω
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro i hi
  exact (Finset.mem_filter.mp hω).2 i (hST hi)

theorem loss_of_nonneighbor_count (bad : ι → Finset Ω) (p : ι → ℚ)
    (N : ι → Finset ι)
    (hAway : ∀ i S, i ∉ S → (∀ j ∈ S, j ∉ N i) →
      ((bad i ∩ avoid bad S).card : ℚ) ≤  p i*((avoid bad S).card : ℚ)) :
    ∀ S i, i ∉ S →
      ((avoid bad S).card : ℚ)-((avoid bad (insert i S)).card : ℚ) ≤ 
        p i*((avoid bad (S \ N i)).card : ℚ) := by
  intro S i hi
  have hNat := Finset.card_sdiff_add_card_inter (avoid bad S) (bad i)
  have hRat : (((avoid bad S \ bad i).card : ℚ)) +
      (((avoid bad S ∩ bad i).card : ℚ)) = ((avoid bad S).card : ℚ) := by
    exact_mod_cast hNat
  have hLossEq : ((avoid bad S).card : ℚ)-((avoid bad (insert i S)).card : ℚ) =
      ((bad i ∩ avoid bad S).card : ℚ) := by
    rw [Finset.inter_comm] at hRat
    rw [avoid_insert]
    linarith
  rw [hLossEq]
  have hsub : bad i ∩ avoid bad S ⊆ bad i ∩ avoid bad (S \ N i) := by
    intro ω hω
    obtain ⟨hbad,hgood⟩ := Finset.mem_inter.mp hω
    exact Finset.mem_inter.mpr ⟨hbad,avoid_antitone bad Finset.sdiff_subset hgood⟩
  have hCard : ((bad i ∩ avoid bad S).card : ℚ) ≤ 
      ((bad i ∩ avoid bad (S \ N i)).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  apply hCard.trans
  apply hAway i (S \ N i)
  · exact fun h => hi (Finset.mem_sdiff.mp h).1
  · intro j hj
    exact (Finset.mem_sdiff.mp hj).2

theorem asymmetric_local_lemma [Fintype ι] [Nonempty Ω]
    (bad : ι → Finset Ω) (p x : ι → ℚ) (N : ι → Finset ι)
    (hx0 : ∀ i, 0 ≤  x i) (hx1 : ∀ i, x i <  1)
    (hp : ∀ i, p i ≤  x i*(∏ j ∈ N i, (1-x j)))
    (hAway : ∀ i S, i ∉ S → (∀ j ∈ S, j ∉ N i) →
      ((bad i ∩ avoid bad S).card : ℚ) ≤  p i*((avoid bad S).card : ℚ)) :
    ∃ ω, ∀ i, ω ∉ bad i := by
  let Z : Finset ι → ℚ := fun S => ((avoid bad S).card : ℚ)
  have hZ : ∀ S, 0 ≤  Z S := fun S => Nat.cast_nonneg _
  have hEmpty : 0 <  Z ∅ := by
    have hΩ : 0 <  Fintype.card Ω := Fintype.card_pos_iff.mpr inferInstance
    have hh : (0 : ℚ) <  (Fintype.card Ω : ℚ) := by exact_mod_cast hΩ
    simpa only [Z,avoid_empty,Finset.card_univ] using hh
  have hpositive := positive_of_loss Z p x N hZ hEmpty hx0 hx1 hp
    (loss_of_nonneighbor_count bad p N hAway)
  have hNat : 0 <  (avoid bad Finset.univ).card := by
    have hh : (0 : ℚ) <  ((avoid bad Finset.univ).card : ℚ) := hpositive Finset.univ
    exact_mod_cast hh
  obtain ⟨ω,hω⟩ := Finset.card_pos.mp hNat
  refine ⟨ω,?_⟩
  intro i
  exact (mem_avoid bad Finset.univ ω).mp hω i (Finset.mem_univ _)

end
end SensitivityLLL

end SensitivityLabelCache12607
end
end z2

section z3

section

set_option maxHeartbeats 4000000
open scoped Classical BigOperators

namespace CompactAtomicLLL

noncomputable section

open SensitivityLabelCache12607.SensitivityLLL

variable {V E : Type*} [Fintype V] [DecidableEq V]







theorem mem_event (a : Atom V) (x : V → Fin 2) :
    x ∈ event a ↔ Holds a x := by
  simp only [event, Finset.mem_filter, Finset.mem_univ, true_and]





theorem overwrite_preserves_avoidance (a b : Atom V) (x : V → Fin 2)
    (hx : Holds a x) (hcompat : ¬ Conflict a b) (hb : ¬ Holds b x)
    (u : a.support → Fin 2) : ¬ Holds b (overwrite a x u) := by
  intro hnew
  apply hb
  intro v hv
  by_cases ha : v ∈ a.support
  · have he : a.value v = b.value v := by
      by_contra hne
      exact hcompat ⟨v, ha, hv, hne⟩
    exact (hx v ha).trans he
  · simpa only [overwrite, dif_neg ha] using hnew v hv

theorem conditional_count [DecidableEq E]
    (a : Atom V) (atoms : E → Atom V) (S : Finset E)
    (hcompat : ∀ j ∈ S, ¬ Conflict a (atoms j)) :
    (event a ∩ avoid (fun j => event (atoms j)) S).card * 2 ^ a.support.card ≤ 
      (avoid (fun j => event (atoms j)) S).card := by
  let A := event a ∩ avoid (fun j => event (atoms j)) S
  let B := avoid (fun j => event (atoms j)) S
  let encode : A × (a.support → Fin 2) → B := fun p =>
    ⟨overwrite a p.1.val p.2, by
      have hA : Holds a p.1.val :=
        (mem_event a p.1.val).mp (Finset.mem_inter.mp p.1.property).1
      have hB := (mem_avoid (fun j => event (atoms j)) S p.1.val).mp
        (Finset.mem_inter.mp p.1.property).2
      apply (mem_avoid (fun j => event (atoms j)) S _).mpr
      intro j hj hnew
      exact overwrite_preserves_avoidance a (atoms j) p.1.val hA (hcompat j hj)
        (fun h => hB j hj ((mem_event (atoms j) p.1.val).mpr h)) p.2
        ((mem_event (atoms j) _).mp hnew)⟩
  have hinj : Function.Injective encode := by
    intro p q heq
    have hout : overwrite a p.1.val p.2 = overwrite a q.1.val q.2 :=
      congrArg Subtype.val heq
    have hp : Holds a p.1.val :=
      (mem_event a p.1.val).mp (Finset.mem_inter.mp p.1.property).1
    have hq : Holds a q.1.val :=
      (mem_event a q.1.val).mp (Finset.mem_inter.mp q.1.property).1
    apply Prod.ext
    · apply Subtype.ext
      funext v
      by_cases hv : v ∈ a.support
      · exact (hp v hv).trans (hq v hv).symm
      · simpa only [overwrite, dif_neg hv] using congrFun hout v
    · funext v
      simpa only [overwrite, dif_pos v.property] using congrFun hout v.val
  have hc := Fintype.card_le_of_injective encode hinj
  simpa only [A, B, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_fun, Fintype.card_fin] using hc

theorem conditional_probability_bound [DecidableEq E]
    (a : Atom V) (atoms : E → Atom V) (S : Finset E)
    (hcompat : ∀ j ∈ S, ¬ Conflict a (atoms j)) :
    ((event a ∩ avoid (fun j => event (atoms j)) S).card : ℚ) ≤ 
      (1 / (2 : ℚ) ^ a.support.card) *
        ((avoid (fun j => event (atoms j)) S).card : ℚ) := by
  have hc : ((event a ∩ avoid (fun j => event (atoms j)) S).card : ℚ) *
      (2 : ℚ) ^ a.support.card ≤ 
        ((avoid (fun j => event (atoms j)) S).card : ℚ) := by
    exact_mod_cast conditional_count a atoms S hcompat
  have hden : (0 : ℚ) <  (2 : ℚ) ^ a.support.card := by positivity
  calc
    ((event a ∩ avoid (fun j => event (atoms j)) S).card : ℚ) ≤ 
        ((avoid (fun j => event (atoms j)) S).card : ℚ) /
          (2 : ℚ) ^ a.support.card := (le_div_iff₀ hden).mpr hc
    _ = (1 / (2 : ℚ) ^ a.support.card) *
        ((avoid (fun j => event (atoms j)) S).card : ℚ) := by ring



theorem exists_avoiding [Fintype E] [DecidableEq E]
    (atoms : E → Atom V) (x : E → ℚ)
    (hx0 : ∀ i, 0 ≤  x i) (hx1 : ∀ i, x i <  1)
    (hproduct : ∀ i, (1 / (2 : ℚ) ^ (atoms i).support.card) ≤ 
      x i * ∏ j ∈ neighbors atoms i, (1 - x j)) :
    ∃ labeling : V → Fin 2, ∀ i, ¬ Holds (atoms i) labeling := by
  obtain ⟨labeling, hlabel⟩ := asymmetric_local_lemma
    (fun i => event (atoms i)) (fun i => 1 / (2 : ℚ) ^ (atoms i).support.card)
    x (neighbors atoms) hx0 hx1 hproduct (by
      intro i S hi haway
      apply conditional_probability_bound
      intro j hj hconflict
      exact haway j hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconflict⟩))
  refine ⟨labeling, ?_⟩
  intro i hi
  exact hlabel i ((mem_event (atoms i) labeling).mpr hi)

end

end CompactAtomicLLL
end
end z3

section z5

section

namespace SensitivityLabelCache12607

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

open scoped BigOperators

namespace SensitivityLLL
noncomputable section



theorem weighted_bernoulli_finset {Q : Type*} [DecidableEq Q]
    (S : Finset Q) (x : Q → ℚ) (C : Q → ℕ)
    (hx0 : ∀ q, 0 ≤  x q) (hx1 : ∀ q, x q ≤  1) :
    1 - ∑ q ∈ S, (C q : ℚ) * x q ≤  ∏ q ∈ S, (1 - x q) ^ C q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
    rw [Finset.sum_insert hq, Finset.prod_insert hq]
    have hf0 : (0 : ℚ) ≤  (1 - x q) ^ C q :=
      pow_nonneg (by linarith [hx1 q]) _
    have hf1 : (1 - x q) ^ C q ≤  (1 : ℚ) :=
      pow_le_one₀ (by linarith [hx1 q]) (by linarith [hx0 q])
    have hB : 1 - (C q : ℚ) * x q ≤  (1 - x q) ^ C q := by
      simpa only [mul_neg, sub_eq_add_neg] using
        (one_add_mul_le_pow (R := ℚ) (a := -x q) (by linarith [hx1 q]) (C q))
    have hsum0 : (0 : ℚ) ≤  ∑ j ∈ S, (C j : ℚ) * x j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hx0 j)
    have hmul := mul_le_mul_of_nonneg_left ih hf0
    nlinarith [mul_nonneg (sub_nonneg.mpr hf1) hsum0]







end
end SensitivityLLL

end SensitivityLabelCache12607
end
end z5

section z6

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace CompactAtomicLLL
noncomputable section

open SensitivityLabelCache12607.SensitivityLLL

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem product_lower_of_coordinate_load (atoms : E → Atom V) (i : E)
    (hne : (atoms i).support.Nonempty) (w : E → ℚ)
    (hw0 : ∀ j, 0 ≤  w j) (hw1 : ∀ j, w j ≤  1)
    (lam : ℚ) (hlam : 1 <  lam)
    (hload : ∀ v ∈ (atoms i).support,
      ∑ j ∈ conflictSlice (atoms i) atoms v, w j ≤  1 - 1 / lam) :
    (1 / lam) ^ (atoms i).support.card ≤ 
      ∏ j ∈ neighbors atoms i, (1 - w j) := by
  let S := (atoms i).support
  let N := neighbors atoms i
  obtain ⟨v₀,hv₀⟩ := hne
  have hwitness (j : E) (hj : j ∈ N) :
      ∃ v : S, v.val ∈ (atoms j).support ∧ (atoms i).value v.val ≠ (atoms j).value v.val := by
    obtain ⟨v,hvi,hvj,hne⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨⟨v,hvi⟩,hvj,hne⟩
  let kind : E → S := fun j =>
    if hj : j ∈ N then Classical.choose (hwitness j hj) else ⟨v₀,hv₀⟩
  have hkind (j : E) (hj : j ∈ N) :
      (kind j).val ∈ (atoms j).support ∧
        (atoms i).value (kind j).val ≠ (atoms j).value (kind j).val := by
    dsimp only [kind]
    rw [dif_pos hj]
    exact Classical.choose_spec (hwitness j hj)
  have hgroup (v : S) :
      (1 / lam : ℚ) ≤  ∏ j ∈ N.filter (fun j => kind j = v), (1 - w j) := by
    have hsub : N.filter (fun j => kind j = v) ⊆ conflictSlice (atoms i) atoms v.val := by
      intro j hj
      obtain ⟨hj,hkv⟩ := Finset.mem_filter.mp hj
      have hh := hkind j hj
      rw [hkv] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw0 j)
    have hbudget : ∑ j ∈ N.filter (fun j => kind j = v), w j ≤  1 - 1 / lam :=
      hs.trans (hload v.val v.property)
    have hB := weighted_bernoulli_finset (N.filter (fun j => kind j = v)) w
      (fun _ => 1) hw0 hw1
    simp only [Nat.cast_one, one_mul, pow_one] at hB
    linarith
  calc
    (1 / lam) ^ (atoms i).support.card = ∏ _v : S, (1 / lam : ℚ) := by simp [S]
    _ ≤  ∏ v : S, ∏ j ∈ N.filter (fun j => kind j = v), (1 - w j) :=
      Finset.prod_le_prod (fun _ _ => by positivity) (fun v _ => hgroup v)
    _ = ∏ j ∈ N, (1 - w j) := Finset.prod_fiberwise N kind (fun j => 1 - w j)

theorem exists_avoiding_of_coordinate_load (atoms : E → Atom V)
    (M : E → ℕ) (w : E → ℚ) (lam : ℚ) (hlam : 1 <  lam)
    (hne : ∀ i, (atoms i).support.Nonempty)
    (hM : ∀ i, (atoms i).support.card ≤  M i)
    (hw0 : ∀ i, 0 ≤  w i) (hw1 : ∀ i, w i <  1)
    (hactivity : ∀ i, w i = (1 / (2 : ℚ) ^ (atoms i).support.card) * lam ^ M i)
    (hload : ∀ i v, v ∈ (atoms i).support →
      ∑ j ∈ conflictSlice (atoms i) atoms v, w j ≤  1 - 1 / lam) :
    ∃ ell : V → Fin 2, ∀ i, ¬ Holds (atoms i) ell := by
  apply exists_avoiding atoms w hw0 hw1
  intro i
  have h0 : (0 : ℚ) <  lam := lt_trans zero_lt_one hlam
  have hprod := product_lower_of_coordinate_load atoms i (hne i) w hw0
    (fun j => (hw1 j).le) lam hlam (hload i)
  have hinv0 : (0 : ℚ) ≤  1 / lam := by positivity
  have hinv1 : (1 : ℚ) / lam ≤  1 := (div_le_one h0).mpr hlam.le
  have hpow : (1 / lam) ^ M i ≤  (1 / lam) ^ (atoms i).support.card :=
    pow_le_pow_of_le_one hinv0 hinv1 (hM i)
  have hcancel : w i * (1 / lam) ^ M i = 1 / (2 : ℚ) ^ (atoms i).support.card := by
    rw [hactivity i, mul_assoc, ← mul_pow]
    simp [one_div, ne_of_gt h0]
  calc
    1 / (2 : ℚ) ^ (atoms i).support.card = w i * (1 / lam) ^ M i := hcancel.symm
    _ ≤  w i * ∏ j ∈ neighbors atoms i, (1 - w j) :=
      mul_le_mul_of_nonneg_left (hpow.trans hprod) (hw0 i)

end
end CompactAtomicLLL
end
end z6

section z7

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

open CompactAtomicLLL

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]



namespace SupportedFamily

variable (F : SupportedFamily V D)

























theorem complement_atom_support (i : F.Index) :
    (F.atom (F.complementEquiv i)).support = (F.atom i).support := rfl

theorem complement_atom_value (i : F.Index) (v : V) (hv : v ∈ (F.atom i).support) :
    (F.atom (F.complementEquiv i)).value v = ((F.atom i).value v).rev := by
  change v ∈ F.support i.1 at hv
  change F.extend i.1 (fun v => (i.2.val v).rev) v = (F.extend i.1 i.2.val v).rev
  simp only [extend,dif_pos hv]

theorem avoids_all_iff (ell : V → Fin 2) :
    (∀ i : F.Index, ¬ Holds (F.atom i) ell) ↔ ∀ d, ¬ F.bad d ell := by
  constructor
  · intro h d hd
    let u : F.LocalBad d :=
      ⟨fun v => ell v.val,(F.bad_restrict d ell).mpr hd⟩
    apply h ⟨d,u⟩
    intro v hv
    change v ∈ F.support d at hv
    change ell v = F.extend d u.val v
    simp only [extend,dif_pos hv,u]
  · intro h i hi
    apply h i.1
    apply (F.locality i.1 (F.extend i.1 i.2.val) ell ?_).mp i.2.property
    intro v hv
    exact (hi v hv).symm





theorem coordinate_total (M : D → ℕ) (lam : ℚ) (v : V) :
    (∑ i ∈ Finset.univ.filter (fun i => v ∈ (F.atom i).support), F.atomWeight M lam i) =
      ∑ d ∈ Finset.univ.filter (fun d => v ∈ F.support d), F.localProbability d * lam ^ M d := by
  simp only [Finset.sum_filter]
  change (∑ i : (Σ d : D, F.LocalBad d),
    if v ∈ F.support i.1 then (1 / (2 : ℚ) ^ (F.support i.1).card) * lam ^ M i.1 else 0) =
    ∑ d : D, if v ∈ F.support d then
      ((Fintype.card (F.LocalBad d) : ℚ) / (2 : ℚ) ^ (F.support d).card) * lam ^ M d else 0
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hv : v ∈ F.support d
  · simp only [if_pos hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  · simp only [if_neg hv, Finset.sum_const_zero]

theorem coordinate_conflict_half (M : D → ℕ) (lam : ℚ) (a : Atom V) (v : V) :
    (∑ i ∈ conflictSlice a F.atom v, F.atomWeight M lam i) =
      (∑ d ∈ Finset.univ.filter (fun d => v ∈ F.support d),
        F.localProbability d * lam ^ M d) / 2 := by
  let bad : F.Index → ℚ := fun i =>
    if v ∈ (F.atom i).support ∧ a.value v ≠ (F.atom i).value v then F.atomWeight M lam i else 0
  let good : F.Index → ℚ := fun i =>
    if v ∈ (F.atom i).support ∧ a.value v = (F.atom i).value v then F.atomWeight M lam i else 0
  let total : F.Index → ℚ := fun i =>
    if v ∈ (F.atom i).support then F.atomWeight M lam i else 0
  have hswitch (i : F.Index) : bad (F.complementEquiv i) = good i := by
    by_cases hv : v ∈ (F.atom i).support
    · have hflip : (a.value v ≠ ((F.atom i).value v).rev) ↔ a.value v = (F.atom i).value v := by
        generalize a.value v = b
        generalize (F.atom i).value v = c
        fin_cases b <;> fin_cases c <;> decide
      simp only [bad,good,F.complement_atom_support, hv, true_and,
        F.complement_atom_value i v hv,hflip]
      rfl
    · simp only [bad,good,F.complement_atom_support,hv,false_and,if_false]
  have hsum : ∑ i, bad i = ∑ i, good i := by
    calc
      ∑ i, bad i = ∑ i, bad (F.complementEquiv i) := (F.complementEquiv.sum_comp bad).symm
      _ = ∑ i, good i := Finset.sum_congr rfl fun i _ => hswitch i
  have hpartition : ∑ i, total i = (∑ i, bad i) + ∑ i, good i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hv : v ∈ (F.atom i).support
    · by_cases hc : a.value v = (F.atom i).value v <;> simp [total,bad,good,hv,hc]
    · simp [total,bad,good,hv]
  have he : (∑ i, bad i) = (∑ i, total i) / 2 := by linarith
  have ht := F.coordinate_total M lam v
  simp only [Finset.sum_filter] at ht
  simp only [Finset.sum_filter]
  rw [← ht]
  simpa only [bad,total,conflictSlice,Finset.sum_filter] using he

theorem exists_joint_avoidance (M : D → ℕ) (lam : ℚ) (hlam : 1 <  lam)
    (hne : ∀ d, (F.support d).Nonempty)
    (hM : ∀ d, (F.support d).card ≤  M d)
    (hactivity : ∀ d, (1 / (2 : ℚ) ^ (F.support d).card) * lam ^ M d <  1)
    (hload : ∀ v,
      (∑ d ∈ Finset.univ.filter (fun d => v ∈ F.support d),
        F.localProbability d * lam ^ M d) / 2 ≤  1 - 1 / lam) :
    ∃ ell : V → Fin 2, ∀ d, ¬ F.bad d ell := by
  obtain ⟨ell,hell⟩ := exists_avoiding_of_coordinate_load F.atom
    (fun i => M i.1) (F.atomWeight M lam) lam hlam
    (fun i => hne i.1) (fun i => hM i.1)
    (fun i => by dsimp [atomWeight]; have h0 : (0 : ℚ) <  lam := lt_trans zero_lt_one hlam; positivity)
    (fun i => hactivity i.1) (fun i => rfl) (by
      intro i v hv
      rw [F.coordinate_conflict_half M lam (F.atom i) v]
      exact hload v)
  exact ⟨ell,(F.avoids_all_iff ell).mp hell⟩

end SupportedFamily
end
end ZL
end
end z7

section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]







































theorem markedSupport_card_le (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M : Finset V) :
    (markedSupport R A M).card ≤  A.card.choose 2 + M.card * A.card := by
  calc
    (markedSupport R A M).card ≤ 
        (internalEdges R A).card + (crossEdges R M A).card := Finset.card_union_le _ _
    _ ≤  A.card.choose 2 + M.card * A.card := by
      rw [_root_.Sensitivity213981Formal.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges R hloop htour]
      apply Nat.add_le_add_left
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_product M A)

theorem markedSupport_card_lower (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M : Finset V) : A.card.choose 2 ≤  (markedSupport R A M).card := by
  rw [← _root_.Sensitivity213981Formal.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges R hloop htour]
  exact Finset.card_le_card Finset.subset_union_left







end
end ZL
end
end z8

section z16

section
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 32768
open scoped Classical BigOperators

namespace CompactLabeling10007
open ZL ZL.RowCounting






















































end CompactLabeling10007
end
end z16

section z17

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
































end
end ZL
end
end z17

section z25

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem activity_small_of_support (E S M : ℕ) (lam : ℚ)
    (hE : 0 <  E) (hES : E ≤  S) (hM : M ≤  2*E)
    (hlam : 1 ≤  lam) (hsq : lam^2 <  2) :
    (1 / (2 : ℚ)^S) * lam^M <  1 := by
  have hp : lam^M <  (2 : ℚ)^S := by
    calc
      lam^M ≤  lam^(2*E) := pow_le_pow_right₀ hlam hM
      _ = (lam^2)^E := pow_mul lam 2 E
      _ <  (2 : ℚ)^E := pow_lt_pow_left₀ hsq (sq_nonneg lam) (Nat.ne_of_gt hE)
      _ ≤  (2 : ℚ)^S := pow_le_pow_right₀ (by norm_num) hES
  have hd : lam^M / (2 : ℚ)^S <  1 := (div_lt_one (by positivity)).mpr hp
  simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hd

theorem ordinaryFamily_support_bounds (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (q a : ℕ) (I : OrdinaryIndex V a) :
    ((ordinaryFamily R q a).support I).card = a.choose 2 := by
  change (internalEdges R I.val).card = _
  rw [_root_.Sensitivity213981Formal.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges R hloop htour,(Finset.mem_powersetCard.mp I.property).2]

theorem markedFamily_support_bounds (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (q a m B : ℕ) (I : MarkedIndex V a m) :
    a.choose 2 ≤  ((markedFamily R q a m B).support I).card ∧
      ((markedFamily R q a m B).support I).card ≤  a.choose 2+m*a := by
  constructor
  · simpa only [markedFamily,markedIndex_cardA] using
      markedSupport_card_lower R hloop htour I.2.val I.1.val
  · simpa only [markedFamily,markedIndex_cardA,markedIndex_cardM] using
      markedSupport_card_le R hloop htour I.2.val I.1.val

end
end ZL
end
end z25

section z27

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL.SupportedFamily
noncomputable section
variable {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T]
variable {D : T → Type*} [∀ t, Fintype (D t)]





theorem exists_avoiding_families
    (F : ∀ t, ZL.SupportedFamily V (D t))
    (M : T → ℕ) (cap : T → ℚ) (lam : ℚ) (hlam : 1 <  lam)
    (hne : ∀ t d, ((F t).support d).Nonempty)
    (hM : ∀ t d, ((F t).support d).card ≤  M t)
    (hactivity : ∀ t d,
      (1 / (2 : ℚ)^((F t).support d).card) * lam^M t <  1)
    (hcap : ∀ t v,
      (∑ d ∈ Finset.univ.filter (fun d => v ∈ (F t).support d),
        (F t).localProbability d * lam^M t) / 2 ≤  cap t)
    (hsum : ∑ t, cap t ≤  1 - 1/lam) :
    ∃ ell : V → Fin 2, ∀ t d, ¬ (F t).bad d ell := by
  obtain ⟨ell,hell⟩ := (iUnion F).exists_joint_avoidance (fun i => M i.1) lam hlam
    (fun i => hne i.1 i.2) (fun i => hM i.1 i.2)
    (fun i => hactivity i.1 i.2) (by
      intro v
      simp only [Finset.sum_filter]
      change ((∑ i : (Σ t, D t), if v ∈ (F i.1).support i.2 then
        (F i.1).localProbability i.2 * lam^M i.1 else 0) / 2) ≤  1-1/lam
      rw [Fintype.sum_sigma,Finset.sum_div]
      apply (Finset.sum_le_sum (fun t _ => ?_)).trans hsum
      simpa only [Finset.sum_filter] using hcap t v)
  exact ⟨ell,fun t d => hell ⟨t,d⟩⟩

end
end ZL.SupportedFamily
end
end z27

section z28

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped Classical BigOperators
noncomputable section

namespace CompactLabeling10007
open ZL ZL.RowCounting
attribute [local irreducible] N degree common lam
variable {V : Type*} [Fintype V] [DecidableEq V]





























end CompactLabeling10007
end
end z28

end Sensitivity10007Labeling

end
end Sensitivity213981Formal


