-- Prove2me | Definitions.Def_Sensitivity213981Formal_PerfectDominatorFamily
-- name    : Sensitivity213981Formal_PerfectDominatorFamily
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:07:00.785824+00:00
-- url     : https://prove2.me/theorems/4c0a54f2-dfa7-45ce-a4e8-2aa2c349d227
-- title:
--   Perfect Dominator Family — sensitivity certificate definitions
-- statement:
--   The definitions for Perfect Dominator Family in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundPerfectFamily.weight_mass`, `ThreeBoundPerfectFamily.weight_map`, `ThreeBoundPerfectFamily.local_probability`, `ThreeBoundPerfectFamily.family`, `ThreeBoundPerfectFamily.incidence_bound`, `ThreeBoundPerfectFamily.coordinate_load`, `ThreeBoundPerfectFamily.weight`, `ThreeBoundPerfectFamily.dominated_subset_compl`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; PerfectDominatorFamily.lean, lines 1–187.

import Definitions.Def_Sensitivity213981Formal_MarkedArcMass
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
/- Coherent dominated targets with three markers, counted by arc averaging. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundPerfectFamily
open Sensitivity10007Labeling ZL ZL.RowCounting ThreeBoundArcAverage
open scoped Classical BigOperators
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def family (R : V → V → Prop) (a m : ℕ) :
    SupportedFamily (V × V) (MarkedIndex V a m) where
  support I := markedSupport R I.2.val I.1.val
  bad I ell := I.2.val ⊆ dominatedBy R I.1.val ∧ CoherentBad R I.2.val I.1.val ell
  locality I ell ell' h := and_congr_right fun _ =>
    coherentBad_congr R I.2.val I.1.val ell ell' h
  complement I ell := and_congr_right fun _ =>
    coherentBad_complement R I.2.val I.1.val ell

def weight (R : V → V → Prop) (a m : ℕ) (I : MarkedIndex V a m) : ℚ :=
  if I.2.val ⊆ dominatedBy R I.1.val then 1 else 0

theorem dominated_subset_compl (R : V → V → Prop) (hloop : ∀ x, ¬ R x x)
    (M : Finset V) : dominatedBy R M ⊆ Mᶜ := by
  intro y hy
  exact Finset.mem_compl.mpr fun hm => hloop y ((Finset.mem_filter.mp hy).2 y hm)

theorem weight_mass (R : V → V → Prop) (hloop : ∀ x, ¬ R x x)
    (a m d : ℕ) (hdom : ∀ M : Finset V, M.card = m → (dominatedBy R M).card ≤  d) :
    (∑ I : MarkedIndex V a m, weight R a m I) ≤ 
      ((Fintype.card V).choose m : ℚ) * (d.choose a : ℚ) := by
  change (∑ I : Σ M : ((Finset.univ : Finset V).powersetCard m), M.valᶜ.powersetCard a,
    if I.2.val ⊆ dominatedBy R I.1.val then (1 : ℚ) else 0) ≤  _
  rw [Fintype.sum_sigma]
  calc
    _ ≤  ∑ _M : (Finset.univ : Finset V).powersetCard m, (d.choose a : ℚ) := by
      apply Finset.sum_le_sum
      intro M _
      rw [Finset.sum_coe_sort (s := M.valᶜ.powersetCard a)
        (f := fun A : Finset V => if A ⊆ dominatedBy R M.val then (1 : ℚ) else 0)]
      have hfilter : (M.valᶜ.powersetCard a).filter
          (fun A => A ⊆ dominatedBy R M.val) = (dominatedBy R M.val).powersetCard a := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h =>
          ⟨⟨h.1.trans (dominated_subset_compl R hloop M.val),h.2⟩,h.1⟩⟩
      rw [← Finset.sum_filter, hfilter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powersetCard]
      exact_mod_cast Nat.choose_le_choose a (hdom M.val (Finset.mem_powersetCard.mp M.property).2)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]

theorem weight_map (R : V → V → Prop) (a m : ℕ) (e : V ≃ V)
    (hR : ∀ x y, R (e x) (e y) ↔ R x y) (I : MarkedIndex V a m) :
    weight R a m (markedIndexMap a m e I) = weight R a m I := by
  have hdom : (I.2.val.map e.toEmbedding ⊆ dominatedBy R (I.1.val.map e.toEmbedding)) ↔
      I.2.val ⊆ dominatedBy R I.1.val := by
    constructor
    · intro h y hy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro x hx
      exact (hR x y).mp ((Finset.mem_filter.mp (h (Finset.mem_map.mpr ⟨y,hy,rfl⟩))).2
        (e x) (Finset.mem_map.mpr ⟨x,hx,rfl⟩))
    · intro h y hy
      obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro x hx
      obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hx
      exact (hR w z).mpr ((Finset.mem_filter.mp (h hz)).2 w hw)
  simp only [weight, markedIndexMap_targets, markedIndexMap_markers, hdom]

theorem local_probability (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (a m : ℕ) (I : MarkedIndex V a m) :
    (family R a m).localProbability I ≤ 
      ((2 : ℚ)^a / 2^(a.choose 2+m*a)) * weight R a m I := by
  by_cases hd : I.2.val ⊆ dominatedBy R I.1.val
  · have hc := coherent_localProbability_le (family R a m) I R I.2.val I.1.val
      rfl (fun ell => by simp only [family, hd, true_and, CoherentBad])
    have hs := dominatedSupport_card R hloop htour I.2.val I.1.val
      (markedIndex_disjoint a m I)
      (fun x hx y hy => (Finset.mem_filter.mp (hd hy)).2 x hx)
    simpa only [weight, if_pos hd, mul_one, hs, markedIndex_cardA, markedIndex_cardM] using hc
  · have hempty : IsEmpty ((family R a m).LocalBad I) :=
      ⟨fun u => hd u.property.1⟩
    have hc : Fintype.card ((family R a m).LocalBad I) = 0 :=
      Fintype.card_eq_zero_iff.mpr hempty
    simp only [SupportedFamily.localProbability, hc, Nat.cast_zero, zero_div,
      weight, if_neg hd, mul_zero, le_refl]

theorem incidence_bound (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (htrans : ∀ x y u v, R x y → R u v →
      ∃ e : V ≃ V, e x = u ∧ e y = v ∧ ∀ a b, R (e a) (e b) ↔ R a b)
    (a m d : ℕ) (hdom : ∀ M : Finset V, M.card = m → (dominatedBy R M).card ≤  d)
    (x y : V) (hxy : R x y) :
    incidence (fun I : MarkedIndex V a m => markedSupport R I.2.val I.1.val)
      (weight R a m) (x,y) ≤ 
      (a.choose 2+m*a : ℕ) * (((Fintype.card V).choose m : ℚ)*(d.choose a : ℚ)) /
        (Fintype.card V).choose 2 := by
  let edges : Finset (V × V) := Finset.univ.filter fun e => R e.1 e.2
  have he : (x,y) ∈ edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy⟩
  have hsub (I : MarkedIndex V a m) : markedSupport R I.2.val I.1.val ⊆ edges := by
    intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    obtain he|he := Finset.mem_union.mp he <;> exact (Finset.mem_filter.mp he).2
  have hsize (I : MarkedIndex V a m) :
      (markedSupport R I.2.val I.1.val).card ≤  a.choose 2+m*a := by
    simpa only [markedIndex_cardA, markedIndex_cardM] using
      markedSupport_card_le R hloop htour I.2.val I.1.val
  have hunif (e : V × V) (he : e ∈ edges) :
      incidence (fun I : MarkedIndex V a m => markedSupport R I.2.val I.1.val)
        (weight R a m) e =
      incidence (fun I : MarkedIndex V a m => markedSupport R I.2.val I.1.val)
        (weight R a m) (x,y) := by
    obtain ⟨σ,hx,hy,hσ⟩ := htrans x y e.1 e.2 hxy (Finset.mem_filter.mp he).2
    apply incidence_invariant _ _ (x,y) e (markedIndexMap a m σ)
    · intro I
      rw [markedIndex_support R a m σ hσ I]
      have hmap : (σ.prodCongr σ) (x,y) = e := Prod.ext hx hy
      rw [← hmap, Finset.mem_map_equiv]
      simp only [Equiv.symm_apply_apply]
    · exact weight_map R a m σ hσ
  have hcard : edges.card = (Fintype.card V).choose 2 := by
    have h := Paley10007Verified.CompactLabeling.card_internalEdges R hloop htour
      (Finset.univ : Finset V)
    simpa only [internalEdges, Finset.univ_product_univ, Finset.card_univ, edges] using h
  have h := uniform_incidence_bound edges _ _ (x,y) he (a.choose 2+m*a)
    (((Fintype.card V).choose m : ℚ)*(d.choose a : ℚ)) hsub hsize
    (fun I => by unfold weight; positivity) (weight_mass R hloop a m d hdom) hunif
  simpa only [hcard] using h

theorem coordinate_load (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (htrans : ∀ x y u v, R x y → R u v →
      ∃ e : V ≃ V, e x = u ∧ e y = v ∧ ∀ a b, R (e a) (e b) ↔ R a b)
    (a m d : ℕ) (hdom : ∀ M : Finset V, M.card = m → (dominatedBy R M).card ≤  d)
    (lam : ℚ) (hlam : 0 ≤  lam) (e : V × V) :
    (∑ I ∈ Finset.univ.filter (fun I => e ∈ (family R a m).support I),
      (family R a m).localProbability I * lam^(a.choose 2+m*a))/2 ≤ 
      ((a.choose 2+m*a : ℕ) * (((Fintype.card V).choose m : ℚ)*(d.choose a : ℚ)) /
        (Fintype.card V).choose 2) * ((2 : ℚ)^a/2^(a.choose 2+m*a)) *
        lam^(a.choose 2+m*a)/2 := by
  by_cases hxy : R e.1 e.2
  · have hmass := incidence_bound R hloop htour htrans a m d hdom e.1 e.2 hxy
    have hprob : (∑ I ∈ Finset.univ.filter (fun I => e ∈ (family R a m).support I),
        (family R a m).localProbability I) ≤ 
        ((2 : ℚ)^a/2^(a.choose 2+m*a))*
          incidence (fun I : MarkedIndex V a m => markedSupport R I.2.val I.1.val)
            (weight R a m) e := by
      calc
        _ ≤  ∑ I ∈ Finset.univ.filter (fun I => e ∈ (family R a m).support I),
            ((2 : ℚ)^a/2^(a.choose 2+m*a))*weight R a m I :=
          Finset.sum_le_sum fun I _ => local_probability R hloop htour a m I
        _ = _ := by
          rw [← Finset.mul_sum]
          congr 1
          unfold incidence
          rw [← Finset.sum_filter]
          rfl
    rw [← Finset.sum_mul]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam _)
    rw [mul_comm _ ((2 : ℚ)^a/2^(a.choose 2+m*a))]
    exact hprob.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
  · have hempty : (Finset.univ.filter
        (fun I : MarkedIndex V a m => e ∈ (family R a m).support I)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro I _ hi
      obtain hi|hi := Finset.mem_union.mp hi <;> exact hxy (Finset.mem_filter.mp hi).2
    rw [hempty, Finset.sum_empty, zero_div]
    positivity

end
end ThreeBoundPerfectFamily



end
end Sensitivity213981Formal


