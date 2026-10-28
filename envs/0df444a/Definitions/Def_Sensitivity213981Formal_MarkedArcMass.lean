-- Prove2me | Definitions.Def_Sensitivity213981Formal_MarkedArcMass
-- name    : Sensitivity213981Formal_MarkedArcMass
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:06:15.656141+00:00
-- url     : https://prove2.me/theorems/788cea59-4f5f-4ac3-8fa6-ec71358229e5
-- title:
--   Marked Arc Mass — sensitivity certificate definitions
-- statement:
--   The definitions for Marked Arc Mass in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundArcAverage.markedWeight_incidence_uniform`, `ThreeBoundArcAverage.markedWeight_incidence_bound`, `ThreeBoundArcAverage.markedWeight`, `ThreeBoundArcAverage.markedWeight_nonneg`, `ThreeBoundArcAverage.markedWeight_mass`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MarkedArcMass.lean, lines 1–99.

import Definitions.Def_Sensitivity213981Formal_MarkedTransport
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Paley5591
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
/- Exact weighted marked-event mass and arc averaging. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundArcAverage
open Sensitivity10007Labeling ZL ZL.RowCounting
open scoped Classical BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def markedWeight (R : V→V→Prop) (q a m : ℕ) (C : ℕ→ℚ) (I : MarkedIndex V a m) : ℚ :=
  ∏z∈I.2.val, orientationWeight q C (outOn R I.1.val z).card

theorem markedWeight_nonneg (R : V→V→Prop) (q a m : ℕ) (C : ℕ→ℚ)
    (hC : ∀t≤ q,0≤ C t) (I : MarkedIndex V a m) : 0≤ markedWeight R q a m C I :=
  Finset.prod_nonneg fun z _=>orientationWeight_nonneg q C hC _

theorem markedWeight_mass (R : V→V→Prop) (q a m : ℕ) (C : ℕ→ℚ)
    (hC : ∀t≤ q,0≤ C t) (W : ℚ)
    (hsum : ∀M∈(Finset.univ : Finset V).powersetCard m,
      ∑z∈Mᶜ,orientationWeight q C (outOn R M z).card≤ W) :
    (∑I:MarkedIndex V a m, markedWeight R q a m C I)≤ 
      ((Fintype.card V).choose m : ℚ)*W^a/a.factorial := by
  change (∑I : Σ M : ((Finset.univ : Finset V).powersetCard m), M.valᶜ.powersetCard a,
    ∏z∈I.2.val,orientationWeight q C (outOn R I.1.val z).card)≤ _
  rw [Fintype.sum_sigma]
  calc
    (∑M : (Finset.univ : Finset V).powersetCard m,
        ∑A : M.valᶜ.powersetCard a,
          ∏z∈A.val,orientationWeight q C (outOn R M.val z).card)≤ 
        ∑_M : (Finset.univ : Finset V).powersetCard m,W^a/a.factorial := by
      apply Finset.sum_le_sum
      intro M _
      rw [Finset.sum_coe_sort (s:=M.valᶜ.powersetCard a)
        (f:=fun A:Finset V=>∏z∈A,orientationWeight q C (outOn R M.val z).card)]
      exact weightedSubsets_le M.valᶜ _ (fun z=>orientationWeight_nonneg q C hC _) a W
        (hsum M.val M.property)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,
      Finset.card_powersetCard,Finset.card_univ,nsmul_eq_mul]; ring

theorem markedWeight_incidence_uniform (R : V→V→Prop) (q a m : ℕ) (C : ℕ→ℚ)
    (e f : V×V) (σ : V≃V) (hσ : ∀x y,R (σ x) (σ y)↔R x y)
    (he : σ e.1=f.1) (hf : σ e.2=f.2) :
    incidence (fun I:MarkedIndex V a m=>markedSupport R I.2.val I.1.val)
      (markedWeight R q a m C) f=
    incidence (fun I:MarkedIndex V a m=>markedSupport R I.2.val I.1.val)
      (markedWeight R q a m C) e := by
  apply incidence_invariant _ _ e f (markedIndexMap a m σ)
  · intro I
    rw [markedIndex_support R a m σ hσ I]
    have hmap : (σ.prodCongr σ) e=f := by
      apply Prod.ext <;> assumption
    rw [←hmap,Finset.mem_map_equiv]
    simp only [Equiv.symm_apply_apply]
  · intro I
    exact markedIndex_weight R a m q C σ hσ I

theorem markedWeight_incidence_bound (R : V→V→Prop)
    (hloop : ∀x,¬R x x) (htour : ∀x y,x≠y→(R x y↔¬R y x))
    (htrans : ∀x y u v,R x y→R u v→
      ∃e:V≃V,e x=u∧e y=v∧∀a b,R (e a) (e b)↔R a b)
    (q a m : ℕ) (C : ℕ→ℚ) (hC : ∀t≤ q,0≤ C t) (W : ℚ)
    (hsum : ∀M∈(Finset.univ : Finset V).powersetCard m,
      ∑z∈Mᶜ,orientationWeight q C (outOn R M z).card≤ W)
    (x y : V) (hxy : R x y) :
    incidence (fun I:MarkedIndex V a m=>markedSupport R I.2.val I.1.val)
      (markedWeight R q a m C) (x,y)≤ 
      (a.choose 2+m*a : ℕ)*(((Fintype.card V).choose m : ℚ)*W^a/a.factorial)/
        (Fintype.card V).choose 2 := by
  let edges : Finset (V×V) := Finset.univ.filter fun e=>R e.1 e.2
  have he : (x,y)∈edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy⟩
  have hsub (I:MarkedIndex V a m) : markedSupport R I.2.val I.1.val⊆edges := by
    intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    obtain he|he:=Finset.mem_union.mp he <;> exact (Finset.mem_filter.mp he).2
  have hsize (I:MarkedIndex V a m) : (markedSupport R I.2.val I.1.val).card≤ a.choose 2+m*a := by
    have h:=markedSupport_card_add R hloop htour I.2.val I.1.val (markedIndex_disjoint a m I)
    rw [markedIndex_cardA,markedIndex_cardM] at h
    omega
  have hunif (e:V×V) (he:e∈edges) :
      incidence (fun I:MarkedIndex V a m=>markedSupport R I.2.val I.1.val)
        (markedWeight R q a m C) e=
      incidence (fun I:MarkedIndex V a m=>markedSupport R I.2.val I.1.val)
        (markedWeight R q a m C) (x,y) := by
    obtain ⟨σ,hx,hy,hσ⟩:=htrans x y e.1 e.2 hxy (Finset.mem_filter.mp he).2
    exact markedWeight_incidence_uniform R q a m C (x,y) e σ hσ hx hy
  have hcard : edges.card=(Fintype.card V).choose 2 := by
    have h:=Paley10007Verified.CompactLabeling.card_internalEdges R hloop htour (Finset.univ:Finset V)
    simpa only [internalEdges,Finset.univ_product_univ,Finset.card_univ,edges] using h
  have h:=uniform_incidence_bound edges _ _ (x,y) he (a.choose 2+m*a)
    (((Fintype.card V).choose m : ℚ)*W^a/a.factorial) hsub hsize
    (markedWeight_nonneg R q a m C hC) (markedWeight_mass R q a m C hC W hsum) hunif
  simpa only [hcard] using h

end
end ThreeBoundArcAverage


end
end Sensitivity213981Formal


