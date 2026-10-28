-- Prove2me | Definitions.Def_Sensitivity213981Formal_MarkedArcLoad
-- name    : Sensitivity213981Formal_MarkedArcLoad
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:12:23.966566+00:00
-- url     : https://prove2.me/theorems/20719811-969f-4d63-93ab-3e5dfeccb1fa
-- title:
--   Marked Arc Load — sensitivity certificate definitions
-- statement:
--   The definitions for Marked Arc Load in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundArcAverage.markedFamily_arc_load_le`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MarkedArcLoad.lean, lines 1–58.

import Definitions.Def_Sensitivity213981Formal_MarkedArcMass
import Definitions.Def_Sensitivity213981Formal_MarkedTwoProbability
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
/- Per-arc probability load from the invariant weighted incidence bound. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundArcAverage
open Sensitivity10007Labeling ZL ZL.RowCounting
open scoped Classical BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem markedFamily_arc_load_le (R : V→V→Prop)
    (hloop:∀x,¬R x x) (htour:∀x y,x≠y→(R x y↔¬R y x))
    (htrans:∀x y u v,R x y→R u v→
      ∃e:V≃V,e x=u∧e y=v∧∀a b,R (e a) (e b)↔R a b)
    (q a m B:ℕ) (C:ℕ→ℚ) (hC:∀t≤ q,0≤ C t) (W pref lam:ℚ)
    (hpref:0≤ pref) (hlam:0≤ lam) (hW:0≤ W)
    (hsum:∀M∈(Finset.univ:Finset V).powersetCard m,
      ∑z∈Mᶜ,orientationWeight q C (outOn R M z).card≤ W)
    (hlocal:∀I:MarkedIndex V a m,
      (markedFamily R q a m B).localProbability I≤ pref*markedWeight R q a m C I)
    (x y:V) :
    (∑I∈Finset.univ.filter (fun I=>(x,y)∈(markedFamily R q a m B).support I),
      (markedFamily R q a m B).localProbability I*lam^(a.choose 2+m*a))/2≤ 
      pref*((a.choose 2+m*a:ℕ)*(((Fintype.card V).choose m:ℚ)*W^a/a.factorial)/
        (Fintype.card V).choose 2)*lam^(a.choose 2+m*a)/2 := by
  by_cases hxy:R x y
  · have hmass:=markedWeight_incidence_bound R hloop htour htrans q a m C hC W hsum x y hxy
    have hprob :
        (∑I∈Finset.univ.filter (fun I=>(x,y)∈(markedFamily R q a m B).support I),
          (markedFamily R q a m B).localProbability I)≤ 
        pref*incidence (fun I:MarkedIndex V a m=>markedSupport R I.2.val I.1.val)
          (markedWeight R q a m C) (x,y) := by
      calc
        _≤ ∑I∈Finset.univ.filter (fun I=>(x,y)∈(markedFamily R q a m B).support I),
          pref*markedWeight R q a m C I := Finset.sum_le_sum fun I _=>hlocal I
        _=_ := by
          rw [←Finset.mul_sum]
          congr 1
          unfold incidence
          rw [←Finset.sum_filter]
          rfl
    rw [←Finset.sum_mul]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam _)
    exact hprob.trans (mul_le_mul_of_nonneg_left hmass hpref)
  · have hempty : (Finset.univ.filter (fun I:MarkedIndex V a m=>
        (x,y)∈(markedFamily R q a m B).support I))=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro I _ hi
      obtain hi|hi:=Finset.mem_union.mp hi <;> exact hxy (Finset.mem_filter.mp hi).2
    rw [hempty,Finset.sum_empty,zero_div]

    positivity

end
end ThreeBoundArcAverage


end
end Sensitivity213981Formal


