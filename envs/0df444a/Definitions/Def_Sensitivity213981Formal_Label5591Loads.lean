-- Prove2me | Definitions.Def_Sensitivity213981Formal_Label5591Loads
-- name    : Sensitivity213981Formal_Label5591Loads
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:22:06.225021+00:00
-- url     : https://prove2.me/theorems/6ff71586-2753-465d-83b3-768ff78836a7
-- title:
--   Label5591 Loads — sensitivity certificate definitions
-- statement:
--   The definitions for Label5591 Loads in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.Caps.marked_coordinate_load`, `Sensitivity5591Labeling.Caps.marked_positive_m`, `Sensitivity5591Labeling.Caps.ordinary_coordinate_load`, `Sensitivity5591Labeling.Caps.marked_probability`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Label5591Loads.lean, lines 1–97.

import Definitions.Def_Sensitivity213981Formal_Label5591Checks
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
/- The 23 ordinary, marked, and small-dominator families at order5591. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Sensitivity5591Labeling.Caps
open Sensitivity10007Labeling ZL ZL.RowCounting ThreeBoundArcAverage
open scoped Classical BigOperators
noncomputable section
variable {V:Type*}[Fintype V][DecidableEq V]

theorem marked_positive_m(i:Fin 12):0< (marked i).m := by fin_cases i <;> decide +kernel

theorem marked_probability(R:V→V→Prop)
    (hloop:∀x,¬R x x)(htour:∀x y,x≠y→(R x y↔¬R y x))
    (i:Fin 12)(I:MarkedIndex V (marked i).a (marked i).m) :
    (markedFamily R (marked i).q (marked i).a (marked i).m (marked i).B).localProbability I≤ 
      markedPref (marked i)*markedWeight R (marked i).q (marked i).a (marked i).m (marked i).C I := by
  let p:=marked i
  obtain ⟨hu,hg,hw,hC,hf⟩:=marked_parameters i
  have ht:∀d< p.a,∀t≤ p.q,(rowPatterns t d:ℚ)≤ p.C t*p.u^d:=
    fun d hd t ht=>marked_tangents i d t hd ht
  have hA:=markedIndex_cardA p.a p.m I
  have hM:=markedIndex_cardM p.a p.m I
  have hd:=markedIndex_disjoint p.a p.m I
  by_cases hz:p.zero=true
  · have hb:p.B=0:=by simp [CompactLabeling10007.MarkedParameters.B,hz]
    have hh:=marked_localProbability_weighted_le
      (markedFamily R p.q p.a p.m p.B) I R hloop htour I.2.val I.1.val ∅ p.q p.B hd rfl
      (fun _=>Iff.rfl) p.u p.C hu hC (by simpa only [hA] using ht)
    simpa only [hA,hM,markedPref,markedHead,hz,if_pos,headErrorFactor,hb,
      Bool.true_eq,markedWeight,p] using hh
  · have hz':p.zero=false:=Bool.eq_false_iff.mpr hz
    have hb:p.B≠0 := by
      simp only [CompactLabeling10007.MarkedParameters.B,hz',Bool.false_eq_true,if_false]
      exact Nat.ne_of_gt (Nat.mul_pos (marked_positive_m i) (by omega))
    by_cases hm:p.m=2
    · have hh:=ThreeBoundRefinedMarked.localProbability_weighted_le_two
        (markedFamily R p.q p.a p.m p.B) I R hloop htour I.2.val I.1.val ∅ p.q p.B hd
        (hM.trans hm) rfl (fun _=>Iff.rfl) p.u p.C hu hC (by simpa only [hA] using ht)
      simpa only [hA,hM,markedPref,markedHead,hz',Bool.false_eq_true,if_false,hm,if_pos,
        markedWeight,p] using hh
    · have hh:=marked_localProbability_weighted_le
        (markedFamily R p.q p.a p.m p.B) I R hloop htour I.2.val I.1.val ∅ p.q p.B hd rfl
        (fun _=>Iff.rfl) p.u p.C hu hC (by simpa only [hA] using ht)
      simpa only [hA,hM,markedPref,markedHead,hz',Bool.false_eq_true,if_false,hm,if_neg,
        headErrorFactor,hb,markedWeight,p] using hh

theorem marked_coordinate_load(R:V→V→Prop)(hn:Fintype.card V=N)
    (hloop:∀x,¬R x x)(htour:∀x y,x≠y→(R x y↔¬R y x))
    (hin:∀y,(inOn R Finset.univ y).card=degree)
    (hcommon:∀x y,x≠y→(Finset.univ.filter fun z=>R z x∧R z y).card=common)
    (htrans:∀x y u v,R x y→R u v→
      ∃e:V≃V,e x=u∧e y=v∧∀a b,R (e a) (e b)↔R a b)
    (i:Fin 12)(e:V×V) :
    (∑I∈Finset.univ.filter (fun I=>e∈(markedFamily R (marked i).q (marked i).a
      (marked i).m (marked i).B).support I),
      (markedFamily R (marked i).q (marked i).a (marked i).m (marked i).B).localProbability I*
        lam^((marked i).a.choose 2+(marked i).m*(marked i).a))/2≤ markedCeiling i := by
  let p:=marked i
  obtain ⟨hu,hg,hw,hC,hf⟩:=marked_parameters i
  have hsum(M:Finset V)(hM:M∈Finset.univ.powersetCard p.m):
      ∑z∈Mᶜ,orientationWeight p.q p.C (outOn R M z).card≤ markedW p := by
    have hMc: M.card=p.m:=(Finset.mem_powersetCard.mp hM).2
    have hpoly:∀f≤ M.card,orientationWeight p.q p.C f≤ p.alpha+p.beta*f+p.gamma*f.choose 2:=
      fun f hf'=> (hf f (hf'.trans_eq hMc)).2
    have hh:=orientation_weight_sum_le R degree common hloop htour hin hcommon M
      (orientationWeight p.q p.C) p.alpha p.beta p.gamma hg hpoly
    simpa only [hn,hMc,markedW] using hh
  have hpref:0≤ markedPref p:=by unfold markedPref; positivity
  have hlam:0≤ lam:=le_trans (by norm_num) basic_constants.2.2.2.1.le
  have hh:=markedFamily_arc_load_le R hloop htour htrans p.q p.a p.m p.B p.C hC
    (markedW p) (markedPref p) lam hpref hlam (marked_data i).2.2.2 hsum
    (marked_probability R hloop htour i) e.1 e.2
  apply le_trans ?_ (marked_load i)
  simpa only [hn,markedLoad,p] using hh

theorem ordinary_coordinate_load(R:V→V→Prop)(hn:Fintype.card V=N)
    (hloop:∀x,¬R x x)(htour:∀x y,x≠y→(R x y↔¬R y x))
    (q:Fin 9)(e:V×V) :
    (∑I∈Finset.univ.filter (fun I=>e∈(ordinaryFamily R q.val (ordinaryA q)).support I),
      (ordinaryFamily R q.val (ordinaryA q)).localProbability I*lam^((ordinaryA q).choose 2))/2≤ 
      ordinaryCeiling q := by
  obtain ⟨hA2,hAN,hL,hH,hr,hd⟩:=elementary_ordinary q
  have hlam:0≤ lam:=le_trans (by norm_num) basic_constants.2.2.2.1.le
  have ht:∀d< ordinaryA q,rowPatterns q.val d*ordinaryLowValue q^d*
      ordinaryHighValue q^ordinaryLo q≤ ordinaryLowValue q^(ordinaryLo q+1)*ordinaryHighValue q^d:=
    fun d hd=>ordinary_tangent q ⟨d,hd⟩
  have hh:=Paley10007Verified.CompactLabeling.ordinaryFamily_load_le R N hn hloop htour
    q.val (ordinaryA q) (ordinaryLo q) (ordinaryRem q) (ordinaryLowValue q) (ordinaryHighValue q)
    lam hlam hr hL hH hd ht e.1 e.2
  exact hh.trans (ordinary_load q)

end
end Sensitivity5591Labeling.Caps



end
end Sensitivity213981Formal


