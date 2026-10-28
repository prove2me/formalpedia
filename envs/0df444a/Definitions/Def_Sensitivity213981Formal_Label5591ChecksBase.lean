-- Prove2me | Definitions.Def_Sensitivity213981Formal_Label5591ChecksBase
-- name    : Sensitivity213981Formal_Label5591ChecksBase
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:14:55.224985+00:00
-- url     : https://prove2.me/theorems/583f79ba-17d7-4a56-ab20-f492d140d768
-- title:
--   Label5591 Checks Base — sensitivity certificate definitions
-- statement:
--   The definitions for Label5591 Checks Base in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.Caps.ordinary_tangent_6`, `Sensitivity5591Labeling.Caps.ordinary_tangent_7`, `Sensitivity5591Labeling.Caps.ordinary_tangent_8`, `Sensitivity5591Labeling.Caps.elementary_ordinary`, `Sensitivity5591Labeling.Caps.ordinary_tangent`, `Sensitivity5591Labeling.Caps.marked_tangents`, `Sensitivity5591Labeling.Caps.marked_parameters`, `Sensitivity5591Labeling.Caps.total_load`, `Sensitivity5591Labeling.Caps.marked_data`, `Sensitivity5591Labeling.Caps.basic_constants`, `Sensitivity5591Labeling.Caps.ordinary_tangent_0`, `Sensitivity5591Labeling.Caps.ordinary_tangent_1`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Label5591ChecksBase.lean, lines 1–103.

import Definitions.Def_Sensitivity213981Formal_Label5591Data
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

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
set_option exponentiation.threshold 1000000
namespace Sensitivity5591Labeling.Caps
open Sensitivity10007Labeling ZL ZL.RowCounting
open scoped Classical BigOperators
theorem basic_constants : N=5591 ∧ degree=2795 ∧ common=1397 ∧ 1< lam ∧ lam^2< 2 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem elementary_ordinary : ∀q:Fin 9,
    2≤ ordinaryA q ∧ ordinaryA q≤ N ∧ 0< ordinaryLowValue q ∧ 0< ordinaryHighValue q ∧
    ordinaryRem q≤ ordinaryA q ∧ ordinaryLo q*ordinaryA q+ordinaryRem q=(ordinaryA q).choose 2 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem marked_data : ∀i:Fin 12,
    (marked i).a≤ (CompactLabeling10007.marked i).a ∧ 0< (marked i).a.choose 2 ∧
    (marked i).a.choose 2+(marked i).m*(marked i).a≤ 2*(marked i).a.choose 2 ∧
    0≤ markedW (marked i) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent_0 : ∀d:Fin (ordinaryA 0),
    rowPatterns 0 d.val*ordinaryLowValue 0^d.val*ordinaryHighValue 0^ordinaryLo 0≤ 
      ordinaryLowValue 0^(ordinaryLo 0+1)*ordinaryHighValue 0^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent_1 : ∀d:Fin (ordinaryA 1),
    rowPatterns 1 d.val*ordinaryLowValue 1^d.val*ordinaryHighValue 1^ordinaryLo 1≤ 
      ordinaryLowValue 1^(ordinaryLo 1+1)*ordinaryHighValue 1^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent_2 : ∀d:Fin (ordinaryA 2),
    rowPatterns 2 d.val*ordinaryLowValue 2^d.val*ordinaryHighValue 2^ordinaryLo 2≤ 
      ordinaryLowValue 2^(ordinaryLo 2+1)*ordinaryHighValue 2^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent_3 : ∀d:Fin (ordinaryA 3),
    rowPatterns 3 d.val*ordinaryLowValue 3^d.val*ordinaryHighValue 3^ordinaryLo 3≤ 
      ordinaryLowValue 3^(ordinaryLo 3+1)*ordinaryHighValue 3^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent_4 : ∀d:Fin (ordinaryA 4),
    rowPatterns 4 d.val*ordinaryLowValue 4^d.val*ordinaryHighValue 4^ordinaryLo 4≤ 
      ordinaryLowValue 4^(ordinaryLo 4+1)*ordinaryHighValue 4^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent_5 : ∀d:Fin (ordinaryA 5),
    rowPatterns 5 d.val*ordinaryLowValue 5^d.val*ordinaryHighValue 5^ordinaryLo 5≤ 
      ordinaryLowValue 5^(ordinaryLo 5+1)*ordinaryHighValue 5^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent_6 : ∀d:Fin (ordinaryA 6),
    rowPatterns 6 d.val*ordinaryLowValue 6^d.val*ordinaryHighValue 6^ordinaryLo 6≤ 
      ordinaryLowValue 6^(ordinaryLo 6+1)*ordinaryHighValue 6^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent_7 : ∀d:Fin (ordinaryA 7),
    rowPatterns 7 d.val*ordinaryLowValue 7^d.val*ordinaryHighValue 7^ordinaryLo 7≤ 
      ordinaryLowValue 7^(ordinaryLo 7+1)*ordinaryHighValue 7^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent_8 : ∀d:Fin (ordinaryA 8),
    rowPatterns 8 d.val*ordinaryLowValue 8^d.val*ordinaryHighValue 8^ordinaryLo 8≤ 
      ordinaryLowValue 8^(ordinaryLo 8+1)*ordinaryHighValue 8^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
theorem ordinary_tangent(q:Fin 9) : ∀d:Fin (ordinaryA q),
    rowPatterns q.val d.val*ordinaryLowValue q^d.val*ordinaryHighValue q^ordinaryLo q≤ 
      ordinaryLowValue q^(ordinaryLo q+1)*ordinaryHighValue q^d.val := by
  fin_cases q
  · exact ordinary_tangent_0
  · exact ordinary_tangent_1
  · exact ordinary_tangent_2
  · exact ordinary_tangent_3
  · exact ordinary_tangent_4
  · exact ordinary_tangent_5
  · exact ordinary_tangent_6
  · exact ordinary_tangent_7
  · exact ordinary_tangent_8
theorem marked_tangents(i:Fin 12) (d t:ℕ) (hd:d< (marked i).a) (ht:t≤ (marked i).q) :
    (rowPatterns t d:ℚ)≤ (marked i).C t*(marked i).u^d := by
  have hh:=CompactLabeling10007.marked_tangents i
    ⟨d,hd.trans_le (marked_data i).1⟩ ⟨t,Nat.lt_succ_of_le ht⟩
  exact hh

theorem marked_parameters(i:Fin 12) :
    0≤ (marked i).u ∧ 0≤ (marked i).gamma ∧ 0≤ (marked i).wm ∧
    (∀t≤ (marked i).q,0≤ (marked i).C t) ∧
    (∀f≤ (marked i).m,orientationWeight (marked i).q (marked i).C f≤ (marked i).wm ∧
      orientationWeight (marked i).q (marked i).C f≤ 
        (marked i).alpha+(marked i).beta*f+(marked i).gamma*f.choose 2) := by
  obtain ⟨_,_,hu,hg,hw,_,hC,hf⟩:=CompactLabeling10007.marked_parameters i
  exact ⟨hu,hg,hw,fun t ht=>hC ⟨t,Nat.lt_succ_of_le ht⟩,
    fun f hf'=>hf ⟨f,Nat.lt_succ_of_le hf'⟩⟩

theorem total_load : (∑q:Fin 9,ordinaryCeiling q)+(∑i:Fin 12,markedCeiling i)+
    sourceCeiling+dominatorCeiling+perfectCeiling≤ 1-1/lam := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,perfectLoad,markedCutoffs,markedA,marked,markedW,markedHead,markedPref,markedLoad,ordinaryCeilings,ordinaryCeiling,markedCeilings,markedCeiling,sourceCeiling,dominatorCeiling,perfectCeiling,ThreeBoundRefinedMarked.headFactor,headErrorFactor,rowPatterns,Nat.choose_eq_fast_choose,CompactLabeling10007.MarkedParameters.C,CompactLabeling10007.MarkedParameters.B,CompactLabeling10007.marked0,CompactLabeling10007.marked1,CompactLabeling10007.marked2,CompactLabeling10007.marked3,CompactLabeling10007.marked4,CompactLabeling10007.marked5,CompactLabeling10007.marked6,CompactLabeling10007.marked7,CompactLabeling10007.marked8,CompactLabeling10007.marked9,CompactLabeling10007.marked10,CompactLabeling10007.marked11,CompactLabeling10007.markedParameters,CompactLabeling10007.marked]
  decide +kernel
end Sensitivity5591Labeling.Caps


end
end Sensitivity213981Formal


