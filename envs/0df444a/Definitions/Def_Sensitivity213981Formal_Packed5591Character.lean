-- Prove2me | Definitions.Def_Sensitivity213981Formal_Packed5591Character
-- name    : Sensitivity213981Formal_Packed5591Character
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:26:32.002159+00:00
-- url     : https://prove2.me/theorems/12c32670-4a0b-476d-974d-dcda0b8d0317
-- title:
--   Packed5591 Character — sensitivity certificate definitions
-- statement:
--   The definitions for Packed5591 Character in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.base_bit_character`, `Sensitivity5591Labeling.sub_val_mod`, `Sensitivity5591Labeling.out_bit_adj`, `Sensitivity5591Labeling.base_bit_adj`, `Sensitivity5591Labeling.intersection_bit_adj`, `Sensitivity5591Labeling.pow_val`, `Sensitivity5591Labeling.euler_iff`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Packed5591Character.lean, lines 1–80.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Packed5591Checks
import Definitions.Def_Sensitivity213981Formal_Packed5591Rotation
import Definitions.Def_Sensitivity213981Formal_Paley5591
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
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
/- Certified sparse-word calculations imply actual Paley triple geometry. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option Elab.async false
set_option maxRecDepth 200000
set_option exponentiation.threshold 200000
namespace Sensitivity5591Labeling
open Sensitivity10007Labeling ZL ThreeBoundPackedBits Sensitivity5591Packed
open scoped Classical BigOperators
noncomputable section
attribute [local irreducible] core base out intersection euler

theorem pow_val(v:Vertex)(k:ℕ):(v^k).val=v.val^k%5591 := by
  calc
    (v^k).val=((v.val:Vertex)^k).val:=by rw [ZMod.natCast_zmod_val]
    _=((v.val^k:ℕ):Vertex).val:=by rw [Nat.cast_pow]
    _=_:=ZMod.val_natCast 5591 (v.val^k)


theorem euler_iff(v:Vertex):quadraticChar Vertex v=1↔euler v.val=1 := by
  have hp:(v^2795).val=euler v.val := by
    unfold euler
    exact pow_val v 2795
  have he:(v^2795=1)↔euler v.val=1 := by
    constructor
    · intro h
      have hh:=congrArg ZMod.val h
      simpa only [hp,ZMod.val_one] using hh
    · intro h
      apply ZMod.val_injective 5591
      simpa only [hp,ZMod.val_one] using h
  by_cases hv:v=0
  · subst v
    simp [euler]
  · rw [quadraticChar_eq_pow_of_char_ne_two characteristic_ne_two hv,card_vertex]
    norm_num only [show (5591:ℕ)/2=2795 by decide]
    by_cases hh:v^2795=1
    · simp [hh,he.mp hh]
    · have hn:¬euler v.val=1:=fun h=>hh (he.mpr h)
      simp [hh,hn]

theorem base_bit_character(v:Vertex):
    base.testBit (16*v.val)=decide (quadraticChar Vertex v=1) := by
  rw [←euler_correct ⟨v.val,v.val_lt⟩]
  exact Bool.decide_congr (euler_iff v).symm

theorem sub_val_mod(v y:Vertex):(y-v).val=(y.val+5591-v.val)%5591 := by
  have hlt:=v.val_lt
  have he:((y.val+5591-v.val:ℕ):Vertex)=y-v := by
    rw [Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_self,
      ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,add_zero]
  have h:=congrArg ZMod.val he
  simpa only [ZMod.val_natCast] using h.symm

theorem out_bit_adj(v y:Vertex):
    (out v.val).testBit (16*y.val)=decide (Adj v y) := by
  have hr:=out_bit v.val y.val v.val_lt y.val_lt
  have hc:=base_bit_character (y-v)
  rw [sub_val_mod v y] at hc
  exact hr.trans (hc.trans (Bool.decide_congr (adj_character v y).symm))

theorem base_bit_adj(y:Vertex):base.testBit (16*y.val)=decide (Adj 0 y) :=
  (base_bit_character y).trans (Bool.decide_congr (by simpa only [sub_zero] using (adj_character 0 y).symm))

theorem intersection_bit_adj(v y:Vertex):
    (intersection v.val).testBit (16*y.val)=decide ((Adj 0 y∧Adj 1 y)∧Adj v y) := by
  have h0:=base_bit_adj y
  have h1:(out 1).testBit (16*y.val)=decide (Adj 1 y):=out_bit_adj 1 y
  have hv:=out_bit_adj v y
  unfold intersection
  rw [Nat.testBit_and,Nat.testBit_and,h0,h1,hv]
  simp only [Bool.decide_and]


end
end Sensitivity5591Labeling


end
end Sensitivity213981Formal


