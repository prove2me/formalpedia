-- Prove2me | Definitions.Def_Sensitivity213981Formal_Paley5591
-- name    : Sensitivity213981Formal_Paley5591
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:05:02.27948+00:00
-- url     : https://prove2.me/theorems/ff1584e1-3c4f-4928-8453-d3e4f8e46e6f
-- title:
--   Paley5591 — sensitivity certificate definitions
-- statement:
--   The definitions for Paley5591 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.edge_compl`, `Sensitivity5591Labeling.outdegree`, `Sensitivity5591Labeling.indegree`, `Sensitivity5591Labeling.common_out`, `Sensitivity5591Labeling.common_in`, `Sensitivity5591Labeling.affine`, `Sensitivity5591Labeling.affine_apply`, `Sensitivity5591Labeling.affine_adj`, `Sensitivity5591Labeling.arc_transitive`, `Sensitivity5591Labeling.instFactPrimeOfNatNat_paley5591`, `Sensitivity5591Labeling.Vertex`, `Sensitivity5591Labeling.characteristic_ne_two`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Paley5591.lean, lines 1–99.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Paley10007
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
/- Paley-5591 geometry and explicit affine transitivity on directed edges. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Sensitivity5591Labeling
open Sensitivity10007Labeling
open CompactDRT
open scoped Classical BigOperators
noncomputable section

instance _root_.Sensitivity213981Formal.Sensitivity5591Labeling.instFactPrimeOfNatNat_paley5591 : Fact (Nat.Prime 5591) := ⟨by norm_num⟩

abbrev Vertex := ZMod 5591

theorem characteristic_ne_two : ringChar Vertex≠2 := by norm_num [ZMod.ringChar_zmod_n]

theorem negative_one : quadraticChar Vertex (-1)=-1 := by
  rw [quadraticChar_neg_one characteristic_ne_two,ZMod.card]
  decide +kernel

def core : Core Vertex := paleyCore characteristic_ne_two negative_one
attribute [local irreducible] core

abbrev Adj := core.Adj

theorem adj_character (x y : Vertex) : Adj x y ↔ quadraticChar Vertex (y-x)=1 := by
  unfold Adj core Core.Adj paleyCore
  rfl

theorem card_vertex : Fintype.card Vertex=5591 := ZMod.card 5591

theorem irreflexive (x : Vertex) : ¬Adj x x := core.irreflexive x

theorem edge_compl (x y : Vertex) (hxy : x≠y) : Adj x y ↔ ¬Adj y x :=
  ⟨core.asymmetric x y,fun hn=>(core.oriented x y hxy).resolve_right hn⟩

theorem outdegree (x : Vertex) : (Finset.univ.filter (Adj x)).card=2795 := by
  have h := core.degree_identity x
  rw [card_vertex] at h
  change 2 * ((Finset.univ.filter (Adj x)).card : ℤ) = _ at h
  omega

theorem indegree (x : Vertex) : (Finset.univ.filter fun z=>Adj z x).card=2795 := by
  have h := core.in_degree_identity x
  rw [card_vertex] at h
  change 2 * ((Finset.univ.filter fun z=>Adj z x).card : ℤ) = _ at h
  omega

theorem common_out (x y : Vertex) (hxy : x≠y) :
    (Finset.univ.filter fun z=>Adj x z ∧ Adj y z).card=1397 := by
  have h := core.common_identity x y hxy
  rw [card_vertex] at h
  change 4 * ((Finset.univ.filter fun z=>Adj x z ∧ Adj y z).card : ℤ) = _ at h
  omega

theorem common_in (x y : Vertex) (hxy : x≠y) :
    (Finset.univ.filter fun z=>Adj z x ∧ Adj z y).card=1397 := by
  have h := core.common_in_identity x y hxy
  rw [card_vertex] at h
  change 4 * ((Finset.univ.filter fun z=>Adj z x ∧ Adj z y).card : ℤ) = _ at h
  omega

def affine (a b : Vertex) (ha : a≠0) : Vertex≃Vertex :=
  (Equiv.mulLeft₀ a ha).trans (Equiv.addRight b)

@[simp] theorem affine_apply (a b : Vertex) (ha : a≠0) (x : Vertex) :
    affine a b ha x=a*x+b := rfl

theorem affine_adj (a b : Vertex) (ha : a≠0) (hsq : quadraticChar Vertex a=1)
    (x y : Vertex) : Adj (affine a b ha x) (affine a b ha y) ↔ Adj x y := by
  rw [adj_character,adj_character,affine_apply,affine_apply]
  rw [show a*y+b-(a*x+b)=a*(y-x) by ring,map_mul,hsq,one_mul]

theorem arc_transitive (x y u v : Vertex) (hxy : Adj x y) (huv : Adj u v) :
    ∃ e : Vertex≃Vertex, e x=u ∧ e y=v ∧ ∀ a b, Adj (e a) (e b) ↔ Adj a b := by
  have hyx : y-x≠0 := sub_ne_zero.mpr (by intro h; subst y; exact irreflexive x hxy)
  have hvu : v-u≠0 := sub_ne_zero.mpr (by intro h; subst v; exact irreflexive u huv)
  let t := (v-u)/(y-x)
  have ht : t≠0 := div_ne_zero hvu hyx
  have hprod : t*(y-x)=v-u := by dsimp [t]; exact div_mul_cancel₀ _ hyx
  have htχ : quadraticChar Vertex t=1 := by
    have h := congrArg (quadraticChar Vertex) hprod
    rw [map_mul,(adj_character x y).mp hxy,(adj_character u v).mp huv,mul_one] at h
    exact h
  refine ⟨affine t (u-t*x) ht,?_,?_,affine_adj t (u-t*x) ht htχ⟩
  · rw [affine_apply]; ring
  · rw [affine_apply]
    calc
      t*y+(u-t*x)=t*(y-x)+u := by ring
      _=v := by rw [hprod]; ring

end
end Sensitivity5591Labeling




end
end Sensitivity213981Formal


