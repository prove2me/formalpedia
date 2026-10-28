-- Prove2me | Definitions.Def_Sensitivity213981Formal_Packed5591Geometry
-- name    : Sensitivity213981Formal_Packed5591Geometry
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:28:08.076133+00:00
-- url     : https://prove2.me/theorems/36191167-8ae8-4df3-9596-98058d34f924
-- title:
--   Packed5591 Geometry — sensitivity certificate definitions
-- statement:
--   The definitions for Packed5591 Geometry in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.normalized_card`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Packed5591Geometry.lean, lines 1–39.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Packed5591Character
import Definitions.Def_Sensitivity213981Formal_PackedBitCard
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
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
/- Certified sparse words give the normalized Paley triple bound. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace Sensitivity5591Labeling
open Sensitivity10007Labeling ZL ThreeBoundPackedBits Sensitivity5591Packed
open scoped Classical BigOperators
noncomputable section
attribute [local irreducible] core base out intersection euler

theorem normalized_card(v:Vertex)(hv0:v≠0)(hv1:v≠1):
    (Finset.univ.filter fun y=>Adj 0 y∧Adj 1 y∧Adj v y).card≤ 800 := by
  have hvzero:v.val≠0 := by
    intro h
    apply hv0
    rw [←ZMod.natCast_zmod_val v,h]
    rfl
  have hvone:v.val≠1 := by
    intro h
    apply hv1
    rw [←ZMod.natCast_zmod_val v,h]
    rfl
  have hv:2≤ v.val:=by omega
  have hc:(Finset.univ.filter fun y=>Adj 0 y∧Adj 1 y∧Adj v y).card=
      bitSum 5591 (intersection v.val) := by
    apply ThreeBoundPackedBits.filter_card_bits (ZMod.finEquiv 5591).toEquiv
    intro y
    have hh:=intersection_bit_adj v ((ZMod.finEquiv 5591).toEquiv y)
    have he:((ZMod.finEquiv 5591).toEquiv y).val=y.val:=rfl
    rw [he] at hh
    exact hh.trans (Bool.decide_congr and_assoc)
  rw [hc,bitSum_eq_mod 5591 (intersection v.val) (by decide) (intersection_mask v.val)]
  exact intersection_bound ⟨v.val,v.val_lt⟩ hv

end
end Sensitivity5591Labeling


end
end Sensitivity213981Formal


