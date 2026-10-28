-- Prove2me | Definitions.Def_Sensitivity213981Formal_Paley5591Triple
-- name    : Sensitivity213981Formal_Paley5591Triple
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:28:46.460663+00:00
-- url     : https://prove2.me/theorems/c22dbbb9-9bb4-44f3-b3b0-d6ee1cab1e49
-- title:
--   Paley5591 Triple — sensitivity certificate definitions
-- statement:
--   The definitions for Paley5591 Triple in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.triple_card_of_arc`, `Sensitivity5591Labeling.triple_common_out`, `Sensitivity5591Labeling.dominatedBy_map`, `Sensitivity5591Labeling.normalized_dominated`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Paley5591Triple.lean, lines 1–58.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Packed5591Geometry
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
/- Affine normalization upgrades the certified word check to every marker triple. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Sensitivity5591Labeling
open Sensitivity10007Labeling ZL
open scoped Classical
noncomputable section

theorem dominatedBy_map(e:Vertex≃Vertex)
    (hR:∀x y,Adj (e x) (e y)↔Adj x y)(M:Finset Vertex):
    dominatedBy Adj (M.map e.toEmbedding)=(dominatedBy Adj M).map e.toEmbedding := by
  ext y
  obtain ⟨y,rfl⟩:=e.surjective y
  simp only [dominatedBy,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_map_equiv,Equiv.symm_apply_apply]
  constructor
  · intro h x hx
    exact (hR x y).mp (h (e x) (by simpa only [Equiv.symm_apply_apply] using hx))
  · intro h x hx
    obtain ⟨x,rfl⟩:=e.surjective x
    have hx':x∈M:=by simpa only [Finset.mem_map_equiv,Equiv.symm_apply_apply] using hx
    exact (hR x y).mpr (h x hx')

theorem normalized_dominated(v:Vertex)(hv0:v≠0)(hv1:v≠1):
    (dominatedBy Adj {0,1,v}).card≤ 800 := by
  have he:dominatedBy Adj {0,1,v}=
      Finset.univ.filter (fun y=>Adj 0 y∧Adj 1 y∧Adj v y) := by
    ext y
    simp [dominatedBy]
  rw [he]
  exact normalized_card v hv0 hv1

theorem triple_card_of_arc(x y z:Vertex)(hxy:Adj x y)(hxz:x≠z)(hyz:y≠z):
    (dominatedBy Adj {x,y,z}).card≤ 800 := by
  have h01:Adj 0 1 := by rw [adj_character]; simp
  obtain ⟨e,hx,hy,hR⟩:=arc_transitive x y 0 1 hxy h01
  have hz0:e z≠0:=fun hz=>hxz (e.injective (hx.trans hz.symm))
  have hz1:e z≠1:=fun hz=>hyz (e.injective (hy.trans hz.symm))
  have hc:=congrArg Finset.card (dominatedBy_map e hR {x,y,z})
  rw [Finset.card_map] at hc
  calc
    _=(dominatedBy Adj (({x,y,z}:Finset Vertex).map e.toEmbedding)).card:=hc.symm
    _=(dominatedBy Adj {0,1,e z}).card:=by
      simp only [Finset.map_insert,Finset.map_singleton,Equiv.toEmbedding_apply,hx,hy]
    _≤ 800:=normalized_dominated (e z) hz0 hz1

theorem triple_common_out(M:Finset Vertex)(hm:M.card=3):
    (dominatedBy Adj M).card≤ 800 := by
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩:=Finset.card_eq_three.mp hm
  by_cases h:Adj x y
  · exact triple_card_of_arc x y z h hxz hyz
  · rw [Finset.insert_comm x y]
    exact triple_card_of_arc y x z ((edge_compl y x hxy.symm).mpr h) hyz hxz

end
end Sensitivity5591Labeling


end
end Sensitivity213981Formal


