-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22HybridTransfer
-- name    : Sensitivity213981Formal_Endpoint22HybridTransfer
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:29:12.022935+00:00
-- url     : https://prove2.me/theorems/31e5aca0-2715-417f-bc15-7107ebf2adef
-- title:
--   Endpoint22 Hybrid Transfer — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Hybrid Transfer in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Hybrid.SeedBounds`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22HybridTransfer.lean, lines 1–58.

import Definitions.Def_Sensitivity213981Formal_Endpoint22Selected
import Definitions.Def_Sensitivity213981Formal_MinmaxHybridTransfer
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
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
/- The third endpoint needs upward arithmetic only on a covering set of entries. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundEndpoint22Hybrid
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxHybrid
open Sensitivity5591Labeling.Labeling5591
open scoped Classical
noncomputable section
variable {I : Type} [Fintype I]

def SeedBounds (records : List (List ℕ)) (p : Fin 4) (v w : Profile 22)
    (seeds : List (Fin 22 × Fin 22)) : Prop :=
  ∀ pair ∈ seeds, pair.1 ≤  pair.2 ∧
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p pair.1)
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p pair.2)).eval v ≤  w (.a pair.1 pair.2)



end
end ThreeBoundEndpoint22Hybrid



end
end Sensitivity213981Formal


