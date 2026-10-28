-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
-- name    : Sensitivity213981Formal_RankCoefficientDominance
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:56:35.414138+00:00
-- url     : https://prove2.me/theorems/85e5284d-aa62-4b02-9b99-80dbcdb110b8
-- title:
--   Rank Coefficient Dominance — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Coefficient Dominance in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankAnnotated.CoefficientLe`, `ThreeBoundRankAnnotated.MaskLe`, `ThreeBoundRankAnnotated.instDecidableMaskLe`, `ThreeBoundRankAnnotated.instDecidableCoefficientLe`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankCoefficientDominance.lean, lines 1–119.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
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
/- Reuse an exact record certificate when every normalized cost decreases. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundRankAnnotated
open ThreeBoundRankCached ThreeBoundRankNumeric
open ThreeBoundEndpoint22Records

structure CoefficientLe (q : ℕ) (x y : CostValues) (a b : ℕ) : Prop where
  heads : ∀ k : Fin 33, x.heads.getD k.val 0*b≤ y.heads.getD k.val 0*a
  guard : x.guard*b≤ y.guard*a
  converted : x.converted*b≤ y.converted*a
  negative : ∀ k : Fin (q+1), x.negative.getD k.val 0*b≤ y.negative.getD k.val 0*a

instance _root_.Sensitivity213981Formal.ThreeBoundRankAnnotated.instDecidableCoefficientLe (q : ℕ) (x y : CostValues) (a b : ℕ) : Decidable (CoefficientLe q x y a b) :=
  decidable_of_iff
    ((∀ k : Fin 33, x.heads.getD k.val 0*b≤ y.heads.getD k.val 0*a) ∧
      x.guard*b≤ y.guard*a ∧ x.converted*b≤ y.converted*a ∧
      ∀ k : Fin (q+1), x.negative.getD k.val 0*b≤ y.negative.getD k.val 0*a)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,
      fun h => ⟨h.heads,h.guard,h.converted,h.negative⟩⟩







def MaskLe (small large : Array Bool) : Prop :=
  ∀ k : Fin 11, small.getD k.val false=true → large.getD k.val false=true

instance _root_.Sensitivity213981Formal.ThreeBoundRankAnnotated.instDecidableMaskLe (small large : Array Bool) : Decidable (MaskLe small large) := by
  unfold MaskLe
  infer_instance







end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal


