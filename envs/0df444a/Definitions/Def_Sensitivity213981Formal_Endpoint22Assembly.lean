-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22Assembly
-- name    : Sensitivity213981Formal_Endpoint22Assembly
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:29:33.397303+00:00
-- url     : https://prove2.me/theorems/1bd5f7f9-4c80-482d-9265-31d27a345aff
-- title:
--   Endpoint22 Assembly — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Assembly in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Endpoint22.input`, `ThreeBoundMinmaxNumeric.Endpoint22.rawInput`, `ThreeBoundMinmaxNumeric.Endpoint22.output`, `ThreeBoundMinmaxNumeric.Endpoint22.ClosureBounds`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22Assembly.lean, lines 1–128.

import Definitions.Def_Sensitivity213981Formal_Endpoint22Invariant
import Definitions.Def_Sensitivity213981Formal_Endpoint22Selected
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
/- Four exact scaled stages and reset give the third endpoint's infinite family. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundWitness
open ThreeBoundEndpoint22Selected

def input (p : Fin 4) : Profile 22 :=
  match p.val with | 0 => profile0 | 1 => profile1 | 2 => profile2 | _ => profile3

def rawInput (p : Fin 4) : Profile 22 :=
  match p.val with | 0 => rawProfile0 | 1 => rawProfile1 | 2 => rawProfile2 | _ => rawProfile3

def output (p : Fin 4) : Profile 22 :=
  match p.val with | 0 => profile1 | 1 => profile2 | 2 => profile3 | _ => profile4



def ClosureBounds : Prop :=
  ∀ (p : Fin 4) (I : Type) [Fintype I] (F : Fin 22 → (I → Bool) → Bool), Nested F →
    ∀ c : ℕ, Upper F (scale c (rawInput p)) → Upper F (scale c (output p))















end ThreeBoundMinmaxNumeric.Endpoint22




end
end Sensitivity213981Formal


