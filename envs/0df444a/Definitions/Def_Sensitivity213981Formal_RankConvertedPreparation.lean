-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankConvertedPreparation
-- name    : Sensitivity213981Formal_RankConvertedPreparation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:35:16.122999+00:00
-- url     : https://prove2.me/theorems/0facfa52-8900-4c26-8188-2dd9e51e8551
-- title:
--   Rank Converted Preparation — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Converted Preparation in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankCached.convertedSuffix`, `ThreeBoundRankCached.convertedNegative`, `ThreeBoundRankCached.preparedFromConverted`, `ThreeBoundRankCached.ConvertedValues`, `ThreeBoundRankCached.readConverted`, `ThreeBoundRankCached.ConvertedOK`, `ThreeBoundRankCached.instDecidableConvertedOK`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankConvertedPreparation.lean, lines 1–99.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankStaticPreparation
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
/- Each static record needs only four converted caps per external-arc count.
The q-specific greedy increments are then computed from these small arrays. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Caps interval )
open ThreeBoundRankNumeric

structure ConvertedValues where
  feasible : Array Bool
  converted : Array (Array ℕ)
  deriving Repr

def readConverted (values : ConvertedValues) (e k : ℕ) : ℕ :=
  (values.converted.getD e #[]).getD k 0

def ConvertedOK (caps : Caps) (perfect : ℕ) (r : Record) (values : ConvertedValues) : Prop :=
  (∀ q : Fin 4, values.feasible.getD q.val false=staticAllowed caps q.val r) ∧
  (∀ e : Fin (r 11+1), ∀ k : Fin 4,
    readConverted values e.val k.val=convertedCap caps perfect r e.val k.val)

instance _root_.Sensitivity213981Formal.ThreeBoundRankCached.instDecidableConvertedOK (caps : Caps) (perfect : ℕ) (r : Record) (values : ConvertedValues) :
    Decidable (ConvertedOK caps perfect r values) := by unfold ConvertedOK; infer_instance



def convertedSuffix (values : ConvertedValues) (q e k : ℕ) : ℕ :=
  ((interval k (q+1)).map fun j => readConverted values e j).foldl min (readConverted values e q)

def convertedNegative (values : ConvertedValues) (q e k : ℕ) : ℕ :=
  if k=0 then convertedSuffix values q e 0 else
    convertedSuffix values q e k-convertedSuffix values q e (k-1)

def preparedFromConverted (q external : ℕ) (values : ConvertedValues) : PreparedValues where
  feasible := values.feasible.getD q false
  negative := Array.ofFn fun e : Fin (external+1) =>
    Array.ofFn fun k : Fin (q+1) => convertedNegative values q e.val k.val















end ThreeBoundRankCached




end
end Sensitivity213981Formal


