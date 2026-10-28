-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankSummarizedConverted
-- name    : Sensitivity213981Formal_RankSummarizedConverted
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:43:20.867018+00:00
-- url     : https://prove2.me/theorems/af275e8a-ed51-454d-a480-d045b442a0e5
-- title:
--   Rank Summarized Converted — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Summarized Converted in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankCached.ConvertedFastOK`, `ThreeBoundRankCached.instDecidableConvertedFastOK`, `ThreeBoundRankCached.convertedFastCheck`, `ThreeBoundRankCached.ConvertedSummary`, `ThreeBoundRankCached.summarizedConvertedCheck`, `ThreeBoundRankCached.SummaryOK`, `ThreeBoundRankCached.instDecidableSummaryOK`, `ThreeBoundRankCached.summaryCheck`, `ThreeBoundRankCached.fastConverted`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankSummarizedConverted.lean, lines 1–90.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankConvertedPreparation
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
/- Prefix caps are certified once per static key and reused for every external count. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Caps)
open ThreeBoundRankNumeric

structure ConvertedSummary where
  base : Array ℕ
  guard : ℕ
  deriving Repr

def SummaryOK (caps : Caps) (r : Record) (summary : ConvertedSummary) : Prop :=
  summary.guard=guardCount r ∧ ∀ q : Fin 4,
    let cp := capPrefix caps r q.val
    let pp := positivePrefix r q.val
    summary.base.getD q.val 0=cp-pp ∧ pp ≤  cp

instance _root_.Sensitivity213981Formal.ThreeBoundRankCached.instDecidableSummaryOK (caps : Caps) (r : Record) (summary : ConvertedSummary) : Decidable (SummaryOK caps r summary) := by
  unfold SummaryOK
  infer_instance

def summaryCheck (caps : Caps) (r : Record) (summary : ConvertedSummary) : Bool :=
  decide (SummaryOK caps r summary)

def fastConverted (caps : Caps) (perfect : ℕ) (summary : ConvertedSummary) (e q : ℕ) : ℕ :=
  let c0 := summary.base.getD q 0
  let c1 := tighten c0 (caps.pcross+allowance 1 e (summary.guard)) (q=0 ∧ 1 ≤  summary.guard)
  let c2 := tighten c1 (Caps.at caps.zero 2+allowance 2 e (summary.guard)) (q=0 ∧ 2 ≤  summary.guard)
  let c3 := tighten c2 (perfect+allowance 3 e (summary.guard)) (q=0 ∧ 3 ≤  summary.guard)
  let c4 := tighten c3 (Caps.at caps.marked 6-1+allowance 3 e (summary.guard)) (q=1 ∧ 3 ≤  summary.guard)
  let c5 := tighten c4 (Caps.at caps.marked 7-1+allowance 4 e (summary.guard)) (q=2 ∧ 4 ≤  summary.guard)
  let c6 := tighten c5 (Caps.at caps.marked 8-1+allowance 5 e (summary.guard)) (q=3 ∧ 5 ≤  summary.guard)
  let c7 := tighten c6 (Caps.at caps.marked 9-1+allowance 6 e (summary.guard)) (q=3 ∧ 6 ≤  summary.guard)
  let c8 := tighten c7 (Caps.at caps.marked 11-1+allowance 7 e (summary.guard)) (q=3 ∧ 7 ≤  summary.guard)
  c8





def ConvertedFastOK (caps : Caps) (perfect external : ℕ) (summary : ConvertedSummary)
    (values : ConvertedValues) : Prop :=
  (∀ q : Fin 4, values.feasible.getD q.val false=true) ∧
  ∀ e : Fin (external+1), ∀ q : Fin 4,
    readConverted values e.val q.val=fastConverted caps perfect summary e.val q.val

instance _root_.Sensitivity213981Formal.ThreeBoundRankCached.instDecidableConvertedFastOK (caps : Caps) (perfect external : ℕ) (summary : ConvertedSummary) (values : ConvertedValues) :
    Decidable (ConvertedFastOK caps perfect external summary values) := by unfold ConvertedFastOK; infer_instance

def convertedFastCheck (caps : Caps) (perfect external : ℕ) (summary : ConvertedSummary)
    (values : ConvertedValues) : Bool := decide (ConvertedFastOK caps perfect external summary values)

def summarizedConvertedCheck (caps : Caps) (perfect : ℕ) (r : Record) (summary : ConvertedSummary)
    (values : ConvertedValues) : Bool :=
  summaryCheck caps r summary && convertedFastCheck caps perfect (r 11) summary values





end ThreeBoundRankCached



end
end Sensitivity213981Formal


