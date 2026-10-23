-- Prove2me | Definitions.Def_Paley11987Support_030
-- name    : Paley11987Support_030
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:33:20.794543+00:00
-- url     : https://prove2.me/theorems/9aa4802d-70c5-4716-af0c-f9f1f1ecd164
-- title:
--   Labeling caps and total candidate caps
-- statement:
--   Defines the complete labeling-cap predicate and the explicit candidate-total-cap function used for tolerances from one through eight.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module BooleanTransferPositiveCaps.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferPositiveCaps, SHA256 2c8ec868e5f366da81fde081552a9cff6ed3903651a0815c70ec9936b35774cf

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
import Definitions.Def_Paley11987Support_000
import Definitions.Def_Paley11987Support_001
import Definitions.Def_Paley11987Support_002
import Definitions.Def_Paley11987Support_003
import Definitions.Def_Paley11987Support_004
import Definitions.Def_Paley11987Support_005
import Definitions.Def_Paley11987Support_006
import Definitions.Def_Paley11987Support_007
import Definitions.Def_Paley11987Support_008
import Definitions.Def_Paley11987Support_009
import Definitions.Def_Paley11987Support_010
import Definitions.Def_Paley11987Support_011
import Definitions.Def_Paley11987Support_012
import Definitions.Def_Paley11987Support_013
import Definitions.Def_Paley11987Support_014
import Definitions.Def_Paley11987Support_015
import Definitions.Def_Paley11987Support_016
import Definitions.Def_Paley11987Support_017
import Definitions.Def_Paley11987Support_018
import Definitions.Def_Paley11987Support_019
import Definitions.Def_Paley11987Support_020
import Definitions.Def_Paley11987Support_021
import Definitions.Def_Paley11987Support_022
import Definitions.Def_Paley11987Support_023
import Definitions.Def_Paley11987Support_024
import Definitions.Def_Paley11987Support_025
import Definitions.Def_Paley11987Support_026
import Definitions.Def_Paley11987Support_027
import Definitions.Def_Paley11987Support_028
import Definitions.Def_Paley11987Support_029

set_option autoImplicit false
set_option Elab.async false
section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

structure LabelCaps (T : Tournament k) (label : Fin k → Fin k → Fin 2) : Prop where
  ordinary : ∀ q, q ≤ 8 → DefectBound T label q (cutoff q)
  source : SensitivitySourceZero.SourceBound T label 22
  double : DoubleCardBound T label 18
  one : ∀ q, 1 ≤ q → q ≤ 4 → MarkedCardBound T label q 1 0 (q+1) (guardCap q+1)
  two_one : MarkedCardBound T label 1 2 0 4 28
  two_two : MarkedCardBound T label 2 2 0 6 34
  zero_one_three : MarkedCardBound T label 1 3 0 0 24
  zero_two_four : MarkedCardBound T label 2 4 0 0 29
  zero_three_five : MarkedCardBound T label 3 5 0 0 32
  zero_three_six : MarkedCardBound T label 3 6 0 0 30
  zero_four_six : MarkedCardBound T label 4 6 0 0 35
  zero_three_seven : MarkedCardBound T label 3 7 0 0 28

def candidateTotalCap (q m u : ℕ) : ℕ :=
  let t := if m > 0 then min (cutoff q-m) (guardCap q) else cutoff q-1
  let tt := if u > 0 then min t (targetCap q) else t
  let tt := if q=1 ∧ u≥2 then min tt 29 else tt
  let tt := if q=1 ∧ u≥3 then min tt 26 else tt
  let tt := if q=1 ∧ m≥2 then min tt 27 else tt
  if q=2 ∧ m≥2 then min tt 33 else tt





end ZT
end
end z45


