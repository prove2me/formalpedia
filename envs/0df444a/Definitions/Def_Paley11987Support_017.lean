-- Prove2me | Definitions.Def_Paley11987Support_017
-- name    : Paley11987Support_017
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:58:48.972723+00:00
-- url     : https://prove2.me/theorems/4e47be35-c35f-4af0-996b-131f9c35af8f
-- title:
--   Unions of supported event families
-- statement:
--   Defines the indexed union of supported bad-event families used to impose their exclusions simultaneously.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabelingUnion.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingUnion, SHA256 65f0e23a5ebdbb568580935811dd6e892ff5ce6413076c9de099ef802d053fbe

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

set_option autoImplicit false
set_option Elab.async false
section z27

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL.SupportedFamily
noncomputable section
variable {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T]
variable {D : T → Type*} [∀ t, Fintype (D t)]

def iUnion (F : ∀ t, ZL.SupportedFamily V (D t)) :
    ZL.SupportedFamily V (Σ t, D t) where
  support i := (F i.1).support i.2
  bad i ell := (F i.1).bad i.2 ell
  locality i ell ell' h := (F i.1).locality i.2 ell ell' h
  complement i ell := (F i.1).complement i.2 ell





end
end ZL.SupportedFamily
end
end z27


