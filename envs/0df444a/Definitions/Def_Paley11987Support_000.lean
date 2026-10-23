-- Prove2me | Definitions.Def_Paley11987Support_000
-- name    : Paley11987Support_000
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:36:22.737518+00:00
-- url     : https://prove2.me/theorems/8b46348f-fe9b-4e89-9279-eb51e40ef48b
-- title:
--   Tournament incidence sets
-- statement:
--   Defines outgoing and incoming neighbors inside a finite set and the directed internal-edge set of a tournament relation.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabelingGeometry.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingGeometry, SHA256 8e8d158d09002e894af583f60555d6ea75055990434d8de7db7b8c105c681695

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

set_option autoImplicit false
set_option Elab.async false
section z0

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def outOn (R : V → V → Prop) (S : Finset V) (x : V) : Finset V :=
  S.filter (R x)

def inOn (R : V → V → Prop) (S : Finset V) (x : V) : Finset V :=
  S.filter fun y => R y x

def internalEdges (R : V → V → Prop) (S : Finset V) : Finset (V × V) :=
  (S ×ˢ S).filter fun e => R e.1 e.2



























end
end ZL
end
end z0


