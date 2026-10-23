-- Prove2me | Definitions.Def_Paley11987Support_003
-- name    : Paley11987Support_003
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:38:15.048843+00:00
-- url     : https://prove2.me/theorems/f9798ba7-0fc0-4b33-b9ab-653fb265e537
-- title:
--   Atomic local events
-- statement:
--   Defines supported coordinate assignments, their occurrence and conflict predicates, overwrite operations, and conflict neighborhoods for the atomic local lemma.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module AtomicLopsidedLocality.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module AtomicLopsidedLocality, SHA256 69538a98eb59f2c46d0f2612d59e2b873cf5d42171769587f21e44fa3cb8f627

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

set_option autoImplicit false
set_option Elab.async false
section z3

section

set_option maxHeartbeats 4000000
open scoped Classical BigOperators

namespace CompactAtomicLLL

noncomputable section

open SensitivityLabelCache12607.SensitivityLLL

variable {V E : Type*} [Fintype V] [DecidableEq V]

structure Atom (V : Type*) where
  support : Finset V
  value : V → Fin 2

def Holds (a : Atom V) (x : V → Fin 2) : Prop :=
  ∀ v ∈ a.support, x v = a.value v

def event (a : Atom V) : Finset (V → Fin 2) :=
  Finset.univ.filter (Holds a)



def Conflict (a b : Atom V) : Prop :=
  ∃ v ∈ a.support, v ∈ b.support ∧ a.value v ≠ b.value v

def overwrite (a : Atom V) (x : V → Fin 2) (u : a.support → Fin 2) : V → Fin 2 :=
  fun v => if hv : v ∈ a.support then u ⟨v, hv⟩ else x v







def neighbors [Fintype E] (atoms : E → Atom V) (i : E) : Finset E :=
  Finset.univ.filter fun j => Conflict (atoms i) (atoms j)



end

end CompactAtomicLLL
end
end z3


