-- Prove2me | Definitions.Def_Paley11987Support_018
-- name    : Paley11987Support_018
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:59:24.620987+00:00
-- url     : https://prove2.me/theorems/0f91003d-7aba-4cb0-b289-48284c5e9580
-- title:
--   The joint exclusion system at order 11987
-- statement:
--   Defines the finite family types, their description sets, exponents, ceilings, and the joint exclusion predicate for all recorded labeling constraints.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabeling11987Joint.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabeling11987Joint, SHA256 f43609b027676880501481b9bb66e7b84f6e7ae90b71f42a2ecfa8241cd76fcf

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

set_option autoImplicit false
set_option Elab.async false
section z28

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped Classical BigOperators
noncomputable section

namespace CompactLabeling11987
open ZL ZL.RowCounting
attribute [local irreducible] N degree common lam
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev FamilyKind := Fin 9 ⊕ (Fin 12 ⊕ Bool)

def Description (R : V → V → Prop) : FamilyKind → Type _
  | .inl q => OrdinaryIndex V (ordinaryA q)
  | .inr (.inl i) => MarkedIndex V (marked i).a (marked i).m
  | .inr (.inr false) => SourceIndex R 21
  | .inr (.inr true) => DominatorIndex R 18

instance descriptionFintype (R : V → V → Prop) (t : FamilyKind) : Fintype (Description R t) := by
  rcases t with q | i | b
  · exact ordinaryIndexFintype (ordinaryA q)
  · exact markedIndexFintype (marked i).a (marked i).m
  · cases b
    · exact sourceIndexFintype R 21
    · exact dominatorIndexFintype R 18

def family (R : V → V → Prop) : (t : FamilyKind) → SupportedFamily (V × V) (Description R t)
  | .inl q => ordinaryFamily R q.val (ordinaryA q)
  | .inr (.inl i) => markedFamily R (marked i).q (marked i).a (marked i).m (marked i).B
  | .inr (.inr false) => sourceFamily R 21
  | .inr (.inr true) => dominatorFamily R 18

def exponent : FamilyKind → ℕ
  | .inl q => (ordinaryA q).choose 2
  | .inr (.inl i) => (marked i).a.choose 2+(marked i).m*(marked i).a
  | .inr (.inr false) => 231
  | .inr (.inr true) => 189

def lowerExponent : FamilyKind → ℕ
  | .inl q => (ordinaryA q).choose 2
  | .inr (.inl i) => (marked i).a.choose 2
  | .inr (.inr false) => 231
  | .inr (.inr true) => 189

def ceiling : FamilyKind → ℚ
  | .inl q => ordinaryCeiling q
  | .inr (.inl i) => markedCeiling i
  | .inr (.inr false) => sourceCeiling
  | .inr (.inr true) => dominatorCeiling

structure JointExclusions (R : V → V → Prop) (ell : V × V → Fin 2) : Prop where
  ordinary : ∀ (q : Fin 9) (I : OrdinaryIndex V (ordinaryA q)),
    ¬ (ordinaryFamily R q.val (ordinaryA q)).bad I ell
  marked : ∀ (i : Fin 12) (I : MarkedIndex V (marked i).a (marked i).m),
    ¬ (markedFamily R (marked i).q (marked i).a (marked i).m (marked i).B).bad I ell
  source : ∀ I : SourceIndex R 21, ¬ (sourceFamily R 21).bad I ell
  dominator : ∀ I : DominatorIndex R 18, ¬ (dominatorFamily R 18).bad I ell



















end CompactLabeling11987
end
end z28


