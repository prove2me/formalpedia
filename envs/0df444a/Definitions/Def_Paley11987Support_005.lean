-- Prove2me | Definitions.Def_Paley11987Support_005
-- name    : Paley11987Support_005
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:39:53.139991+00:00
-- url     : https://prove2.me/theorems/1bbf02d2-b52a-4e2d-98f9-5110303864ae
-- title:
--   Supported bad-event families
-- statement:
--   Defines finite supported families of bad events, their local assignments and index types, complement operations, atom weights, and local probabilities. Necessary constructor and finite-type helpers are included.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabelingAtomization.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingAtomization, SHA256 9936eab61ef233246147dc5f49aa5aa70cc8b76e3d63e6582da01d14cea22c13

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

set_option autoImplicit false
set_option Elab.async false
section z7

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

open CompactAtomicLLL

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

structure SupportedFamily (V D : Type*) [DecidableEq V] where
  support : D → Finset V
  bad : D → (V → Fin 2) → Prop
  locality : ∀ d x y, (∀ v ∈ support d, x v = y v) → (bad d x ↔ bad d y)
  complement : ∀ d x, bad d (fun v => (x v).rev) ↔ bad d x

namespace SupportedFamily

variable (F : SupportedFamily V D)

def extend (d : D) (u : F.support d → Fin 2) : V → Fin 2 :=
  fun v => if hv : v ∈ F.support d then u ⟨v,hv⟩ else 0

def LocalBad (d : D) := {u : F.support d → Fin 2 // F.bad d (F.extend d u)}

def Index := Σ d : D, F.LocalBad d

instance localBadFintype (d : D) : Fintype (F.LocalBad d) := by
  unfold LocalBad
  infer_instance

instance indexFintype : Fintype F.Index := by
  unfold Index
  infer_instance

def atom (i : F.Index) : Atom V := ⟨F.support i.1, F.extend i.1 i.2.val⟩



theorem bad_restrict (d : D) (ell : V → Fin 2) :
    F.bad d (F.extend d (fun v => ell v.val)) ↔ F.bad d ell := by
  apply F.locality
  intro v hv
  simp only [extend, dif_pos hv]

def complementLocal (d : D) (u : F.LocalBad d) : F.LocalBad d :=
  ⟨fun v => (u.val v).rev, by
    have hc := (F.complement d (F.extend d u.val)).mpr u.property
    apply (F.locality d _ _ ?_).mp hc
    intro v hv
    simp only [extend, dif_pos hv]⟩

def complementIndex (i : F.Index) : F.Index := ⟨i.1,F.complementLocal i.1 i.2⟩

theorem complementIndex_involutive : Function.Involutive F.complementIndex := by
  rintro ⟨d,u⟩
  apply congrArg (Sigma.mk d)
  apply Subtype.ext
  funext v
  exact Fin.rev_rev (u.val v)

def complementEquiv : F.Index ≃ F.Index :=
  ⟨F.complementIndex,F.complementIndex,F.complementIndex_involutive,F.complementIndex_involutive⟩







def atomWeight (M : D → ℕ) (lam : ℚ) (i : F.Index) : ℚ :=
  (1 / (2 : ℚ) ^ (F.support i.1).card) * lam ^ M i.1

def localProbability (d : D) : ℚ :=
  (Fintype.card (F.LocalBad d) : ℚ) / (2 : ℚ) ^ (F.support d).card







end SupportedFamily
end
end ZL
end
end z7


