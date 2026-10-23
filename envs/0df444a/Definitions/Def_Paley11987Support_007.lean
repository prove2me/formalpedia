-- Prove2me | Definitions.Def_Paley11987Support_007
-- name    : Paley11987Support_007
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:41:49.16598+00:00
-- url     : https://prove2.me/theorems/5e752faf-ff3a-4c02-8ac8-76820c612a3c
-- title:
--   Global assignments for ordinary events
-- statement:
--   Defines gluing local assignments into global bad events, the corresponding equivalence, ordinary row data, head colors, and ordinary assignments.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabelingGlobalCounts.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingGlobalCounts, SHA256 23763adf7b1b9e75414b0facaff25505f3c064c8fd8b03900fbab7fe87b0015f

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

set_option autoImplicit false
set_option Elab.async false
section z9

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

namespace SupportedFamily
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
variable (F : SupportedFamily V D)

def glue (d : D) (u : F.support d → Fin 2) (v : ((F.support d)ᶜ : Finset V) → Fin 2) : V → Fin 2 :=
  fun x => if hx : x ∈ F.support d then u ⟨x,hx⟩ else v ⟨x,Finset.mem_compl.mpr hx⟩

def globalBadEquiv (d : D) :
    {ell : V → Fin 2 // F.bad d ell} ≃ F.LocalBad d × (((F.support d)ᶜ : Finset V) → Fin 2) where
  toFun ell := ⟨⟨fun v => ell.val v.val,(F.bad_restrict d ell.val).mpr ell.property⟩,
    fun v => ell.val v.val⟩
  invFun p := ⟨F.glue d p.1.val p.2, by
    apply (F.locality d (F.extend d p.1.val) _ ?_).mp p.1.property
    intro v hv
    simp only [glue,extend,dif_pos hv]⟩
  left_inv ell := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ F.support d <;> simp [glue,hv]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext v
      simp only [glue,dif_pos v.property]
    · funext v
      simp only [glue,dif_neg (Finset.mem_compl.mp v.property)]






end SupportedFamily

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

open RowCounting

def outgoingRow (A : Finset V) (i : V) : Finset (V × V) :=
  (outOn R A i).image (fun j => (i,j))





def ordinaryRows (A : Finset V) (i : A) : Finset (V × V) := outgoingRow R A i.val



def headColor (A : Finset V) (c : A → Fin 2) (e : V × V) : Fin 2 :=
  if h : e.2 ∈ A then c ⟨e.2,h⟩ else 0

def ordinaryAssignments (A : Finset V) (q : ℕ) : Finset ((V × V) → Fin 2) :=
  Finset.univ.filter (fun ell => OrdinaryBad R ell A q)



end
end ZL
end
end z9


