-- Prove2me | Definitions.Def_Paley11987Support_006
-- name    : Paley11987Support_006
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:40:52.023031+00:00
-- url     : https://prove2.me/theorems/515500ea-e3d4-48dc-b8eb-7846369aa099
-- title:
--   Ordinary and marked labeling events
-- statement:
--   Defines mismatch counts, ordinary and marked good and bad patterns, coherence, and the two-dominator condition for a binary labeling of a tournament. Complement and restriction identities provide their structural interface.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabelingEvents.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingEvents, SHA256 48995fe241fb52a03fb73161c6b031d3e4d5270be4a7b222f9344f5b3e9c37f7

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

set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def mismatch (R : V → V → Prop) (ell : V × V → Fin 2)
    (S : Finset V) (color : V → Fin 2) (x : V) : Finset V :=
  S.filter fun y => R x y ∧ ell (x,y) ≠ color y

def OrdinaryGood (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (q : ℕ) (color : V → Fin 2) : Prop :=
  ∀ x ∈ A, (mismatch R ell A color x).card ≤ q

def MarkedGood (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) (color : V → Fin 2) : Prop :=
  (∀ x ∈ A, (mismatch R ell A color x).card + (outOn R M x).card ≤ q) ∧
  (∀ y ∈ M, (outOn R M y).card + (mismatch R ell A color y).card ≤
    q + if y ∈ P then 0 else 1) ∧
  (∑ y ∈ M, (mismatch R ell A color y).card) ≤ B

def OrdinaryBad (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (q : ℕ) : Prop := ∃ color, OrdinaryGood R ell A q color

def MarkedBad (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) : Prop := ∃ color, MarkedGood R ell A M P q B color

def crossEdges (R : V → V → Prop) (M A : Finset V) : Finset (V × V) :=
  (M ×ˢ A).filter fun e => R e.1 e.2

def markedSupport (R : V → V → Prop) (A M : Finset V) : Finset (V × V) :=
  internalEdges R A ∪ crossEdges R M A

def Coherent (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M : Finset V) (color : V → Fin 2) : Prop :=
  ∀ e ∈ markedSupport R A M, ell e = color e.2

def TwoDominatorGood (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M : Finset V) (color : V → Fin 2) : Prop :=
  Disjoint A M ∧ M.card = 2 ∧
    (∀ x ∈ M, ∀ y ∈ A, R x y) ∧ Coherent R ell A M color











theorem mismatch_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (color : V → Fin 2) (x : V) :
    mismatch R (fun e => (ell e).rev) A (fun y => (color y).rev) x =
      mismatch R ell A color x := by
  ext y
  simp only [mismatch, Finset.mem_filter]
  constructor
  · rintro ⟨hy,hR,hn⟩
    exact ⟨hy,hR,fun h => hn (congrArg Fin.rev h)⟩
  · rintro ⟨hy,hR,hn⟩
    refine ⟨hy,hR,fun h => hn ?_⟩
    simpa only [Fin.rev_rev] using congrArg Fin.rev h

theorem ordinaryGood_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (q : ℕ) (color : V → Fin 2) :
    OrdinaryGood R (fun e => (ell e).rev) A q (fun y => (color y).rev) ↔
      OrdinaryGood R ell A q color := by
  simp only [OrdinaryGood, mismatch_complement]

theorem markedGood_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) (color : V → Fin 2) :
    MarkedGood R (fun e => (ell e).rev) A M P q B (fun y => (color y).rev) ↔
      MarkedGood R ell A M P q B color := by
  simp only [MarkedGood, mismatch_complement]

theorem ordinaryBad_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (q : ℕ) :
    OrdinaryBad R (fun e => (ell e).rev) A q ↔ OrdinaryBad R ell A q := by
  constructor
  · rintro ⟨color,hcolor⟩
    refine ⟨fun y => (color y).rev, ?_⟩
    have h := (ordinaryGood_complement R (fun e => (ell e).rev) A q color).mpr hcolor
    simpa only [Fin.rev_rev] using h
  · rintro ⟨color,hcolor⟩
    exact ⟨fun y => (color y).rev,(ordinaryGood_complement R ell A q color).mpr hcolor⟩

theorem markedBad_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) :
    MarkedBad R (fun e => (ell e).rev) A M P q B ↔ MarkedBad R ell A M P q B := by
  constructor
  · rintro ⟨color,hcolor⟩
    refine ⟨fun y => (color y).rev, ?_⟩
    have h := (markedGood_complement R (fun e => (ell e).rev) A M P q B color).mpr hcolor
    simpa only [Fin.rev_rev] using h
  · rintro ⟨color,hcolor⟩
    exact ⟨fun y => (color y).rev,(markedGood_complement R ell A M P q B color).mpr hcolor⟩





theorem mismatch_eq_of_agrees (R : V → V → Prop) (ell ell' : V × V → Fin 2)
    (A : Finset V) (color : V → Fin 2) (x : V)
    (h : ∀ y ∈ A, R x y → ell (x,y) = ell' (x,y)) :
    mismatch R ell A color x = mismatch R ell' A color x := by
  ext y
  by_cases hy : y ∈ A
  · by_cases hxy : R x y
    · simp only [mismatch, Finset.mem_filter, hy, hxy, h y hy hxy]
    · simp only [mismatch, Finset.mem_filter, hxy, and_false, false_and]
  · simp only [mismatch, Finset.mem_filter, hy, false_and]

theorem markedGood_congr (R : V → V → Prop) (ell ell' : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) (color : V → Fin 2)
    (heq : ∀ e ∈ markedSupport R A M, ell e = ell' e) :
    MarkedGood R ell A M P q B color ↔ MarkedGood R ell' A M P q B color := by
  have hA (x : V) (hx : x ∈ A) :
      mismatch R ell A color x = mismatch R ell' A color x := by
    apply mismatch_eq_of_agrees
    intro y hy hxy
    exact heq (x,y) (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩))
  have hM (x : V) (hx : x ∈ M) :
      mismatch R ell A color x = mismatch R ell' A color x := by
    apply mismatch_eq_of_agrees
    intro y hy hxy
    exact heq (x,y) (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩))
  have hsum : (∑ y ∈ M, (mismatch R ell A color y).card) =
      ∑ y ∈ M, (mismatch R ell' A color y).card :=
    Finset.sum_congr rfl fun y hy => congrArg Finset.card (hM y hy)
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
    · rw [← hA x hx]
      exact h.1 x hx
    · rw [← hM y hy]
      exact h.2.1 y hy
    · rw [← hsum]
      exact h.2.2
  · intro h
    refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
    · rw [hA x hx]
      exact h.1 x hx
    · rw [hM y hy]
      exact h.2.1 y hy
    · rw [hsum]
      exact h.2.2

theorem markedBad_congr (R : V → V → Prop) (ell ell' : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ)
    (heq : ∀ e ∈ markedSupport R A M, ell e = ell' e) :
    MarkedBad R ell A M P q B ↔ MarkedBad R ell' A M P q B := by
  exact exists_congr fun color => markedGood_congr R ell ell' A M P q B color heq



end
end ZL
end
end z8


