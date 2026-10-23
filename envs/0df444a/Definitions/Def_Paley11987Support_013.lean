-- Prove2me | Definitions.Def_Paley11987Support_013
-- name    : Paley11987Support_013
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:51:20.690098+00:00
-- url     : https://prove2.me/theorems/f315a4cd-5727-4245-8148-ac597b30e9d0
-- title:
--   Ordinary, marked, source and dominator families
-- statement:
--   Defines finite index types and supported bad-event families for the four kinds of labeling exclusions, together with their finite-type and complement interfaces.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabelingFamilies.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingFamilies, SHA256 e3d8f85443955e253c13668120d37a09f3bc34439240b5fcfffe0274819e3ab6

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

set_option autoImplicit false
set_option Elab.async false
section z17

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def OrdinaryIndex (V : Type*) [Fintype V] [DecidableEq V] (a : ℕ) :=
  ((Finset.univ : Finset V).powersetCard a)

def MarkedIndex (V : Type*) [Fintype V] [DecidableEq V] (a m : ℕ) :=
  Σ M : ((Finset.univ : Finset V).powersetCard m), M.valᶜ.powersetCard a

def SourceIndex (R : V → V → Prop) (a : ℕ) :=
  Σ s : V, (outOn R Finset.univ s).powersetCard a

def dominatedBy (R : V → V → Prop) (M : Finset V) : Finset V :=
  Finset.univ.filter (fun y => ∀ x ∈ M, R x y)

def DominatorIndex (R : V → V → Prop) (a : ℕ) :=
  Σ M : ((Finset.univ : Finset V).powersetCard 2), (dominatedBy R M.val).powersetCard a

instance ordinaryIndexFintype (a : ℕ) : Fintype (OrdinaryIndex V a) := by
  unfold OrdinaryIndex
  infer_instance
instance markedIndexFintype (a m : ℕ) : Fintype (MarkedIndex V a m) := by
  unfold MarkedIndex
  infer_instance
instance sourceIndexFintype (R : V → V → Prop) (a : ℕ) : Fintype (SourceIndex R a) := by
  unfold SourceIndex
  infer_instance
instance dominatorIndexFintype (R : V → V → Prop) (a : ℕ) : Fintype (DominatorIndex R a) := by
  unfold DominatorIndex
  infer_instance

theorem ordinaryBad_congr (R : V → V → Prop) (A : Finset V) (q : ℕ)
    (ell ell' : V × V → Fin 2)
    (heq : ∀ e ∈ internalEdges R A, ell e = ell' e) :
    OrdinaryBad R ell A q ↔ OrdinaryBad R ell' A q := by
  apply exists_congr
  intro color
  have hm (x : V) (hx : x ∈ A) :
      mismatch R ell A color x = mismatch R ell' A color x := by
    apply mismatch_eq_of_agrees
    intro y hy hxy
    exact heq (x,y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩)
  constructor <;> intro h x hx
  · rw [← hm x hx]
    exact h x hx
  · rw [hm x hx]
    exact h x hx

def CoherentBad (R : V → V → Prop) (A M : Finset V) (ell : V × V → Fin 2) : Prop :=
  ∃ color, Coherent R ell A M color

theorem coherentBad_congr (R : V → V → Prop) (A M : Finset V)
    (ell ell' : V × V → Fin 2)
    (heq : ∀ e ∈ markedSupport R A M, ell e = ell' e) :
    CoherentBad R A M ell ↔ CoherentBad R A M ell' := by
  apply exists_congr
  intro color
  constructor <;> intro h e he
  · rw [← heq e he]
    exact h e he
  · rw [heq e he]
    exact h e he

theorem coherentBad_complement (R : V → V → Prop) (A M : Finset V)
    (ell : V × V → Fin 2) :
    CoherentBad R A M (fun e => (ell e).rev) ↔ CoherentBad R A M ell := by
  constructor
  · rintro ⟨color,hcolor⟩
    refine ⟨fun y => (color y).rev,?_⟩
    intro e he
    simpa only [Fin.rev_rev] using congrArg Fin.rev (hcolor e he)
  · rintro ⟨color,hcolor⟩
    refine ⟨fun y => (color y).rev,?_⟩
    intro e he
    exact congrArg Fin.rev (hcolor e he)

def ordinaryFamily (R : V → V → Prop) (q a : ℕ) :
    SupportedFamily (V × V) (OrdinaryIndex V a) where
  support I := internalEdges R I.val
  bad I ell := OrdinaryBad R ell I.val q
  locality I ell ell' heq := ordinaryBad_congr R I.val q ell ell' heq
  complement I ell := ordinaryBad_complement R ell I.val q

def markedFamily (R : V → V → Prop) (q a m B : ℕ) :
    SupportedFamily (V × V) (MarkedIndex V a m) where
  support I := markedSupport R I.2.val I.1.val
  bad I ell := MarkedBad R ell I.2.val I.1.val ∅ q B
  locality I ell ell' heq := markedBad_congr R ell ell' I.2.val I.1.val ∅ q B heq
  complement I ell := markedBad_complement R ell I.2.val I.1.val ∅ q B

def sourceFamily (R : V → V → Prop) (a : ℕ) :
    SupportedFamily (V × V) (SourceIndex R a) where
  support I := markedSupport R I.2.val {I.1}
  bad I ell := CoherentBad R I.2.val {I.1} ell
  locality I ell ell' heq := coherentBad_congr R I.2.val {I.1} ell ell' heq
  complement I ell := coherentBad_complement R I.2.val {I.1} ell

def dominatorFamily (R : V → V → Prop) (a : ℕ) :
    SupportedFamily (V × V) (DominatorIndex R a) where
  support I := markedSupport R I.2.val I.1.val
  bad I ell := CoherentBad R I.2.val I.1.val ell
  locality I ell ell' heq := coherentBad_congr R I.2.val I.1.val ell ell' heq
  complement I ell := coherentBad_complement R I.2.val I.1.val ell















end
end ZL
end
end z17


