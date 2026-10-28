-- Prove2me | Definitions.Def_Sensitivity213981Formal_ArcAverage
-- name    : Sensitivity213981Formal_ArcAverage
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:04:50.771103+00:00
-- url     : https://prove2.me/theorems/cc2029f8-9ced-4932-8906-103f0123c89a
-- title:
--   Arc Average — sensitivity certificate definitions
-- statement:
--   The definitions for Arc Average in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundArcAverage.uniform_incidence_le`, `ThreeBoundArcAverage.uniform_incidence_bound`, `ThreeBoundArcAverage.incidence`, `ThreeBoundArcAverage.incidence_invariant`, `ThreeBoundArcAverage.incidence_sum`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArcAverage.lean, lines 1–78.

import Definitions.Def_Sensitivity213981Formal_LabelExists
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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

namespace Sensitivity213981Formal
section
/- Weighted support incidence averaged over a transitive finite edge set. -/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundArcAverage
open scoped BigOperators Classical
noncomputable section

variable {E D : Type*} [Fintype D] [DecidableEq E]

def incidence (support : D → Finset E) (weight : D → ℚ) (e : E) : ℚ :=
  ∑ d, if e∈support d then weight d else 0

theorem incidence_invariant (support : D → Finset E) (weight : D → ℚ)
    (e f : E) (σ : D≃D)
    (hs : ∀ d, e∈support d ↔ f∈support (σ d))
    (hw : ∀ d, weight (σ d)=weight d) :
    incidence support weight f=incidence support weight e := by
  unfold incidence
  calc
    (∑ d, if f∈support d then weight d else 0)=
        ∑ d, if f∈support (σ d) then weight (σ d) else 0 := (σ.sum_comp _).symm
    _=_ := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [← hs d,hw d]

theorem incidence_sum (edges : Finset E) (support : D → Finset E) (weight : D → ℚ)
    (hs : ∀ d, support d⊆edges) :
    (∑ e∈edges, incidence support weight e)=∑ d, (support d).card*weight d := by
  unfold incidence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have hfilter : edges.filter (fun e=>e∈support d)=support d := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h=>h.2,fun h=>⟨hs d h,h⟩⟩
  rw [← Finset.sum_filter,hfilter]
  simp

theorem uniform_incidence_le (edges : Finset E) (support : D → Finset E)
    (weight : D → ℚ) (e : E) (he : e∈edges) (s : ℕ)
    (hs : ∀ d, support d⊆edges) (hsize : ∀ d, (support d).card≤ s)
    (hw : ∀ d, 0≤ weight d)
    (huniform : ∀ f∈edges, incidence support weight f=incidence support weight e) :
    (edges.card : ℚ)*incidence support weight e≤ (s : ℚ)*∑ d,weight d := by
  calc
    (edges.card : ℚ)*incidence support weight e=
        ∑ f∈edges, incidence support weight e := by simp
    _=∑ f∈edges, incidence support weight f :=
      Finset.sum_congr rfl fun f hf=>(huniform f hf).symm
    _=∑ d,(support d).card*weight d := incidence_sum edges support weight hs
    _≤ ∑ d,(s : ℚ)*weight d := by
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsize d) (hw d)
    _=(s : ℚ)*∑ d,weight d := (Finset.mul_sum _ _ _).symm

theorem uniform_incidence_bound (edges : Finset E) (support : D → Finset E)
    (weight : D → ℚ) (e : E) (he : e∈edges) (s : ℕ) (mass : ℚ)
    (hs : ∀ d, support d⊆edges) (hsize : ∀ d, (support d).card≤ s)
    (hw : ∀ d, 0≤ weight d) (hmass : (∑ d,weight d)≤ mass)
    (huniform : ∀ f∈edges, incidence support weight f=incidence support weight e) :
    incidence support weight e≤ (s : ℚ)*mass/edges.card := by
  have hedges : 0< (edges.card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨e,he⟩
  apply (le_div_iff₀ hedges).2
  rw [mul_comm]
  exact (uniform_incidence_le edges support weight e he s hs hsize hw huniform).trans
    (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg _))

end
end ThreeBoundArcAverage



end
end Sensitivity213981Formal


