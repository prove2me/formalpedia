-- Prove2me | Definitions.Def_ChapterPvmMeasure
-- name    : ChapterPvmMeasure
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-07T15:32:56.759508+00:00
-- url     : https://prove2.me/theorems/3b43cae2-ca93-4023-b51d-6845bbc6021d
-- title:
--   The Lean 4 theorem `p_empty` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPvmMeasure.lean`): generated def bundle for ChapterPvmMeasure. See BookProof/ChapterPvmMeasure.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPvmMeasure.lean

import Theorems.Thm_BookProof_ChapterOrthogonalSums_hasSum_norm_sq_of_hasSum


import Definitions.Def_ChapterOrthogonalSums
import Mathlib


/-!
# Projection-valued measures on a measurable base, and the measure of a vector

This file is the first step in removing the honest boundary recorded with
`BookProof.ChapterMackeyQuasiInvariant`: over a *continuous* (measure-theoretic) base only
the **induced direction** of Mackey's imprimitivity theorem was formalized, the converse
being available only for a discrete base (`BookProof.ChapterMackeyGeneralBase`).

Here we set up the objects the converse needs.

* `Pvm X H` — a projection-valued measure on the measurable space `X` acting on the complex
  inner-product space `H`: a family `p E` of operators, self-adjoint, multiplicative on
  intersections, normalized (`p univ = 1`) and countably additive in the unconditional
  (`HasSum`) sense.
* `pvmMeasure P ψ` — the scalar measure `E ↦ ‖p E ψ‖²` attached to a vector, a *finite*
  measure on `X`.
* `pvm_eq_zero_of_measure_zero` — for a **cyclic** vector, a set of measure zero carries the
  zero projection: the measure class of `pvmMeasure P ψ` determines the measure algebra of
  the projection-valued measure.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterPvmMeasure

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A **projection-valued measure** on the measurable space `X`, acting on `H`: the
operators `p E` are self-adjoint, multiplicative on intersections of measurable sets,
`p univ = 1`, and countably additive in the unconditional sense. -/
structure Pvm (X H : Type*) [MeasurableSpace X] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The projection attached to a set. -/
  p : Set X → (H →L[ℂ] H)
  /-- Self-adjointness. -/
  symm : ∀ {E : Set X}, MeasurableSet E → ∀ u v : H, ⟪p E u, v⟫_ℂ = ⟪u, p E v⟫_ℂ
  /-- Multiplicativity on intersections. -/
  inter : ∀ {E F : Set X}, MeasurableSet E → MeasurableSet F → ∀ u : H,
    p E (p F u) = p (E ∩ F) u
  /-- Normalization. -/
  univ : ∀ u : H, p Set.univ u = u
  /-- Countable additivity, unconditionally. -/
  hasSum : ∀ f : ℕ → Set X, (∀ i, MeasurableSet (f i)) → Pairwise (Function.onFun Disjoint f) →
    ∀ u : H, HasSum (fun i => p (f i) u) (p (⋃ i, f i) u)

namespace Pvm

variable (P : Pvm X H)

/-- The empty set carries the zero projection. -/
theorem p_empty (u : H) : P.p ∅ u = 0 := by
  have hdisj : Pairwise (Function.onFun Disjoint (fun _ : ℕ => (∅ : Set X))) := by
    intro i j _
    simp [Function.onFun]
  have h := P.hasSum (fun _ : ℕ => (∅ : Set X)) (fun _ => MeasurableSet.empty) hdisj u
  have h0 : Filter.Tendsto (fun _ : ℕ => P.p ∅ u) Filter.atTop (nhds 0) :=
    h.summable.tendsto_atTop_zero
  exact tendsto_const_nhds_iff.mp h0



/-- Disjoint sets carry orthogonal projections. -/
theorem orthogonal {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hd : Disjoint E F) (u : H) : P.p E (P.p F u) = 0 := by
  rw [P.inter hE hF u, Set.disjoint_iff_inter_eq_empty.mp hd, P.p_empty]

/-- Vectors in the ranges of the projections of disjoint sets are orthogonal. -/
theorem inner_eq_zero {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hd : Disjoint E F) (u v : H) : ⟪P.p E u, P.p F v⟫_ℂ = 0 := by
  rw [P.symm hE, P.orthogonal hE hF hd, inner_zero_right]





end Pvm

/-! ## The scalar measure attached to a vector -/

/-- The measure `E ↦ ‖p E ψ‖²` of a vector: a finite measure on the base. -/
noncomputable def pvmMeasure (P : Pvm X H) (ψ : H) : Measure X :=
  Measure.ofMeasurable (fun E _ => ENNReal.ofReal (‖P.p E ψ‖ ^ 2))
    (by simp [P.p_empty])
    (by
      intro f hf hdisj
      have hsum : HasSum (fun i => ‖P.p (f i) ψ‖ ^ 2) (‖P.p (⋃ i, f i) ψ‖ ^ 2) :=
        BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum
          (P.hasSum f hf hdisj ψ)
          (fun i j hij => P.inner_eq_zero (hf i) (hf j) (hdisj hij) ψ ψ)
      change ENNReal.ofReal (‖P.p (⋃ i, f i) ψ‖ ^ 2)
          = ∑' i, ENNReal.ofReal (‖P.p (f i) ψ‖ ^ 2)
      rw [← hsum.tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum.summable])

variable (P : Pvm X H) (ψ : H)

@[simp] theorem pvmMeasure_apply {E : Set X} (hE : MeasurableSet E) :
    pvmMeasure P ψ E = ENNReal.ofReal (‖P.p E ψ‖ ^ 2) :=
  Measure.ofMeasurable_apply E hE

theorem pvmMeasure_univ : pvmMeasure P ψ Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [pvmMeasure_apply P ψ MeasurableSet.univ, P.univ]

instance : IsFiniteMeasure (pvmMeasure P ψ) :=
  ⟨by rw [pvmMeasure_univ]; exact ENNReal.ofReal_lt_top⟩



attribute [irreducible] pvmMeasure

/-! ## Cyclic vectors -/

/-- The set of vectors `p E ψ`: its closed span is the cyclic subspace generated by `ψ`. -/
def pvmOrbit (P : Pvm X H) (ψ : H) : Set H := {v | ∃ E : Set X, MeasurableSet E ∧ v = P.p E ψ}

/-- `ψ` is a **cyclic vector** for `P` when the vectors `p E ψ` span a dense subspace. -/
def IsCyclic (P : Pvm X H) (ψ : H) : Prop :=
  Dense ((Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H) : Set H)



end BookProof.ChapterPvmMeasure


