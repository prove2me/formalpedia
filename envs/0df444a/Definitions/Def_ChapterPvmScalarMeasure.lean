-- Prove2me | Definitions.Def_ChapterPvmScalarMeasure
-- name    : ChapterPvmScalarMeasure
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-16T20:47:16.268488+00:00
-- url     : https://prove2.me/theorems/e1c38a0e-d7f7-4047-a26e-426100bc2a74
-- title:
--   Chapter PvmScalarMeasure
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPvmScalarMeasure.lean`): generated def bundle for ChapterPvmScalarMeasure. See BookProof/ChapterPvmScalarMeasure.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPvmScalarMeasure.lean

import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterMackeyConverse
import Definitions.Def_ChapterPvmInducedSystem
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterPvmMeasure
import Mathlib


/-!
# The scalar spectral measure of a projection-valued measure, and quasi-invariance

`BookProof.ChapterPvmMeasure` attaches to a *cyclic* vector `ψ` the finite measure
`μ_ψ = ‖P(·)ψ‖²` and shows that its null sets are exactly the sets carrying the zero
projection; `BookProof.ChapterMackeyConverse` uses this to prove that the measure of a
system of imprimitivity is quasi-invariant — **in the cyclic case**.  With the cyclic
decomposition of `BookProof.ChapterPvmCyclicDecomposition` the cyclicity hypothesis can be
removed on a separable space.

## Results

* `p_eq_zero_of_forall_measure_zero` — if the cyclic subspaces of a family `S` span a dense
  subspace and every `μ_ψ`, `ψ ∈ S`, gives `E` measure zero, then `P(E) = 0`.
* `scalarMeasure` — the weighted sum `∑ 2^{-n(ψ)} μ_ψ` over a countable family: a **finite**
  measure whose null sets are exactly the sets with `P(E) = 0`
  (`scalarMeasure_eq_zero_iff_p_eq_zero`); it is a *scalar spectral measure* for `P`.
* **`exists_scalarMeasure`** — every projection-valued measure on a separable Hilbert space
  has such a measure.
* **`quasiInvariant_of_null_iff`** and **`exists_quasiInvariant_scalarMeasure`** — for a
  system of imprimitivity over a measurable `G`-space (no cyclic vector assumed, separable
  space) that measure is **quasi-invariant**: the covariance relation makes the family of
  sets with zero projection invariant under the action.
* `pvmMeasure_absolutelyContinuous` and **`exists_induced_system_in_measure_class`** — the
  fibre measures of the direct-sum model of `BookProof.ChapterPvmInducedSystem` all lie in
  the measure class of the scalar measure, so a system of imprimitivity on a separable space
  is, in one quasi-invariant measure class, an `ℓ²`-sum of multiplication systems.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterPvmScalarMeasure

open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicDecomposition
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterMackeyConverse
open BookProof.ChapterPvmInducedSystem

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Sets with zero projection -/

/-- If the orbits of a family span a dense subspace and every member gives `E` measure zero,
then `E` carries the zero projection. -/
theorem p_eq_zero_of_forall_measure_zero {P : Pvm X H} {S : Set H}
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H))
    {E : Set X} (hE : MeasurableSet E) (h : ∀ ψ ∈ S, pvmMeasure P ψ E = 0) :
    P.p E = 0 := by
  have hgen : ∀ v ∈ familyOrbit P S, P.p E v = 0 := by
    intro v hv
    obtain ⟨ψ, hψ, F, hF, rfl⟩ := Set.mem_iUnion₂.mp hv
    have hEF : pvmMeasure P ψ (E ∩ F) = 0 :=
      measure_mono_null Set.inter_subset_left (h ψ hψ)
    have hzero := (pvmMeasure_eq_zero_iff P ψ (hE.inter hF)).mp hEF
    rw [P.inter hE hF ψ]
    exact hzero
  have hspan : ∀ v ∈ (Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H), P.p E v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul c x _ hx => simp [map_smul, hx]
  have hclosed : IsClosed {v : H | P.p E v = 0} := isClosed_eq (P.p E).continuous continuous_const
  ext v
  have hv : v ∈ closure ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H) :=
    hdense v
  have := (closure_minimal (fun w hw => hspan w hw) hclosed) hv
  exact this

/-! ## The scalar spectral measure -/

/-- The weighted sum `∑_ψ 2^{-n(ψ)} μ_ψ` of the measures of a family of vectors, indexed
injectively by the naturals. -/
noncomputable def scalarMeasure (P : Pvm X H) (S : Set H) (n : S → ℕ) : Measure X :=
  Measure.sum fun ψ : S => ((2 : ENNReal)⁻¹ ^ n ψ) • pvmMeasure P (ψ : H)

theorem scalarMeasure_apply (P : Pvm X H) (S : Set H) (n : S → ℕ) {E : Set X}
    (hE : MeasurableSet E) :
    scalarMeasure P S n E = ∑' ψ : S, (2 : ENNReal)⁻¹ ^ n ψ * pvmMeasure P (ψ : H) E := by
  rw [scalarMeasure, Measure.sum_apply _ hE]
  simp

theorem scalarMeasure_eq_zero_iff (P : Pvm X H) (S : Set H) (n : S → ℕ) {E : Set X}
    (hE : MeasurableSet E) :
    scalarMeasure P S n E = 0 ↔ ∀ ψ : S, pvmMeasure P (ψ : H) E = 0 := by
  rw [scalarMeasure_apply P S n hE, ENNReal.tsum_eq_zero]
  refine forall_congr' fun ψ => ?_
  have hne : ((2 : ENNReal)⁻¹ ^ n ψ) ≠ 0 := by
    simp
  simp [mul_eq_zero, hne]

/-- The scalar measure is **finite**: the weights sum to at most `2` and the pieces are unit
vectors. -/
theorem scalarMeasure_univ_le (P : Pvm X H) {S : Set H} {n : S → ℕ}
    (hn : Function.Injective n) (hunit : ∀ ψ ∈ S, ‖ψ‖ = 1) :
    scalarMeasure P S n Set.univ ≤ 2 := by
  rw [scalarMeasure_apply P S n MeasurableSet.univ]
  have hterm : ∀ ψ : S, (2 : ENNReal)⁻¹ ^ n ψ * pvmMeasure P (ψ : H) Set.univ
      = (2 : ENNReal)⁻¹ ^ n ψ := by
    intro ψ
    rw [pvmMeasure_univ, hunit (ψ : H) ψ.2]
    simp
  rw [tsum_congr hterm]
  have hle : ∑' ψ : S, (2 : ENNReal)⁻¹ ^ n ψ ≤ ∑' k : ℕ, (2 : ENNReal)⁻¹ ^ k :=
    ENNReal.tsum_comp_le_tsum_of_injective hn (HPow.hPow (2 : ENNReal)⁻¹)
  refine hle.trans ?_
  rw [ENNReal.tsum_geometric]
  have hhalf : (1 : ENNReal) - (2 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.sub_eq_of_eq_add (by simp) ENNReal.inv_two_add_inv_two.symm]
  rw [hhalf]
  simp

/-- **The null sets of the scalar measure are exactly the sets with zero projection.** -/
theorem scalarMeasure_eq_zero_iff_p_eq_zero {P : Pvm X H} {S : Set H} {n : S → ℕ}
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H))
    {E : Set X} (hE : MeasurableSet E) :
    scalarMeasure P S n E = 0 ↔ P.p E = 0 := by
  rw [scalarMeasure_eq_zero_iff P S n hE]
  constructor
  · intro h
    exact p_eq_zero_of_forall_measure_zero hdense hE (fun ψ hψ => h ⟨ψ, hψ⟩)
  · intro h ψ
    rw [pvmMeasure_eq_zero_iff P (ψ : H) hE, h]
    rfl

/-! ## Existence on a separable space -/

/-- **Every projection-valued measure on a separable Hilbert space has a finite scalar
spectral measure**: a finite measure whose null sets are exactly the sets carrying the zero
projection. -/
theorem exists_scalarMeasure [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P : Pvm X H) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧
      ∀ E : Set X, MeasurableSet E → (μ E = 0 ↔ P.p E = 0) := by
  obtain ⟨S, hS, hdense⟩ := exists_orthCyclicFamily P
  haveI : Countable S := (countable_of_orthCyclicFamily hS).to_subtype
  obtain ⟨n, hn⟩ := Countable.exists_injective_nat S
  refine ⟨scalarMeasure P S n, ⟨?_⟩, fun E hE => scalarMeasure_eq_zero_iff_p_eq_zero hdense hE⟩
  exact lt_of_le_of_lt (scalarMeasure_univ_le P hn hS.unit) (by norm_num)

/-- Each fibre measure of the family is absolutely continuous with respect to the scalar
measure: the fibres of the direct-sum model all live in one measure class. -/
theorem pvmMeasure_absolutelyContinuous (P : Pvm X H) {S : Set H} (n : S → ℕ) (ψ : S) :
    pvmMeasure P (ψ : H) ≪ scalarMeasure P S n := by
  refine Measure.AbsolutelyContinuous.mk fun E hE hzero => ?_
  exact (scalarMeasure_eq_zero_iff P S n hE).mp hzero ψ

/-! ## Quasi-invariance -/

variable {G : Type*} [Group G] [MulAction G X]

/-- The covariance relation makes the family of sets with zero projection invariant. -/
theorem p_image_eq_zero (T : ContinuousImprimitivitySystem G X H) (g : G) {E : Set X}
    (hE : MeasurableSet E) (h : T.P.p E = 0) : T.P.p ((fun x => g • x) '' E) = 0 := by
  ext v
  have hsurj : ∃ w, T.U g w = v := ⟨(T.U g).symm v, by simp⟩
  obtain ⟨w, rfl⟩ := hsurj
  rw [← T.covariant g hE w, h]
  simp







end BookProof.ChapterPvmScalarMeasure


