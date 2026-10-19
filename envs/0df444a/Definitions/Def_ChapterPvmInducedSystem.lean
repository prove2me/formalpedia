-- Prove2me | Definitions.Def_ChapterPvmInducedSystem
-- name    : ChapterPvmInducedSystem
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-16T20:24:35.008807+00:00
-- url     : https://prove2.me/theorems/8adf17fb-f806-430b-8ce4-3a5a32208649
-- title:
--   Chapter PvmInducedSystem
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPvmInducedSystem.lean`): generated def bundle for ChapterPvmInducedSystem. See BookProof/ChapterPvmInducedSystem.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPvmInducedSystem.lean

import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_univ

import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_SameOrbit_symm

import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterPvmCyclicUnitary
import Definitions.Def_ChapterHilbertSumIntertwine
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterPvmMeasure
import Mathlib
import Theorems.Thm_BookProof_ChapterHilbertSumIntertwine_linearIsometryEquiv_intertwine


/-!
# Assembling the cyclic pieces: the induced system with a multiplicity space

`BookProof.ChapterPvmCyclicDecomposition` decomposes a projection-valued measure into
mutually orthogonal cyclic pieces, and `BookProof.ChapterPvmCyclicUnitary` models each
piece as `L²` of a finite measure.  The boundary recorded there was the *assembly* of the
pieces into a single system.  This file removes it.

## Results

* `conjPvm` — a projection-valued measure transported along a unitary; `conjPvm_apply`.
* `swIsom` (from `ChapterPvmCyclicUnitary`) has range exactly the cyclic subspace of `ψ`
  (`range_swIsom`), even without a cyclicity hypothesis, and it intertwines multiplication
  by `1_E` with `P(E)`.
* `isHilbertSum_swIsom` — for a maximal orthogonal cyclic family `S` the isometries
  `L²(μ_ψ) → H` exhibit `H` as the **Hilbert sum** of the fibres `L²(μ_ψ)`, `ψ ∈ S`.
* **`pvm_direct_sum_model`** — the headline in "internal" form: for every projection-valued
  measure there is a family `S` of unit vectors, and isometries `Vψ : L²(X, μ_ψ) → H`
  exhibiting `H` as their Hilbert sum, with `Vψ (1_E · f) = P(E) (Vψ f)`.
* **`pvm_induced_system`** — the headline in "external" form: a single unitary
  `W : H ≃ ℓ²-⨁_{ψ ∈ S} L²(X, μ_ψ)` carrying `P` to the projection-valued measure which
  acts **fibrewise** as multiplication by `1_E`; the multiplicity (fibre) index space is
  `S`.  Both the transported projection-valued measure `conjPvm P W.symm` and the
  fibrewise description are given.
* `pvm_induced_system_separable` — on a separable space the multiplicity space is
  countable.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterPvmInducedSystem

open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicUnitary
open BookProof.ChapterPvmCyclicDecomposition BookProof.ChapterMackeyQuasiInvariant
open BookProof.ChapterHilbertSumIntertwine

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! ## Transport of a projection-valued measure along a unitary -/

/-- A projection-valued measure transported along a unitary `W : K ≃ H`:
`E ↦ W⁻¹ P(E) W`. -/
noncomputable def conjPvm (P : Pvm X H) (W : K ≃ₗᵢ[ℂ] H) : Pvm X K where
  p E := (W.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((P.p E).comp W.toContinuousLinearEquiv.toContinuousLinearMap)
  symm := by
    intro E hE u v
    have hl : ⟪W.symm (P.p E (W u)), v⟫_ℂ = ⟪P.p E (W u), W v⟫_ℂ := by
      have := W.inner_map_map (W.symm (P.p E (W u))) v
      rw [W.apply_symm_apply] at this
      exact this.symm
    have hr : ⟪u, W.symm (P.p E (W v))⟫_ℂ = ⟪W u, P.p E (W v)⟫_ℂ := by
      have := W.inner_map_map u (W.symm (P.p E (W v)))
      rw [W.apply_symm_apply] at this
      exact this.symm
    change ⟪W.symm (P.p E (W u)), v⟫_ℂ = ⟪u, W.symm (P.p E (W v))⟫_ℂ
    rw [hl, hr]
    exact P.symm hE _ _
  inter := by
    intro E F hE hF u
    change W.symm (P.p E (W (W.symm (P.p F (W u))))) = W.symm (P.p (E ∩ F) (W u))
    rw [W.apply_symm_apply, P.inter hE hF]
  univ := by
    intro u
    change W.symm (P.p Set.univ (W u)) = u
    rw [P.univ, W.symm_apply_apply]
  hasSum := by
    intro f hf hdisj u
    have h := P.hasSum f hf hdisj (W u)
    exact h.map (W.symm.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap.toAddMonoidHom)
      (W.symm.continuous)

@[simp] theorem conjPvm_apply (P : Pvm X H) (W : K ≃ₗᵢ[ℂ] H) {E : Set X} (u : K) :
    (conjPvm P W).p E u = W.symm (P.p E (W u)) := rfl

/-! ## The range of the model of a cyclic piece -/

variable [CompleteSpace H]

/-- The model map of the piece of `ψ` takes values in the cyclic subspace of `ψ`. -/
theorem swCLM_mem_cyclicSubspace (P : Pvm X H) (ψ : H) (f : Lp ℂ 2 (pvmMeasure P ψ)) :
    swCLM P ψ f ∈ cyclicSubspace P ψ := by
  refine Lp.induction (p := 2) (by simp)
    (fun f => swCLM P ψ f ∈ cyclicSubspace P ψ) ?_ ?_ ?_ f
  · intro c F hF hμF
    rw [Lp.simpleFunc.coe_indicatorConst]
    have hcsmul : indicatorConstLp 2 hF hμF.ne c
        = c • indicatorConstLp 2 hF (measure_ne_top (pvmMeasure P ψ) F) (1 : ℂ) := by
      refine Lp.ext ?_
      filter_upwards [indicatorConstLp_coeFn (μ := pvmMeasure P ψ) (p := 2) (s := F)
          (hs := hF) (hμs := hμF.ne) (c := c),
        Lp.coeFn_smul c (indicatorConstLp 2 hF (measure_ne_top (pvmMeasure P ψ) F) (1 : ℂ)),
        indicatorConstLp_coeFn (μ := pvmMeasure P ψ) (p := 2) (s := F)
          (hs := hF) (hμs := measure_ne_top (pvmMeasure P ψ) F) (c := (1 : ℂ))] with x e1 e2 e3
      simp only [Pi.smul_apply] at e2
      rw [e1, e2, e3]
      by_cases hx : x ∈ F <;> simp [hx]
    rw [hcsmul, map_smul, swCLM_indicator P ψ hF]
    exact Submodule.smul_mem _ _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨F, hF, rfl⟩))
  · intro g h hg hh _ hPg hPh
    rw [map_add]
    exact Submodule.add_mem _ hPg hPh
  · exact IsClosed.preimage (swCLM P ψ).continuous
      (Submodule.isClosed_topologicalClosure _)

/-- The range of the model map of the piece of `ψ` is exactly the cyclic subspace of `ψ`. -/
theorem range_swIsom (P : Pvm X H) (ψ : H) :
    LinearMap.range (swIsom P ψ).toLinearMap = cyclicSubspace P ψ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨f, rfl⟩
    exact swCLM_mem_cyclicSubspace P ψ f
  · have hclosed : IsClosed (Set.range (swIsom P ψ)) :=
      (swIsom P ψ).isometry.isClosedEmbedding.isClosed_range
    have hle : (Submodule.span ℂ (pvmOrbit P ψ))
        ≤ LinearMap.range (swIsom P ψ).toLinearMap := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨E, hE, rfl⟩
      exact ⟨indicatorConstLp 2 hE (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ),
        swCLM_indicator P ψ hE⟩
    intro v hv
    have hv' : v ∈ closure ((Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H) : Set H) := by
      have : v ∈ (((Submodule.span ℂ (pvmOrbit P ψ)).topologicalClosure : Submodule ℂ H) :
          Set H) := hv
      rwa [Submodule.topologicalClosure_coe] at this
    exact closure_minimal (fun w hw => hle hw) hclosed hv'

theorem swIsom_mem_cyclicSubspace (P : Pvm X H) (ψ : H) (f : Lp ℂ 2 (pvmMeasure P ψ)) :
    swIsom P ψ f ∈ cyclicSubspace P ψ :=
  swCLM_mem_cyclicSubspace P ψ f

/-! ## Orthogonality of the pieces -/

omit [CompleteSpace H] in
/-- Two cyclic-orthogonal vectors generate orthogonal cyclic subspaces. -/
theorem cyclicSubspace_le_orthogonal {P : Pvm X H} {ψ φ : H} (h : OrthOrbit P ψ φ) :
    cyclicSubspace P ψ ≤ (cyclicSubspace P φ)ᗮ := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
  rw [Submodule.span_le]
  rintro _ ⟨E, hE, rfl⟩
  -- `P(E) ψ` is orthogonal to the whole cyclic subspace of `φ`
  have hstep : cyclicSubspace P φ ≤ (Submodule.span ℂ {P.p E ψ})ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro w hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [inner_smul_left, orthOrbit_pairs h hE hF, mul_zero]
  rw [SetLike.mem_coe, Submodule.mem_orthogonal]
  intro w hw
  have hz := (Submodule.mem_orthogonal _ w).mp (hstep hw) (P.p E ψ)
    (Submodule.mem_span_singleton_self _)
  have hc := congrArg (starRingEnd ℂ) hz
  rwa [inner_conj_symm, map_zero] at hc

theorem inner_swIsom_eq_zero {P : Pvm X H} {ψ φ : H} (h : OrthOrbit P ψ φ)
    (u : Lp ℂ 2 (pvmMeasure P ψ)) (v : Lp ℂ 2 (pvmMeasure P φ)) :
    ⟪swIsom P ψ u, swIsom P φ v⟫_ℂ = 0 := by
  have hu : swIsom P ψ u ∈ (cyclicSubspace P φ)ᗮ :=
    cyclicSubspace_le_orthogonal h (swIsom_mem_cyclicSubspace P ψ u)
  exact (Submodule.mem_orthogonal' _ _).mp hu _ (swIsom_mem_cyclicSubspace P φ v)

theorem orthogonalFamily_swIsom {P : Pvm X H} {S : Set H} (hS : OrthCyclicFamily P S) :
    OrthogonalFamily ℂ (fun ψ : S => Lp ℂ 2 (pvmMeasure P (ψ : H)))
      (fun ψ : S => swIsom P (ψ : H)) := by
  intro x y hxy u v
  exact inner_swIsom_eq_zero
    (hS.orth (x : H) x.2 (y : H) y.2 (Subtype.coe_injective.ne hxy)) u v

/-! ## The Hilbert sum -/

theorem isHilbertSum_swIsom {P : Pvm X H} {S : Set H} (hS : OrthCyclicFamily P S)
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H)) :
    IsHilbertSum ℂ (fun ψ : S => Lp ℂ 2 (pvmMeasure P (ψ : H)))
      (fun ψ : S => swIsom P (ψ : H)) := by
  refine IsHilbertSum.mk (orthogonalFamily_swIsom hS) ?_
  have hsub : Submodule.span ℂ (familyOrbit P S)
      ≤ ⨆ ψ : S, LinearMap.range (swIsom P (ψ : H)).toLinearMap := by
    rw [Submodule.span_le]
    rintro v hv
    obtain ⟨ψ, hψ, hv⟩ := Set.mem_iUnion₂.mp hv
    obtain ⟨E, hE, rfl⟩ := hv
    refine Submodule.mem_iSup_of_mem ⟨ψ, hψ⟩ ?_
    exact ⟨indicatorConstLp 2 hE (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ),
      swCLM_indicator P ψ hE⟩
  intro v _
  have hv : v ∈ closure ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H) :=
    hdense v
  have hmono : closure ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H)
      ⊆ closure ((⨆ ψ : S, LinearMap.range (swIsom P (ψ : H)).toLinearMap : Submodule ℂ H) :
        Set H) := closure_mono (fun w hw => hsub hw)
  have := hmono hv
  rwa [← Submodule.topologicalClosure_coe] at this

/-! ## The headline: the direct-sum model -/

/-- **Every projection-valued measure is a direct sum of multiplication systems.**  There
is a family `S` of unit vectors and isometries `Vψ : L²(X, μ_ψ) → H`, `μ_ψ = ‖P(·)ψ‖²`,
which exhibit `H` as the Hilbert sum of the fibres `L²(X, μ_ψ)` and carry multiplication by
the indicator of `E` to `P(E)`. -/
theorem pvm_direct_sum_model (P : Pvm X H) :
    ∃ (S : Set H) (V : ∀ ψ : S, Lp ℂ 2 (pvmMeasure P (ψ : H)) →ₗᵢ[ℂ] H),
      (∀ ψ ∈ S, ‖ψ‖ = 1) ∧
      IsHilbertSum ℂ (fun ψ : S => Lp ℂ 2 (pvmMeasure P (ψ : H))) V ∧
      (∀ (ψ : S) (E : Set X) (hE : MeasurableSet E) (f : Lp ℂ 2 (pvmMeasure P (ψ : H))),
        V ψ (proj (pvmMeasure P (ψ : H)) hE f) = P.p E (V ψ f)) := by
  obtain ⟨S, hS, hdense⟩ := exists_orthCyclicFamily P
  exact ⟨S, fun ψ => swIsom P (ψ : H), hS.unit, isHilbertSum_swIsom hS hdense,
    fun ψ E hE f => swCLM_proj P (ψ : H) hE f⟩

/-! ## The fibrewise form: a single induced system -/

/-- **The unitary of the Hilbert sum carries `P(E)` to fibrewise multiplication by the
indicator of `E`.**  Multiplication by an indicator is a contraction of each fibre and is
carried by the model of the piece to `P(E)`, so the general fibrewise principle of
`BookProof.ChapterHilbertSumIntertwine` applies. -/
theorem linearIsometryEquiv_swIsom_pvm {P : Pvm X H} {S : Set H} (hS : OrthCyclicFamily P S)
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H))
    {E : Set X} (hE : MeasurableSet E) (v : H) (ψ : S) :
    (isHilbertSum_swIsom hS hdense).linearIsometryEquiv (P.p E v) ψ
      = proj (pvmMeasure P (ψ : H)) hE
          ((isHilbertSum_swIsom hS hdense).linearIsometryEquiv v ψ) :=
  linearIsometryEquiv_intertwine (isHilbertSum_swIsom hS hdense) (P.p E)
    (fun ψ : S => projL (pvmMeasure P (ψ : H)) hE)
    (fun ψ u => norm_proj_le (pvmMeasure P (ψ : H)) hE u)
    (fun ψ u => swCLM_proj P (ψ : H) hE u) v ψ

/-- **The induced system with a multiplicity space.**  For every projection-valued measure
`P` on a complete space there is a multiplicity index set `S` of unit vectors, with fibre
measures `μ_ψ = ‖P(·)ψ‖²`, and a single unitary
`W : H ≃ ℓ²-⨁_{ψ ∈ S} L²(X, μ_ψ)` under which `P(E)` becomes multiplication by the
indicator of `E` **in every fibre at once**.  This is the assembly of the cyclic pieces of
`BookProof.ChapterPvmCyclicDecomposition` into one system. -/
theorem pvm_induced_system (P : Pvm X H) :
    ∃ (S : Set H) (W : H ≃ₗᵢ[ℂ] lp (fun ψ : S => Lp ℂ 2 (pvmMeasure P (ψ : H))) 2),
      (∀ ψ ∈ S, ‖ψ‖ = 1) ∧
      (∀ (E : Set X) (hE : MeasurableSet E) (v : H) (ψ : S),
        W (P.p E v) ψ = proj (pvmMeasure P (ψ : H)) hE (W v ψ)) := by
  obtain ⟨S, hS, hdense⟩ := exists_orthCyclicFamily P
  exact ⟨S, (isHilbertSum_swIsom hS hdense).linearIsometryEquiv, hS.unit,
    fun E hE v ψ => linearIsometryEquiv_swIsom_pvm hS hdense hE v ψ⟩

/-- The transported projection-valued measure of the induced system: `W P(·) W⁻¹` is a
projection-valued measure on the `ℓ²`-sum of the fibres, acting fibrewise as multiplication
by the indicator. -/
theorem pvm_induced_system_conj (P : Pvm X H) :
    ∃ (S : Set H) (W : H ≃ₗᵢ[ℂ] lp (fun ψ : S => Lp ℂ 2 (pvmMeasure P (ψ : H))) 2),
      (∀ ψ ∈ S, ‖ψ‖ = 1) ∧
      (∀ (E : Set X) (hE : MeasurableSet E)
          (w : lp (fun ψ : S => Lp ℂ 2 (pvmMeasure P (ψ : H))) 2) (ψ : S),
        (conjPvm P W.symm).p E w ψ = proj (pvmMeasure P (ψ : H)) hE (w ψ)) := by
  obtain ⟨S, W, hunit, hfib⟩ := pvm_induced_system P
  refine ⟨S, W, hunit, ?_⟩
  intro E hE w ψ
  have h : (conjPvm P W.symm).p E w = W (P.p E (W.symm w)) := by
    simp [conjPvm_apply]
  rw [h, hfib E hE (W.symm w) ψ, LinearIsometryEquiv.apply_symm_apply]

/-- **The separable case**: the multiplicity index set is countable. -/
theorem pvm_induced_system_separable [TopologicalSpace.SeparableSpace H] (P : Pvm X H) :
    ∃ (S : Set H) (W : H ≃ₗᵢ[ℂ] lp (fun ψ : S => Lp ℂ 2 (pvmMeasure P (ψ : H))) 2),
      S.Countable ∧ (∀ ψ ∈ S, ‖ψ‖ = 1) ∧
      (∀ (E : Set X) (hE : MeasurableSet E) (v : H) (ψ : S),
        W (P.p E v) ψ = proj (pvmMeasure P (ψ : H)) hE (W v ψ)) := by
  obtain ⟨S, hS, hdense⟩ := exists_orthCyclicFamily P
  exact ⟨S, (isHilbertSum_swIsom hS hdense).linearIsometryEquiv,
    countable_of_orthCyclicFamily hS, hS.unit,
    fun E hE v ψ => linearIsometryEquiv_swIsom_pvm hS hdense hE v ψ⟩

end BookProof.ChapterPvmInducedSystem


