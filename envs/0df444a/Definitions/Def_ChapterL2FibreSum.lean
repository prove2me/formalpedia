-- Prove2me | Definitions.Def_ChapterL2FibreSum
-- name    : ChapterL2FibreSum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T07:44:38.133786+00:00
-- url     : https://prove2.me/theorems/79b12f45-e3c0-4306-9628-7d8843f4a670
-- title:
--   The Lean 4 theorem `proj_add` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterL2FibreSum.lean`): generated def bundle for ChapterL2FibreSum. See BookProof/ChapterL2FibreSum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterL2FibreSum.lean

import Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_coeFn
import Theorems.Thm_BookProof_ChapterHilbertSumIntertwine_linearIsometryEquiv_intertwine



import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterHilbertSumIntertwine
import Mathlib


/-!
# The multiplicity (fibre) Hilbert space: `L²(X, μ; ℓ²(ι)) = ℓ²-⨁_ι L²(X, μ)`

Mackey's *induced* system of imprimitivity of `BookProof.ChapterMackeyQuasiInvariant` lives
on the space `L²(X, μ; K)` of square-integrable functions with values in a **fibre**
(multiplicity) Hilbert space `K`, its projection-valued measure being multiplication by
indicators (`proj`).  The assembly of a general projection-valued measure into a direct sum
(`BookProof.ChapterPvmInducedSystem`) produces instead an `ℓ²`-sum of scalar `L²` spaces.
This file identifies the two, for a **countable** multiplicity index `ι` and the fibre
`K = ℓ²(ι)`:

* `fibreEmb μ i : L²(X, μ) → L²(X, μ; ℓ²(ι))`, `f ↦ f · e_i`, is an isometry;
* the family is orthogonal (`orthogonalFamily_fibreEmb`) and **total**
  (`orthogonal_iSup_range_fibreEmb`: a function orthogonal to all the ranges has all
  coordinates zero almost everywhere, hence vanishes), so
* **`isHilbertSum_fibreEmb`** — `L²(X, μ; ℓ²(ι))` *is* the Hilbert sum of `ι` copies of
  `L²(X, μ)`, and `fibreEquiv` is the unitary; and
* `fibreEmb_proj` — the embeddings intertwine multiplication by `1_E` with multiplication
  by `1_E`, whence **`fibreEquiv_symm_proj`**: under the unitary the fibrewise
  multiplication operators on the `ℓ²`-sum are exactly the multiplication operator `proj` of
  the induced system.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterL2FibreSum

open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterHilbertSumIntertwine

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-! ## Multiplication by an indicator, as a bounded operator on a vector-valued `L²` -/

section ProjCLM

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem proj_add (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f g : Lp K 2 μ) :
    proj μ hE (f + g) = proj μ hE f + proj μ hE g := by
  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ hE (f + g), proj_coeFn μ hE f, proj_coeFn μ hE g,
    Lp.coeFn_add f g, Lp.coeFn_add (proj μ hE f) (proj μ hE g)] with x e1 e2 e3 e4 e5
  simp only [Pi.add_apply] at e4 e5
  rw [e1, e5, e2, e3]
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx, e4]
  · simp only [Set.indicator_of_notMem hx, add_zero]

theorem proj_smul (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (c : ℂ) (f : Lp K 2 μ) :
    proj μ hE (c • f) = c • proj μ hE f := by
  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ hE (c • f), proj_coeFn μ hE f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (proj μ hE f)] with x e1 e2 e3 e4
  simp only [Pi.smul_apply] at e3 e4
  rw [e1, e4, e2]
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx, e3]
  · simp only [Set.indicator_of_notMem hx, smul_zero]

theorem norm_proj_le (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) :
    ‖proj μ hE f‖ ≤ ‖f‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [proj_coeFn μ hE f] with x e1
  rw [e1]
  by_cases hx : x ∈ E <;> simp [hx]

/-- Multiplication by the indicator of `E` on `L²(X, μ; K)`, as a continuous linear map. -/
noncomputable def projCLM (μ : Measure X) {E : Set X} (hE : MeasurableSet E) :
    Lp K 2 μ →L[ℂ] Lp K 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => proj μ hE f
      map_add' := proj_add μ hE
      map_smul' := fun c f => proj_smul μ hE c f } 1
    (fun f => by simpa using norm_proj_le μ hE f)

@[simp] theorem projCLM_apply (μ : Measure X) {E : Set X} (hE : MeasurableSet E)
    (f : Lp K 2 μ) : projCLM μ hE f = proj μ hE f := rfl

end ProjCLM

variable {ι : Type*} [DecidableEq ι]

/-! ## The fibre `ℓ²(ι)` -/

/-- The multiplicity (fibre) Hilbert space `ℓ²(ι)`. -/
abbrev Fibre (ι : Type*) : Type _ := lp (fun _ : ι => ℂ) 2

/-- The `i`-th unit vector of the fibre. -/
noncomputable def fibreUnit (i : ι) : Fibre ι := lp.single 2 i (1 : ℂ)

theorem norm_fibreUnit (i : ι) : ‖fibreUnit i‖ = 1 := by
  simp [fibreUnit, lp.norm_single]

theorem inner_fibreUnit (i : ι) (w : Fibre ι) : ⟪fibreUnit i, w⟫_ℂ = w i := by
  rw [fibreUnit, lp.inner_single_left]
  simp

theorem inner_fibreUnit_fibreUnit {i j : ι} (hij : i ≠ j) :
    ⟪fibreUnit (ι := ι) i, fibreUnit (ι := ι) j⟫_ℂ = 0 := by
  rw [inner_fibreUnit, fibreUnit, lp.single_apply]
  simp [hij]

/-- The embedding of a scalar into the `i`-th coordinate of the fibre. -/
noncomputable def unitCLM (i : ι) : ℂ →L[ℂ] Fibre ι :=
  ContinuousLinearMap.toSpanSingleton ℂ (fibreUnit i)

@[simp] theorem unitCLM_apply (i : ι) (c : ℂ) : unitCLM i c = c • fibreUnit i := rfl

theorem norm_unitCLM_apply (i : ι) (c : ℂ) : ‖unitCLM (ι := ι) i c‖ = ‖c‖ := by
  rw [unitCLM_apply, norm_smul, norm_fibreUnit, mul_one]

section Coord

omit [DecidableEq ι]

/-- The `i`-th coordinate of the fibre, as a continuous linear functional. -/
noncomputable def coordCLM (i : ι) : Fibre ι →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun w => (w : ∀ _ : ι, ℂ) i
      map_add' := fun w v => rfl
      map_smul' := fun c w => rfl } 1
    (fun w => by
      show ‖(w : ∀ _ : ι, ℂ) i‖ ≤ 1 * ‖w‖
      rw [one_mul]
      exact lp.norm_apply_le_norm (by norm_num) w i)

theorem coordCLM_apply (i : ι) (w : Fibre ι) : coordCLM i w = w i := rfl

end Coord

/-! ## The embedding of the `i`-th copy of `L²(X, μ)` -/

/-- `L²(X, μ) → L²(X, μ; ℓ²(ι))`, `f ↦ f · e_i`: the `i`-th copy of the scalar `L²` space
inside the vector-valued one. -/
noncomputable def fibreEmb (μ : Measure X) (i : ι) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp (Fibre ι) 2 μ where
  toLinearMap := ((unitCLM i).compLpL 2 μ).toLinearMap
  norm_map' := by
    intro f
    have h := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := μ) (unitCLM (ι := ι) i) f
    refine le_antisymm (Lp.norm_le_norm_of_ae_le ?_) (Lp.norm_le_norm_of_ae_le ?_) <;>
    · filter_upwards [h] with x hx
      simp only [ContinuousLinearMap.coe_coe]
      rw [hx, norm_unitCLM_apply]

theorem fibreEmb_coeFn (μ : Measure X) (i : ι) (f : Lp ℂ 2 μ) :
    ((fibreEmb μ i f : Lp (Fibre ι) 2 μ) : X → Fibre ι)
      =ᵐ[μ] fun x => (f : X → ℂ) x • fibreUnit i := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := μ) (unitCLM (ι := ι) i) f]
    with x hx
  exact hx

/-! ## Orthogonality -/

theorem inner_fibreEmb_eq_zero {i j : ι} (hij : i ≠ j) (f g : Lp ℂ 2 μ) :
    ⟪fibreEmb μ i f, fibreEmb μ j g⟫_ℂ = 0 := by
  rw [L2.inner_def]
  have h : (fun x => ⟪((fibreEmb μ i f : Lp (Fibre ι) 2 μ) : X → Fibre ι) x,
      ((fibreEmb μ j g : Lp (Fibre ι) 2 μ) : X → Fibre ι) x⟫_ℂ) =ᵐ[μ] fun _ => 0 := by
    filter_upwards [fibreEmb_coeFn μ i f, fibreEmb_coeFn μ j g] with x e1 e2
    rw [e1, e2, inner_smul_left, inner_smul_right, inner_fibreUnit_fibreUnit hij]
    ring
  rw [integral_congr_ae h, integral_zero]

theorem orthogonalFamily_fibreEmb (μ : Measure X) :
    OrthogonalFamily ℂ (fun _ : ι => Lp ℂ 2 μ) (fibreEmb μ) := by
  intro i j hij f g
  exact inner_fibreEmb_eq_zero hij f g

/-! ## Totality -/

/-- The coordinates of a function orthogonal to every copy of `L²(X, μ)` vanish. -/
theorem coord_eq_zero_of_mem_orthogonal {g : Lp (Fibre ι) 2 μ}
    (hg : g ∈ (⨆ i : ι, LinearMap.range (fibreEmb μ i).toLinearMap)ᗮ) (i : ι) :
    (coordCLM i).compLp g = 0 := by
  set gi : Lp ℂ 2 μ := (coordCLM i).compLp g with hgi
  have hgi_coe : (gi : X → ℂ) =ᵐ[μ] fun x => (g : X → Fibre ι) x i :=
    ContinuousLinearMap.coeFn_compLp (coordCLM (ι := ι) i) g
  have hmem : fibreEmb μ i gi ∈ ⨆ i : ι, LinearMap.range (fibreEmb μ i).toLinearMap :=
    Submodule.mem_iSup_of_mem i ⟨gi, rfl⟩
  have hzero : ⟪fibreEmb μ i gi, g⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ g).mp hg _ hmem
  have hinner : ⟪fibreEmb μ i gi, g⟫_ℂ = ⟪gi, gi⟫_ℂ := by
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [fibreEmb_coeFn μ i gi, hgi_coe] with x e1 e2
    rw [e1, e2, inner_smul_left, inner_fibreUnit, Complex.conj_mul',
      inner_self_eq_norm_sq_to_K]
    norm_cast
  have : ⟪gi, gi⟫_ℂ = 0 := by rw [← hinner, hzero]
  exact inner_self_eq_zero.mp this

/-- **Totality**: the copies of `L²(X, μ)` span a dense subspace of `L²(X, μ; ℓ²(ι))`, for a
countable multiplicity index. -/
theorem orthogonal_iSup_range_fibreEmb [Countable ι] (μ : Measure X) :
    (⨆ i : ι, LinearMap.range (fibreEmb μ i).toLinearMap)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  have hcoord : ∀ i : ι, ∀ᵐ x ∂μ, (g : X → Fibre ι) x i = 0 := by
    intro i
    have h0 : (coordCLM i).compLp g = 0 := coord_eq_zero_of_mem_orthogonal hg i
    have h1 : (((coordCLM (ι := ι) i).compLp g : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] 0 :=
      Lp.eq_zero_iff_ae_eq_zero.mp h0
    filter_upwards [ContinuousLinearMap.coeFn_compLp (coordCLM (ι := ι) i) g, h1]
      with x e1 e2
    rw [show ((g : X → Fibre ι) x) i = (coordCLM (ι := ι) i) ((g : X → Fibre ι) x) from rfl,
      ← e1, e2]
    rfl
  have hall : ∀ᵐ x ∂μ, ∀ i : ι, (g : X → Fibre ι) x i = 0 := ae_all_iff.mpr hcoord
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [hall] with x hx
  refine lp.ext ?_
  funext i
  simpa using hx i

/-! ## The Hilbert sum -/

/-- **`L²(X, μ; ℓ²(ι))` is the Hilbert sum of `ι` copies of `L²(X, μ)`.** -/
theorem isHilbertSum_fibreEmb [Countable ι] (μ : Measure X) :
    IsHilbertSum ℂ (fun _ : ι => Lp ℂ 2 μ) (fibreEmb μ) := by
  refine IsHilbertSum.mk (orthogonalFamily_fibreEmb μ) ?_
  have h : (⨆ i : ι, LinearMap.range (fibreEmb μ i).toLinearMap).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr (orthogonal_iSup_range_fibreEmb μ)
  exact le_of_eq h.symm

/-- The unitary `L²(X, μ; ℓ²(ι)) ≃ ℓ²-⨁_ι L²(X, μ)`. -/
noncomputable def fibreEquiv [Countable ι] (μ : Measure X) :
    Lp (Fibre ι) 2 μ ≃ₗᵢ[ℂ] lp (fun _ : ι => Lp ℂ 2 μ) 2 :=
  (isHilbertSum_fibreEmb μ).linearIsometryEquiv

/-! ## Multiplication by indicators -/

/-- The embeddings intertwine multiplication by `1_E` on the scalar `L²` with multiplication
by `1_E` on the vector-valued `L²`. -/
theorem fibreEmb_proj (μ : Measure X) (i : ι) {E : Set X} (hE : MeasurableSet E)
    (f : Lp ℂ 2 μ) :
    fibreEmb μ i (proj μ hE f) = proj μ hE (fibreEmb μ i f) := by
  refine Lp.ext ?_
  filter_upwards [fibreEmb_coeFn μ i (proj μ hE f), proj_coeFn μ hE f,
    proj_coeFn (K := Fibre ι) μ hE (fibreEmb μ i f), fibreEmb_coeFn μ i f] with x e1 e2 e3 e4
  rw [e1, e2, e3]
  by_cases hx : x ∈ E <;> simp [hx, e4]

/-- **Under the unitary, the fibrewise multiplication operators of the `ℓ²`-sum are exactly
the multiplication operator of the induced system.** -/
theorem fibreEquiv_proj [Countable ι] (μ : Measure X) {E : Set X} (hE : MeasurableSet E)
    (v : Lp (Fibre ι) 2 μ) (i : ι) :
    fibreEquiv μ (proj μ hE v) i = proj μ hE (fibreEquiv μ v i) :=
  linearIsometryEquiv_intertwine (isHilbertSum_fibreEmb μ) (projCLM μ hE)
    (fun _ : ι => projCLM μ hE) (fun _ u => norm_proj_le μ hE u)
    (fun i u => fibreEmb_proj μ i hE u) v i

end BookProof.ChapterL2FibreSum


