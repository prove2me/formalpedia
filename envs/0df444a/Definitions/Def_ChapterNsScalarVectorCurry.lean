-- Prove2me | Definitions.Def_ChapterNsScalarVectorCurry
-- name    : ChapterNsScalarVectorCurry
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T19:01:50.41705+00:00
-- url     : https://prove2.me/theorems/97c06a0b-1eba-413a-964b-c02a4f8f2c75
-- title:
--   The Lean 4 theorem `memLp_mulProd` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsScalarVectorCurry.lean`): generated def bundle for ChapterNsScalarVectorCurry. See BookProof/ChapterNsScalarVectorCurry.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsScalarVectorCurry.lean

import Mathlib


/-!
# The scalar–vector identification `L²(V; L²(W)) ≅ L²(V × W)`

This module closes the residual of item 1 of the Navier–Stokes plan items of
`CONSOLIDATED_PLAN.md` — *the spatial Fourier unitary and the diagonal derivative*.  The partial
(spatial-only) transform of `BookProof.ChapterNsPartialFourier` is built on the **fibred** model
of the one-particle space, the vector-valued `L²(V; L²(W))`; the plan's honest boundary was that
the measure-theoretic identification of that model with the **scalar** `L²(V × W)` was not
formalized.  Mathlib has no currying statement for `Lp`, so it is built here.

For σ-finite measures `μ` on `V` and `ν` on `W` the module constructs

* `curryLI : Lp (Lp ℂ 2 ν) 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν)`,

the unitary identification of the fibred `L²` with the scalar `L²` of the product measure, and
pins it down by its values on the generators:

* `curryLI_fibMk` — `curryLI (fibMk a c) = prodMk a c`, where `fibMk a c` is the fibred element
  `x ↦ a x • c` and `prodMk a c` the scalar function `(x, y) ↦ a x * c y`;
* `curryLI_indicator_prod` — on the tensor generators of the two sides,
  `1_s ⊗ 1_t ↦ 1_{s ×ˢ t}`;
* `curryLI_setIntegral_rect` — **currying is slicing**, in the form that needs no measurable
  choice of slices: the integral of the scalar picture over a measurable rectangle `s ×ˢ t` is the
  integral over `s` of the fibre integrals over `t`;
* `isSliceOf_curryLI` — **currying is slicing, pointwise**: almost everywhere in the spatial
  variable, the fibre `f x` of a fibred element *is* the slice `y ↦ (curryLI f) (x, y)` of its
  scalar picture (§7).  Its ingredients are of independent use: `eLpNorm_two_sq` and
  `lintegral_eLpNorm_slice_sq`, the Bochner–Fubini identity for the squared `L²(ν)` seminorms of
  the slices.

The route is the one specified by the plan.  `prodMk` and `fibMk` are bilinear, so they lift to
linear maps `prodTensor` and `fibTensor` out of the algebraic tensor product
`L²(μ) ⊗[ℂ] L²(ν)`; the two lifts have the *same* inner products on generators
(`inner_prodMk`, `inner_fibMk`, both computed by Fubini resp. by the pointwise inner product of
the fibred space), hence the same norms on the whole tensor product
(`norm_prodTensor_eq_norm_fibTensor`).  Both have dense range — on the fibred side because the
`Lp`-simple functions are dense and each of them is a finite sum of generators
(`denseRange_fibTensor`), on the scalar side by the orthogonality argument
`ae_eq_zero_of_forall_setIntegral_rect_eq_zero`: an `L²` function of the product measure whose
integral over every finite-measure measurable rectangle vanishes is zero a.e. (a π–λ induction
over the rectangles, which is the only genuinely new analysis here).  `LinearEquiv.extendOfIsometry`
then assembles the two dense isometric pictures into `curryLI`.

The module is stated for arbitrary σ-finite measures; nothing about `ℝ^d` or Lebesgue measure is
used, so it is Mathlib-level material.
-/

open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate

namespace BookProof.NsScalarVectorCurry

noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

/-! ## 1.  The generators on the two sides -/

/-- The product `(x, y) ↦ a x * c y` of two square-integrable functions is square integrable for
the product measure. -/
theorem memLp_mulProd (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    MemLp (fun z : V × W => (a : V → ℂ) z.1 * (c : W → ℂ) z.2) 2 (μ.prod ν) := by
  have ha : AEStronglyMeasurable (fun z : V × W => (a : V → ℂ) z.1) (μ.prod ν) :=
    (Lp.aestronglyMeasurable a).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hc : AEStronglyMeasurable (fun z : V × W => (c : W → ℂ) z.2) (μ.prod ν) :=
    (Lp.aestronglyMeasurable c).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  refine (memLp_two_iff_integrable_sq_norm (ha.mul hc)).2 ?_
  have h1 : Integrable (fun x => ‖(a : V → ℂ) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable a)).1 (Lp.memLp a)
  have h2 : Integrable (fun y => ‖(c : W → ℂ) y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable c)).1 (Lp.memLp c)
  simpa [norm_mul, mul_pow, smul_eq_mul] using h1.smul_prod h2

/-- The fibre-valued function `x ↦ a x • c` is square integrable. -/
theorem memLp_smulConst (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    MemLp (fun x : V => (a : V → ℂ) x • c) 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm ((Lp.aestronglyMeasurable a).smul_const c)).2 ?_
  have h1 : Integrable (fun x => ‖(a : V → ℂ) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable a)).1 (Lp.memLp a)
  have key : (fun x => ‖(a : V → ℂ) x • c‖ ^ 2)
      = ‖c‖ ^ 2 • fun x => ‖(a : V → ℂ) x‖ ^ 2 := by
    funext x
    rw [norm_smul, mul_pow]
    simp [mul_comm, smul_eq_mul]
  rw [key]
  exact h1.smul (‖c‖ ^ 2)

/-- The scalar generator: the class of `(x, y) ↦ a x * c y` in `L²(μ.prod ν)`. -/
def prodMk (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) := (memLp_mulProd a c).toLp _

/-- The fibred generator: the class of `x ↦ a x • c` in `L²(μ; L²(ν))`. -/
def fibMk (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) : Lp (Lp ℂ 2 ν) 2 μ := (memLp_smulConst a c).toLp _

theorem coeFn_prodMk (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    (prodMk a c : V × W → ℂ) =ᵐ[μ.prod ν] fun z => (a : V → ℂ) z.1 * (c : W → ℂ) z.2 :=
  (memLp_mulProd a c).coeFn_toLp

theorem coeFn_fibMk (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    (fibMk a c : V → Lp ℂ 2 ν) =ᵐ[μ] fun x => (a : V → ℂ) x • c :=
  (memLp_smulConst a c).coeFn_toLp

/-! ### Bilinearity -/

theorem prodMk_add_left (a a' : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    prodMk (a + a') c = prodMk a c + prodMk a' c := by
  have hfst : ((fun x => ((a + a' : Lp ℂ 2 μ) : V → ℂ) x) ∘ Prod.fst)
      =ᵐ[μ.prod ν] ((fun x => (a : V → ℂ) x + (a' : V → ℂ) x) ∘ Prod.fst) :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_add a a')
  refine Lp.ext ?_
  filter_upwards [coeFn_prodMk (a + a') c, Lp.coeFn_add (prodMk a c) (prodMk a' c),
    coeFn_prodMk a c, coeFn_prodMk a' c, hfst] with z h1 h2 h3 h4 h5
  simp only [Function.comp_apply] at h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5]
  ring

theorem prodMk_smul_left (r : ℂ) (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    prodMk (r • a) c = r • prodMk a c := by
  have hfst : ((fun x => ((r • a : Lp ℂ 2 μ) : V → ℂ) x) ∘ Prod.fst)
      =ᵐ[μ.prod ν] ((fun x => r • (a : V → ℂ) x) ∘ Prod.fst) :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_smul r a)
  refine Lp.ext ?_
  filter_upwards [coeFn_prodMk (r • a) c, Lp.coeFn_smul r (prodMk a c),
    coeFn_prodMk a c, hfst] with z h1 h2 h3 h5
  simp only [Function.comp_apply] at h5
  rw [h1, h2, Pi.smul_apply, h3, h5]
  simp only [smul_eq_mul]
  ring

theorem prodMk_add_right (a : Lp ℂ 2 μ) (c c' : Lp ℂ 2 ν) :
    prodMk a (c + c') = prodMk a c + prodMk a c' := by
  have hsnd : ((fun y => ((c + c' : Lp ℂ 2 ν) : W → ℂ) y) ∘ Prod.snd)
      =ᵐ[μ.prod ν] ((fun y => (c : W → ℂ) y + (c' : W → ℂ) y) ∘ Prod.snd) :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_add c c')
  refine Lp.ext ?_
  filter_upwards [coeFn_prodMk a (c + c'), Lp.coeFn_add (prodMk a c) (prodMk a c'),
    coeFn_prodMk a c, coeFn_prodMk a c', hsnd] with z h1 h2 h3 h4 h5
  simp only [Function.comp_apply] at h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5]
  ring

theorem prodMk_smul_right (r : ℂ) (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    prodMk a (r • c) = r • prodMk a c := by
  have hsnd : ((fun y => ((r • c : Lp ℂ 2 ν) : W → ℂ) y) ∘ Prod.snd)
      =ᵐ[μ.prod ν] ((fun y => r • (c : W → ℂ) y) ∘ Prod.snd) :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_smul r c)
  refine Lp.ext ?_
  filter_upwards [coeFn_prodMk a (r • c), Lp.coeFn_smul r (prodMk a c),
    coeFn_prodMk a c, hsnd] with z h1 h2 h3 h5
  simp only [Function.comp_apply] at h5
  rw [h1, h2, Pi.smul_apply, h3, h5]
  simp only [smul_eq_mul]
  ring

theorem fibMk_add_left (a a' : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    fibMk (a + a') c = fibMk a c + fibMk a' c := by
  refine Lp.ext ?_
  filter_upwards [coeFn_fibMk (a + a') c, Lp.coeFn_add (fibMk a c) (fibMk a' c),
    coeFn_fibMk a c, coeFn_fibMk a' c, Lp.coeFn_add a a'] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5]
  simp [add_smul]

theorem fibMk_smul_left (r : ℂ) (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    fibMk (r • a) c = r • fibMk a c := by
  refine Lp.ext ?_
  filter_upwards [coeFn_fibMk (r • a) c, Lp.coeFn_smul r (fibMk a c),
    coeFn_fibMk a c, Lp.coeFn_smul r a] with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4]
  simp [smul_smul]

theorem fibMk_add_right (a : Lp ℂ 2 μ) (c c' : Lp ℂ 2 ν) :
    fibMk a (c + c') = fibMk a c + fibMk a c' := by
  refine Lp.ext ?_
  filter_upwards [coeFn_fibMk a (c + c'), Lp.coeFn_add (fibMk a c) (fibMk a c'),
    coeFn_fibMk a c, coeFn_fibMk a c'] with x h1 h2 h3 h4
  rw [h1, h2, Pi.add_apply, h3, h4, smul_add]

theorem fibMk_smul_right (r : ℂ) (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    fibMk a (r • c) = r • fibMk a c := by
  refine Lp.ext ?_
  filter_upwards [coeFn_fibMk a (r • c), Lp.coeFn_smul r (fibMk a c),
    coeFn_fibMk a c] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_comm]

/-! ### The inner products of the generators agree -/

theorem inner_eq_integral (a b : Lp ℂ 2 μ) :
    inner ℂ a b = ∫ x, (b : V → ℂ) x * conj ((a : V → ℂ) x) ∂μ := by
  rw [L2.inner_def]
  simp [RCLike.inner_apply]

variable [SigmaFinite μ] [SigmaFinite ν]

/-- Fubini: the inner product of two scalar generators factorizes. -/
theorem inner_prodMk (a b : Lp ℂ 2 μ) (c d : Lp ℂ 2 ν) :
    inner ℂ (prodMk a c) (prodMk b d) = inner ℂ a b * inner ℂ c d := by
  rw [L2.inner_def]
  have hcongr : ∫ z : V × W, inner ℂ ((prodMk a c : V × W → ℂ) z) ((prodMk b d : V × W → ℂ) z)
        ∂(μ.prod ν)
      = ∫ z : V × W, ((b : V → ℂ) z.1 * conj ((a : V → ℂ) z.1)) *
          ((d : W → ℂ) z.2 * conj ((c : W → ℂ) z.2)) ∂(μ.prod ν) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_prodMk a c, coeFn_prodMk b d] with z h1 h2
    rw [h1, h2, RCLike.inner_apply]
    simp only [map_mul]
    ring
  rw [hcongr, integral_prod_mul (fun x : V => (b : V → ℂ) x * conj ((a : V → ℂ) x))
    (fun y : W => (d : W → ℂ) y * conj ((c : W → ℂ) y)), inner_eq_integral, inner_eq_integral]

omit [SigmaFinite μ] [SigmaFinite ν] in
/-- The inner product of two fibred generators factorizes in the same way. -/
theorem inner_fibMk (a b : Lp ℂ 2 μ) (c d : Lp ℂ 2 ν) :
    inner ℂ (fibMk a c) (fibMk b d) = inner ℂ a b * inner ℂ c d := by
  rw [L2.inner_def]
  have hcongr : ∫ x : V, inner ℂ ((fibMk a c : V → Lp ℂ 2 ν) x) ((fibMk b d : V → Lp ℂ 2 ν) x) ∂μ
      = ∫ x : V, ((b : V → ℂ) x * conj ((a : V → ℂ) x)) * inner ℂ c d ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_fibMk a c, coeFn_fibMk b d] with x h1 h2
    rw [h1, h2, inner_smul_left, inner_smul_right]
    ring
  rw [hcongr, integral_mul_const, inner_eq_integral a b]

/-! ## 2.  The two lifts to the algebraic tensor product -/

/-- The scalar generator as a bilinear map. -/
def prodBil : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mk₂ ℂ prodMk prodMk_add_left prodMk_smul_left prodMk_add_right prodMk_smul_right

/-- The fibred generator as a bilinear map. -/
def fibBil : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν →ₗ[ℂ] Lp (Lp ℂ 2 ν) 2 μ :=
  LinearMap.mk₂ ℂ fibMk fibMk_add_left fibMk_smul_left fibMk_add_right fibMk_smul_right

/-- The scalar side, as a linear map out of the algebraic tensor product. -/
def prodTensor : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  TensorProduct.lift prodBil

/-- The fibred side, as a linear map out of the algebraic tensor product. -/
def fibTensor : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) →ₗ[ℂ] Lp (Lp ℂ 2 ν) 2 μ :=
  TensorProduct.lift fibBil

omit [SigmaFinite μ] [SigmaFinite ν] in
@[simp] theorem prodTensor_tmul (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    prodTensor (a ⊗ₜ[ℂ] c) = prodMk a c := rfl

omit [SigmaFinite μ] [SigmaFinite ν] in
@[simp] theorem fibTensor_tmul (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    fibTensor (a ⊗ₜ[ℂ] c) = fibMk a c := rfl

/-- The two lifts have the same inner products. -/
theorem inner_prodTensor_eq_inner_fibTensor
    (s t : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)) :
    inner ℂ (prodTensor s) (prodTensor t) = inner ℂ (fibTensor s) (fibTensor t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b d => simp [inner_prodMk, inner_fibMk]
      | add t₁ t₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
  | add s₁ s₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]

/-- Hence the same norms: this is the isometry that gets extended. -/
theorem norm_prodTensor_eq_norm_fibTensor (s : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)) :
    ‖prodTensor s‖ = ‖fibTensor s‖ := by
  have h := inner_prodTensor_eq_inner_fibTensor s s
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : (‖prodTensor s‖ : ℝ) ^ 2 = (‖fibTensor s‖ : ℝ) ^ 2 := by
    exact_mod_cast h
  nlinarith [norm_nonneg (prodTensor s), norm_nonneg (fibTensor s)]

/-! ## 3.  Density of the fibred side -/

omit [SigmaFinite μ] [SigmaFinite ν] in
/-- A fibred indicator is a generator. -/
theorem fibMk_indicatorConstLp {s : Set V} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (c : Lp ℂ 2 ν) :
    fibMk (indicatorConstLp 2 hs hμs (1 : ℂ)) c = indicatorConstLp 2 hs hμs c := by
  refine Lp.ext ?_
  filter_upwards [coeFn_fibMk (indicatorConstLp 2 hs hμs (1 : ℂ)) c,
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := c)] with x h1 h2 h3
  rw [h1, h2, h3]
  by_cases hx : x ∈ s <;> simp [hx]

omit [SigmaFinite μ] [SigmaFinite ν] in
/-- Every `Lp`-simple function with values in the fibre is a finite sum of fibred generators. -/
theorem simpleFunc_mem_range_fibTensor (f : Lp.simpleFunc (Lp ℂ 2 ν) 2 μ) :
    (f : Lp (Lp ℂ 2 ν) 2 μ) ∈ LinearMap.range (fibTensor (μ := μ) (ν := ν)) := by
  induction f using Lp.simpleFunc.induction (p := (2 : ℝ≥0∞)) (by simp) (by simp) with
  | @indicatorConst c s hs hμs =>
      refine ⟨(indicatorConstLp 2 hs hμs.ne (1 : ℂ)) ⊗ₜ[ℂ] c, ?_⟩
      rw [fibTensor_tmul, fibMk_indicatorConstLp]
      exact (Lp.simpleFunc.coe_indicatorConst hs hμs.ne c).symm
  | @add f g hf hg _ hfr hgr =>
      obtain ⟨u, hu⟩ := hfr
      obtain ⟨v, hv⟩ := hgr
      exact ⟨u + v, by rw [map_add, hu, hv]; rfl⟩

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem denseRange_fibTensor :
    DenseRange (fibTensor (μ := μ) (ν := ν)) := by
  have hsub : (Lp.simpleFunc (Lp ℂ 2 ν) 2 μ : Set (Lp (Lp ℂ 2 ν) 2 μ)) ⊆
      Set.range (fibTensor (μ := μ) (ν := ν)) := by
    rintro f hf
    exact simpleFunc_mem_range_fibTensor (⟨f, hf⟩ : Lp.simpleFunc (Lp ℂ 2 ν) 2 μ)
  exact Dense.mono hsub (Lp.simpleFunc.dense (E := Lp ℂ 2 ν) (μ := μ) (p := 2) (by simp))

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem prodMk_indicatorConstLp {s : Set V} {t : Set W} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠ ∞)
    (hst : (μ.prod ν) (s ×ˢ t) ≠ ∞) :
    prodMk (indicatorConstLp 2 hs hμs (1 : ℂ)) (indicatorConstLp 2 ht hνt (1 : ℂ))
      = indicatorConstLp 2 (hs.prod ht) hst (1 : ℂ) := by
  refine Lp.ext ?_
  have h2 : ((fun x => (indicatorConstLp 2 hs hμs (1 : ℂ) : V → ℂ) x) ∘ Prod.fst)
      =ᵐ[μ.prod ν] ((s.indicator fun _ => (1 : ℂ)) ∘ Prod.fst) :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp indicatorConstLp_coeFn
  have h3 : ((fun y => (indicatorConstLp 2 ht hνt (1 : ℂ) : W → ℂ) y) ∘ Prod.snd)
      =ᵐ[μ.prod ν] ((t.indicator fun _ => (1 : ℂ)) ∘ Prod.snd) :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp indicatorConstLp_coeFn
  filter_upwards [coeFn_prodMk (indicatorConstLp 2 hs hμs (1 : ℂ))
      (indicatorConstLp 2 ht hνt (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs.prod ht) (hμs := hst) (c := (1 : ℂ)),
    h2, h3] with z e1 e4 e2 e3
  simp only [Function.comp_apply] at e2 e3
  rw [e1, e4, e2, e3]
  by_cases hz1 : z.1 ∈ s <;> by_cases hz2 : z.2 ∈ t <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz1, hz2, Set.mem_prod]

/-! ## 4.  Density of the scalar side: the rectangles are total -/

theorem integrableOn_of_measure_lt_top {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    (g : Lp ℂ 2 ρ) {A : Set X} (hA : ρ A < ∞) : IntegrableOn (g : X → ℂ) A ρ := by
  haveI : IsFiniteMeasure (ρ.restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  exact ((Lp.memLp g).restrict A).integrable (by norm_num)

/-- **Totality of the rectangles.**  An `L²` function of a product of σ-finite measures whose
integral over every finite-measure measurable rectangle vanishes is zero almost everywhere. -/
theorem ae_eq_zero_of_forall_setIntegral_rect_eq_zero (g : Lp ℂ 2 (μ.prod ν))
    (h : ∀ s : Set V, ∀ t : Set W, MeasurableSet s → MeasurableSet t → μ s < ∞ → ν t < ∞ →
      ∫ z in s ×ˢ t, (g : V × W → ℂ) z ∂(μ.prod ν) = 0) :
    (g : V × W → ℂ) =ᵐ[μ.prod ν] 0 := by
  set K : ℕ → Set (V × W) := fun n => (spanningSets μ n) ×ˢ (spanningSets ν n) with hK
  have hKmeas : ∀ n : ℕ, MeasurableSet (K n) :=
    fun n => (measurableSet_spanningSets μ n).prod (measurableSet_spanningSets ν n)
  have hKfin : ∀ n : ℕ, (μ.prod ν) (K n) < ∞ := by
    intro n
    rw [hK, Measure.prod_prod]
    exact ENNReal.mul_lt_top (measure_spanningSets_lt_top μ n) (measure_spanningSets_lt_top ν n)
  have hKzero : ∀ n : ℕ, ∫ z in K n, (g : V × W → ℂ) z ∂(μ.prod ν) = 0 := fun n =>
    h _ _ (measurableSet_spanningSets μ n) (measurableSet_spanningSets ν n)
      (measure_spanningSets_lt_top μ n) (measure_spanningSets_lt_top ν n)
  have hint : ∀ A : Set (V × W), (μ.prod ν) A < ∞ → IntegrableOn (g : V × W → ℂ) A (μ.prod ν) :=
    fun A hA => integrableOn_of_measure_lt_top g hA
  -- the π–λ induction: the integral over `K n ∩ A` vanishes for every measurable `A`
  have key : ∀ A : Set (V × W), MeasurableSet A → ∀ n : ℕ,
      ∫ z in K n ∩ A, (g : V × W → ℂ) z ∂(μ.prod ν) = 0 := by
    intro A hA
    refine MeasurableSpace.induction_on_inter (C := fun A _ => ∀ n : ℕ,
        ∫ z in K n ∩ A, (g : V × W → ℂ) z ∂(μ.prod ν) = 0)
      generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ A hA
    · intro n; simp
    · rintro _ ⟨s, hs, t, ht, rfl⟩ n
      rw [hK]
      simp only [Set.prod_inter_prod]
      exact h _ _ ((measurableSet_spanningSets μ n).inter hs)
        ((measurableSet_spanningSets ν n).inter ht)
        (lt_of_le_of_lt (measure_mono Set.inter_subset_left) (measure_spanningSets_lt_top μ n))
        (lt_of_le_of_lt (measure_mono Set.inter_subset_left) (measure_spanningSets_lt_top ν n))
    · intro B hB hC n
      have hdiff : K n ∩ Bᶜ = K n \ (K n ∩ B) := by
        ext z; by_cases hz : z ∈ B <;> simp [hz]
      rw [hdiff, integral_diff ((hKmeas n).inter hB) (hint _ (hKfin n)) Set.inter_subset_left,
        hC n, hKzero n, sub_zero]
    · intro B hdisj hBm hC n
      have hunion : K n ∩ (⋃ i, B i) = ⋃ i, (K n ∩ B i) := Set.inter_iUnion _ _
      have hsub : (⋃ i, (K n ∩ B i)) ⊆ K n := Set.iUnion_subset fun _ => Set.inter_subset_left
      rw [hunion, integral_iUnion (fun i => (hKmeas n).inter (hBm i))
        (fun i j hij => ((hdisj hij).mono Set.inter_subset_right Set.inter_subset_right))
        (hint _ (lt_of_le_of_lt (measure_mono hsub) (hKfin n)))]
      simp [hC]
  -- the sets `K n` exhaust the product, so the integral over every finite-measure set vanishes
  have hKunion : (⋃ n, K n) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    have h1 : z.1 ∈ ⋃ i, spanningSets μ i := by rw [iUnion_spanningSets μ]; trivial
    have h2 : z.2 ∈ ⋃ i, spanningSets ν i := by rw [iUnion_spanningSets ν]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h1
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h2
    exact Set.mem_iUnion.2 ⟨max i j, monotone_spanningSets μ (le_max_left i j) hi,
      monotone_spanningSets ν (le_max_right i j) hj⟩
  have hall : ∀ A : Set (V × W), MeasurableSet A → (μ.prod ν) A < ∞ →
      ∫ z in A, (g : V × W → ℂ) z ∂(μ.prod ν) = 0 := by
    intro A hA hfin
    have hmono : Monotone fun n => K n ∩ A := by
      intro m n hmn
      exact Set.inter_subset_inter_left _
        (Set.prod_mono (monotone_spanningSets μ hmn) (monotone_spanningSets ν hmn))
    have hunion : (⋃ n, K n ∩ A) = A := by
      rw [← Set.iUnion_inter, hKunion, Set.univ_inter]
    have htend := tendsto_setIntegral_of_monotone (μ := μ.prod ν) (f := (g : V × W → ℂ))
      (fun n => (hKmeas n).inter hA) hmono (by rw [hunion]; exact hint A hfin)
    rw [hunion] at htend
    have hconst : (fun n => ∫ z in K n ∩ A, (g : V × W → ℂ) z ∂(μ.prod ν)) = fun _ => (0 : ℂ) :=
      funext fun n => key A hA n
    rw [hconst] at htend
    exact (tendsto_nhds_unique tendsto_const_nhds htend).symm
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero g (by norm_num) (by norm_num)
    (fun s _ hfin => hint s hfin) (fun s hs hfin => hall s hs hfin)

theorem denseRange_prodTensor :
    DenseRange (prodTensor (μ := μ) (ν := ν)) := by
  have hbot : (LinearMap.range (prodTensor (μ := μ) (ν := ν)))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    have hrect : ∀ s : Set V, ∀ t : Set W, MeasurableSet s → MeasurableSet t → μ s < ∞ →
        ν t < ∞ → ∫ z in s ×ˢ t, (g : V × W → ℂ) z ∂(μ.prod ν) = 0 := by
      intro s t hs ht hμs hνt
      have hst : (μ.prod ν) (s ×ˢ t) ≠ ∞ := by
        rw [Measure.prod_prod]
        exact ENNReal.mul_ne_top hμs.ne hνt.ne
      have hmem : prodMk (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
          (indicatorConstLp 2 ht hνt.ne (1 : ℂ)) ∈
            LinearMap.range (prodTensor (μ := μ) (ν := ν)) :=
        ⟨(indicatorConstLp 2 hs hμs.ne (1 : ℂ)) ⊗ₜ[ℂ] (indicatorConstLp 2 ht hνt.ne (1 : ℂ)),
          rfl⟩
      have := (Submodule.mem_orthogonal _ g).1 hg _ hmem
      rwa [prodMk_indicatorConstLp hs ht hμs.ne hνt.ne hst,
        L2.inner_indicatorConstLp_one (𝕜 := ℂ) (hs.prod ht) hst g] at this
    have := ae_eq_zero_of_forall_setIntegral_rect_eq_zero g hrect
    exact (Lp.eq_zero_iff_ae_eq_zero).2 this
  have hclosure : (LinearMap.range (prodTensor (μ := μ) (ν := ν))).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2 hbot
  have := Submodule.dense_iff_topologicalClosure_eq_top.2 hclosure
  simpa [DenseRange, LinearMap.coe_range] using this

/-! ## 5.  The identification -/

/-- **The scalar–vector identification.**  For σ-finite measures the fibred `L²(V; L²(W))` and the
scalar `L²(V × W)` are unitarily identified, by the unique unitary carrying the fibred generator
`x ↦ a x • c` to the scalar function `(x, y) ↦ a x * c y`. -/
def curryLI : Lp (Lp ℂ 2 ν) 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  (LinearEquiv.refl ℂ (TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν))).extendOfIsometry
    fibTensor prodTensor denseRange_fibTensor denseRange_prodTensor
    (fun s => norm_prodTensor_eq_norm_fibTensor s)

/-- The identification carries the fibred lift of a tensor to its scalar lift. -/
theorem curryLI_fibTensor (t : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)) :
    curryLI (fibTensor t) = prodTensor t :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ t

@[simp] theorem curryLI_fibMk (a : Lp ℂ 2 μ) (c : Lp ℂ 2 ν) :
    curryLI (fibMk a c) = prodMk a c := curryLI_fibTensor (a ⊗ₜ[ℂ] c)



/-! ## 6.  Currying is slicing, tested on the rectangles -/



/-! ## 7.  The pointwise a.e. slice identity -/

/-- `IsSliceOf f g` : the fibred element `f` is, almost everywhere in the spatial variable, the
slice of the scalar function `g`. -/
def IsSliceOf (f : Lp (Lp ℂ 2 ν) 2 μ) (g : Lp ℂ 2 (μ.prod ν)) : Prop :=
  ∀ᵐ x ∂μ, ((f : V → Lp ℂ 2 ν) x : W → ℂ) =ᵐ[ν] fun y => (g : V × W → ℂ) (x, y)













omit [SigmaFinite μ] in
/-- The slice property is preserved by sums. -/
theorem IsSliceOf.add {f₁ f₂ : Lp (Lp ℂ 2 ν) 2 μ} {g₁ g₂ : Lp ℂ 2 (μ.prod ν)}
    (h₁ : IsSliceOf f₁ g₁) (h₂ : IsSliceOf f₂ g₂) : IsSliceOf (f₁ + f₂) (g₁ + g₂) := by
  have hg := Measure.ae_ae_of_ae_prod (Lp.coeFn_add g₁ g₂)
  filter_upwards [h₁, h₂, Lp.coeFn_add f₁ f₂, hg] with x e₁ e₂ e₃ e₄
  have e₅ := Lp.coeFn_add ((f₁ : V → Lp ℂ 2 ν) x) ((f₂ : V → Lp ℂ 2 ν) x)
  filter_upwards [e₁, e₂, e₄, e₅] with y d₁ d₂ d₄ d₅
  rw [e₃]
  simp only [Pi.add_apply] at d₅ ⊢
  rw [d₅, d₁, d₂, d₄]
  simp





end

end BookProof.NsScalarVectorCurry


