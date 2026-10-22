-- Prove2me | Definitions.Def_ChapterSolovayHilbertTensor
-- name    : ChapterSolovayHilbertTensor
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-21T15:59:16.167078+00:00
-- url     : https://prove2.me/theorems/fb60a299-c82d-41b8-87ad-592448d50bcf
-- title:
--   The Lean 4 theorem `measurePreserving_prodProdProdComm` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSolovayHilbertTensor.lean`): generated def bundle for ChapterSolovayHilbertTensor. See BookProof/ChapterSolovayHilbertTensor.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSolovayHilbertTensor.lean

import Theorems.Thm_BookProof_ChapterSolovayCoordinates_tailTensorEquiv_map

import Definitions.Def_ChapterSolovayCoordinates
import Mathlib


/-!
# The Hilbert-space form of the Solovay–Kopperman tensor product (plan §4.2)

`ChapterSolovayCoordinates` proves the *measure* form of the tensor identification:
two coordinate tails interleave into one (`tailTensorEquiv_map`) and two finite
heads concatenate.  This module assembles those two pieces into a single
measure-preserving isomorphism of state spaces and derives the **Hilbert form**: a
linear isometric equivalence of the corresponding `L²` spaces.

## Deliverables

* `prodProdProdCommEquiv` and `measurePreserving_prodProdProdComm` — the four-fold
  shuffle `(A × B) × (C × D) ≃ᵐ (A × C) × (B × D)`, measure preserving for
  products of (s-finite) measures;
* `headConcatEquiv` — concatenation of two finite heads,
  `(Fin N₁ → ℝ) × (Fin N₂ → ℝ) ≃ᵐ (Fin (N₁ + N₂) → ℝ)`;
* `solovayTensorEquiv` — the tensor isomorphism of state spaces
  `CoordinateSpace N₁ × CoordinateSpace N₂ ≃ᵐ CoordinateSpace (N₁ + N₂)`;
* `solovayTensorEquiv_map` / `measurePreserving_solovayTensorEquiv` — it carries the
  *product* of the two state laws to the state law of the concatenated head with the
  one Mehler tail: the measure-theoretic content of
  `H(N₁) ⊗ H(N₂) ≅ H(N₁ + N₂)`;
* `lpCongrOfMeasurePreserving` — a measure-preserving isomorphism induces a linear
  isometric equivalence of `L²` spaces;
* `solovayTensorUnitary` — **headline**: the Solovay `L²` space of the combined
  system is *unitarily* the `L²` space of the product of the two systems;
* `tensorMemLp`, `tensorLp`, `inner_tensorLp` — the pure tensors: `f ⊗ g` is in
  `L²` of the product law and `⟪f₁ ⊗ g₁, f₂ ⊗ g₂⟫ = ⟪f₁, f₂⟫ · ⟪g₁, g₂⟫`, the
  defining property of a Hilbert tensor product on elementary tensors.

## Documented scope

The identification proved here is the unitary identification of `L²` of the
combined state law with `L²` of the product state law, together with the
multiplicativity of the inner product on pure tensors.  That the closed span of the
pure tensors exhausts `L²` of a product measure — the *completeness* half of the
statement "`L²(μ ⊗ ν)` is the Hilbert tensor product of `L²(μ)` and `L²(ν)`" — is
not formalized here, and Mathlib has no Hilbert-space tensor product to state it
against.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BookProof.ChapterSolovayHilbertTensor

open BookProof.ChapterSolovayCoordinates

/-! ## The four-fold shuffle -/

section Shuffle

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace D]

/-- The four-fold shuffle `(A × B) × (C × D) ≃ᵐ (A × C) × (B × D)`, written as a
composition of associativity and commutativity isomorphisms so that measure
preservation follows from the standard lemmas. -/
def prodProdProdCommEquiv : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D) :=
  (MeasurableEquiv.prodAssoc.trans <|
    ((MeasurableEquiv.refl A).prodCongr (MeasurableEquiv.prodAssoc (α := B) (β := C)
        (γ := D)).symm).trans <|
      ((MeasurableEquiv.refl A).prodCongr
          ((MeasurableEquiv.prodComm (α := B) (β := C)).prodCongr
            (MeasurableEquiv.refl D))).trans <|
        ((MeasurableEquiv.refl A).prodCongr (MeasurableEquiv.prodAssoc (α := C) (β := B)
            (γ := D))).trans
          (MeasurableEquiv.prodAssoc (α := A) (β := C) (γ := B × D)).symm)

@[simp] theorem prodProdProdCommEquiv_apply (z : (A × B) × (C × D)) :
    prodProdProdCommEquiv z = ((z.1.1, z.2.1), (z.1.2, z.2.2)) := rfl

/-- The shuffle is measure preserving for products of s-finite measures. -/
theorem measurePreserving_prodProdProdComm (μA : Measure A) (μB : Measure B)
    (μC : Measure C) (μD : Measure D) [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (prodProdProdCommEquiv : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc : (A × B) × (C × D) ≃ᵐ _)
      ((μA.prod μB).prod (μC.prod μD)) (μA.prod (μB.prod (μC.prod μD))) :=
    measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h2 : MeasurePreserving
      ((MeasurableEquiv.refl A).prodCongr
        (MeasurableEquiv.prodAssoc (α := B) (β := C) (γ := D)).symm)
      (μA.prod (μB.prod (μC.prod μD))) (μA.prod ((μB.prod μC).prod μD)) :=
    (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μB μC μD).symm
  have h3 : MeasurePreserving
      ((MeasurableEquiv.refl A).prodCongr
        ((MeasurableEquiv.prodComm (α := B) (β := C)).prodCongr (MeasurableEquiv.refl D)))
      (μA.prod ((μB.prod μC).prod μD)) (μA.prod ((μC.prod μB).prod μD)) :=
    (MeasurePreserving.id μA).prod
      ((Measure.measurePreserving_swap (μ := μB) (ν := μC)).prod (MeasurePreserving.id μD))
  have h4 : MeasurePreserving
      ((MeasurableEquiv.refl A).prodCongr
        (MeasurableEquiv.prodAssoc (α := C) (β := B) (γ := D)))
      (μA.prod ((μC.prod μB).prod μD)) (μA.prod (μC.prod (μB.prod μD))) :=
    (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h5 : MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := A) (β := C) (γ := B × D)).symm
      (μA.prod (μC.prod (μB.prod μD))) ((μA.prod μC).prod (μB.prod μD)) :=
    (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

end Shuffle

/-! ## The tensor isomorphism of Solovay state spaces -/

variable {N₁ N₂ : ℕ}

/-- Concatenation of two finite heads. -/
def headConcatEquiv (N₁ N₂ : ℕ) :
    ((Fin N₁ → ℝ) × (Fin N₂ → ℝ)) ≃ᵐ (Fin (N₁ + N₂) → ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin (N₁ + N₂) => ℝ)
    (finSumFinEquiv (m := N₁) (n := N₂))).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N₁ ⊕ Fin N₂ => ℝ))).symm

/-- The law of the concatenated head. -/
def concatHeadMeasure (N₁ N₂ : ℕ) (headDist₁ : Measure (Fin N₁ → ℝ))
    (headDist₂ : Measure (Fin N₂ → ℝ)) : Measure (Fin (N₁ + N₂) → ℝ) :=
  Measure.map (headConcatEquiv N₁ N₂) (headDist₁.prod headDist₂)

instance concatHeadMeasure_isProbability (N₁ N₂ : ℕ) (headDist₁ : Measure (Fin N₁ → ℝ))
    (headDist₂ : Measure (Fin N₂ → ℝ)) [IsProbabilityMeasure headDist₁]
    [IsProbabilityMeasure headDist₂] :
    IsProbabilityMeasure (concatHeadMeasure N₁ N₂ headDist₁ headDist₂) := by
  unfold concatHeadMeasure
  exact Measure.isProbabilityMeasure_map (MeasurableEquiv.measurable _).aemeasurable

/-- **The tensor isomorphism of state spaces.**  Two Solovay systems (finite head
plus Mehler tail) combine into one: the heads concatenate and the two tails
interleave into a single tail. -/
def solovayTensorEquiv (N₁ N₂ : ℕ) :
    (CoordinateSpace N₁ × CoordinateSpace N₂) ≃ᵐ CoordinateSpace (N₁ + N₂) :=
  prodProdProdCommEquiv.trans ((headConcatEquiv N₁ N₂).prodCongr tailTensorEquiv)

/-- **The tensor isomorphism is measure preserving.**  It carries the product of the
two state laws to the state law of the concatenated head over one Mehler tail. -/
theorem solovayTensorEquiv_map (N₁ N₂ : ℕ) (headDist₁ : Measure (Fin N₁ → ℝ))
    (headDist₂ : Measure (Fin N₂ → ℝ)) [IsProbabilityMeasure headDist₁]
    [IsProbabilityMeasure headDist₂] :
    Measure.map (solovayTensorEquiv N₁ N₂)
        ((coordinateStateMeasure N₁ headDist₁).prod (coordinateStateMeasure N₂ headDist₂))
      = coordinateStateMeasure (N₁ + N₂) (concatHeadMeasure N₁ N₂ headDist₁ headDist₂) := by
  have hshuffle := measurePreserving_prodProdProdComm headDist₁ coordinateTailMeasure
    headDist₂ coordinateTailMeasure
  calc Measure.map (solovayTensorEquiv N₁ N₂)
        ((coordinateStateMeasure N₁ headDist₁).prod (coordinateStateMeasure N₂ headDist₂))
      = Measure.map (Prod.map (headConcatEquiv N₁ N₂) (tailTensorEquiv))
          (Measure.map prodProdProdCommEquiv
            ((headDist₁.prod coordinateTailMeasure).prod
              (headDist₂.prod coordinateTailMeasure))) := by
        rw [solovayTensorEquiv, MeasurableEquiv.coe_trans,
          ← Measure.map_map ((headConcatEquiv N₁ N₂).prodCongr tailTensorEquiv).measurable
            prodProdProdCommEquiv.measurable]
        rfl
    _ = Measure.map (Prod.map (headConcatEquiv N₁ N₂) (tailTensorEquiv))
          ((headDist₁.prod headDist₂).prod
            (coordinateTailMeasure.prod coordinateTailMeasure)) := by
        rw [hshuffle.map_eq]
    _ = (Measure.map (headConcatEquiv N₁ N₂) (headDist₁.prod headDist₂)).prod
          (Measure.map tailTensorEquiv
            (coordinateTailMeasure.prod coordinateTailMeasure)) :=
        (Measure.map_prod_map _ _ (MeasurableEquiv.measurable _)
          (MeasurableEquiv.measurable _)).symm
    _ = coordinateStateMeasure (N₁ + N₂) (concatHeadMeasure N₁ N₂ headDist₁ headDist₂) := by
        rw [tailTensorEquiv_map]
        rfl

theorem measurePreserving_solovayTensorEquiv (N₁ N₂ : ℕ) (headDist₁ : Measure (Fin N₁ → ℝ))
    (headDist₂ : Measure (Fin N₂ → ℝ)) [IsProbabilityMeasure headDist₁]
    [IsProbabilityMeasure headDist₂] :
    MeasurePreserving (solovayTensorEquiv N₁ N₂)
      ((coordinateStateMeasure N₁ headDist₁).prod (coordinateStateMeasure N₂ headDist₂))
      (coordinateStateMeasure (N₁ + N₂) (concatHeadMeasure N₁ N₂ headDist₁ headDist₂)) :=
  ⟨(solovayTensorEquiv N₁ N₂).measurable, solovayTensorEquiv_map N₁ N₂ headDist₁ headDist₂⟩

/-! ## The Hilbert form -/

section LpCongr

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A measure-preserving isomorphism induces a **linear isometric equivalence** of
`L²` spaces. -/
def lpCongrOfMeasurePreserving (μ : Measure α) (ν : Measure β) (e : α ≃ᵐ β)
    (he : MeasurePreserving e μ ν) : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearMap := Lp.compMeasurePreservingₗ ℂ (e : α → β) he
  norm_map' g := Lp.norm_compMeasurePreserving g he
  invFun := Lp.compMeasurePreservingₗ ℂ (e.symm : β → α) he.symm
  left_inv g := by
    refine Lp.ext ?_
    have h1 : (Lp.compMeasurePreservingₗ ℂ (e.symm : β → α) he.symm
        (Lp.compMeasurePreservingₗ ℂ (e : α → β) he g) : β → ℂ)
        =ᵐ[ν] (fun y => (Lp.compMeasurePreservingₗ ℂ (e : α → β) he g) (e.symm y)) :=
      Lp.coeFn_compMeasurePreserving _ he.symm
    have h2 : (Lp.compMeasurePreservingₗ ℂ (e : α → β) he g : α → ℂ) =ᵐ[μ] fun x => g (e x) :=
      Lp.coeFn_compMeasurePreserving _ he
    have h3 : (fun y => (Lp.compMeasurePreservingₗ ℂ (e : α → β) he g) (e.symm y))
        =ᵐ[ν] fun y => g (e (e.symm y)) := by
      have := he.symm.quasiMeasurePreserving.ae h2
      exact this
    refine h1.trans (h3.trans ?_)
    filter_upwards with y
    simp
  right_inv g := by
    refine Lp.ext ?_
    have h1 : (Lp.compMeasurePreservingₗ ℂ (e : α → β) he
        (Lp.compMeasurePreservingₗ ℂ (e.symm : β → α) he.symm g) : α → ℂ)
        =ᵐ[μ] (fun x => (Lp.compMeasurePreservingₗ ℂ (e.symm : β → α) he.symm g) (e x)) :=
      Lp.coeFn_compMeasurePreserving _ he
    have h2 : (Lp.compMeasurePreservingₗ ℂ (e.symm : β → α) he.symm g : β → ℂ)
        =ᵐ[ν] fun y => g (e.symm y) :=
      Lp.coeFn_compMeasurePreserving _ he.symm
    have h3 : (fun x => (Lp.compMeasurePreservingₗ ℂ (e.symm : β → α) he.symm g) (e x))
        =ᵐ[μ] fun x => g (e.symm (e x)) := by
      have := he.quasiMeasurePreserving.ae h2
      exact this
    refine h1.trans (h3.trans ?_)
    filter_upwards with x
    simp

end LpCongr

/-- **Headline (plan §4.2), the Hilbert form.**  The `L²` space of the combined
Solovay system is *unitarily* the `L²` space of the product of the two systems: the
tensor product of two Solovay–Kopperman spaces is a Solovay–Kopperman space. -/
def solovayTensorUnitary (N₁ N₂ : ℕ) (headDist₁ : Measure (Fin N₁ → ℝ))
    (headDist₂ : Measure (Fin N₂ → ℝ)) [IsProbabilityMeasure headDist₁]
    [IsProbabilityMeasure headDist₂] :
    Lp ℂ 2 (coordinateStateMeasure (N₁ + N₂) (concatHeadMeasure N₁ N₂ headDist₁ headDist₂))
      ≃ₗᵢ[ℂ] Lp ℂ 2 ((coordinateStateMeasure N₁ headDist₁).prod
        (coordinateStateMeasure N₂ headDist₂)) :=
  lpCongrOfMeasurePreserving _ _ (solovayTensorEquiv N₁ N₂)
    (measurePreserving_solovayTensorEquiv N₁ N₂ headDist₁ headDist₂)

/-! ## Pure tensors -/

section PureTensor

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
/-- The pure tensor of two `L²` functions is in `L²` of the product measure. -/
theorem tensorMemLp {f : α → ℂ} {g : β → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2 (μ.prod ν) := by
  have hm1 : AEStronglyMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
    hf.aestronglyMeasurable.comp_fst
  have hm2 : AEStronglyMeasurable (fun z : α × β => g z.2) (μ.prod ν) :=
    hg.aestronglyMeasurable.comp_snd
  have hmeas : AEStronglyMeasurable (fun z : α × β => f z.1 * g z.2) (μ.prod ν) := hm1.mul hm2
  refine ⟨hmeas, ?_⟩
  have hsplit : ∀ z : α × β, ‖f z.1 * g z.2‖ₑ ^ (2 : ℝ) = ‖f z.1‖ₑ ^ (2 : ℝ) * ‖g z.2‖ₑ ^ (2 : ℝ) :=
    fun z => by rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have hlint : ∫⁻ z : α × β, ‖f z.1 * g z.2‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂(μ.prod ν)
      = (∫⁻ x, ‖f x‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂μ) * ∫⁻ y, ‖g y‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂ν := by
    simp only [ENNReal.toReal_ofNat]
    rw [lintegral_congr (fun z => hsplit z)]
    exact lintegral_prod_mul
      ((hf.aestronglyMeasurable.enorm).pow_const _)
      ((hg.aestronglyMeasurable.enorm).pow_const _)
  rw [hlint]
  have hfl : (∫⁻ x, ‖f x‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂μ) < ⊤ := by
    have := hf.eLpNorm_lt_top
    rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      ENNReal.rpow_lt_top_iff_of_pos (by norm_num)] at this
  have hgl : (∫⁻ y, ‖g y‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂ν) < ⊤ := by
    have := hg.eLpNorm_lt_top
    rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      ENNReal.rpow_lt_top_iff_of_pos (by norm_num)] at this
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_lt_top hfl hgl).ne

/-- The pure tensor `f ⊗ g` as an element of `L²(μ ⊗ ν)`. -/
def tensorLp {f : α → ℂ} {g : β → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    Lp ℂ 2 (μ.prod ν) :=
  (tensorMemLp hf hg).toLp _

/-- **The inner product of pure tensors multiplies** — the defining property of a
Hilbert tensor product on elementary tensors. -/
theorem inner_tensorLp {f₁ f₂ : α → ℂ} {g₁ g₂ : β → ℂ}
    (hf₁ : MemLp f₁ 2 μ) (hf₂ : MemLp f₂ 2 μ) (hg₁ : MemLp g₁ 2 ν) (hg₂ : MemLp g₂ 2 ν) :
    (inner ℂ (tensorLp hf₁ hg₁) (tensorLp hf₂ hg₂) : ℂ)
      = (inner ℂ (hf₁.toLp f₁) (hf₂.toLp f₂) : ℂ) * (inner ℂ (hg₁.toLp g₁) (hg₂.toLp g₂) : ℂ) := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  have h1 : ∀ᵐ z : α × β ∂(μ.prod ν),
      (inner ℂ ((tensorLp hf₁ hg₁ : α × β → ℂ) z) ((tensorLp hf₂ hg₂ : α × β → ℂ) z) : ℂ)
        = (starRingEnd ℂ) (f₁ z.1) * f₂ z.1 * ((starRingEnd ℂ) (g₁ z.2) * g₂ z.2) := by
    filter_upwards [(tensorMemLp hf₁ hg₁).coeFn_toLp, (tensorMemLp hf₂ hg₂).coeFn_toLp]
      with z hz1 hz2
    rw [tensorLp, tensorLp] at *
    rw [hz1, hz2, RCLike.inner_apply, map_mul]
    ring
  rw [integral_congr_ae h1]
  have h2 := integral_prod_mul (μ := μ) (ν := ν)
    (fun x => (starRingEnd ℂ) (f₁ x) * f₂ x) (fun y => (starRingEnd ℂ) (g₁ y) * g₂ y)
  rw [h2]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [hf₁.coeFn_toLp, hf₂.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply]
    ring
  · refine integral_congr_ae ?_
    filter_upwards [hg₁.coeFn_toLp, hg₂.coeFn_toLp] with y hy1 hy2
    rw [hy1, hy2, RCLike.inner_apply]
    ring

end PureTensor

end BookProof.ChapterSolovayHilbertTensor

end


