-- Prove2me | Definitions.Def_ChapterL2TensorPowerUnitary
-- name    : ChapterL2TensorPowerUnitary
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T21:05:10.726689+00:00
-- url     : https://prove2.me/theorems/52531c8b-0b1f-49e1-83bd-957f39eab374
-- title:
--   ChapterL2TensorPowerUnitary
-- statement:
--   ChapterL2TensorPowerUnitary

import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterYangMillsNonAbelianEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterTensorGraphCore
import Mathlib


/-!
# The `n`-particle sector identification `L²(V)^{⊗̂n} ≅ L²(Vⁿ)`

The second-quantization chapters of the project build the `n`-particle sector as the
completion of the algebraic tensor power (`TensorCore.IPSpace.pow`,
`SecondQuantizationCore.fockSector`), while the concrete many-parcel Hamiltonians
(Navier–Stokes parcels, the gravity/QYM modes) act on `L²` of the `n`-fold product space.
The identification of the two was recorded as an open item (“sector identifications”) in
`CONSOLIDATED_PLAN.md`.  This module constructs it, for an arbitrary σ-finite measure space.

## What is proved

For a σ-finite measure `μ` on `V`, with `L2Space μ = ⟨L²(μ)⟩` and
`piMeasure μ n = μ^{⊗n}` on `Fin n → V`:

* `prodTensorₗᵢ` — the scalar lift `a ⊗ c ↦ ((x, y) ↦ a x · c y)` is an **isometry** from the
  algebraic tensor product (with Mathlib's tensor inner product) to `L²(μ ⊗ ν)`
  (`inner_prodTensor`);
* `splitIso n` — the unitary change of variables `V^{n+1} ≅ V × Vⁿ`,
  `x ↦ (x 0, tail x)` (measure preserving by `measurePreserving_piFinSuccAbove`);
* `embPow n` — the isometry `L²(μ)^{⊗n} → L²(μ^{⊗n})`, by the recursion
  `embPow (n+1) (a ⊗ t) = splitIso (prodMk a (embPow n t))`; `embPow_succ_tmul_ae` — the
  pointwise formula `(embPow (n+1) (a ⊗ t)) x = a (x 0) · (embPow n t) (tail x)` a.e.;
* `denseRange_embPow` — its range is dense, for every `n` (the base case is the
  one-dimensional `L²` of a point; the step combines `denseRange_prodTensor` with the
  induction hypothesis);
* **`tensorPowUnitary n : fockSector (L2Space μ) n ≃ₗᵢ[ℂ] L²(μ^{⊗n})`** — the unitary
  identification of the `n`-particle sector with `L²` of the product space, and
  `tensorPowUnitary_coe` (it extends `embPow n`);
* **`l2dSectorUnitary d n : fockSector (L2dSpace d) n ≃ₗᵢ[ℂ] L²((ℝ^d)ⁿ)`** — the Lebesgue
  instance;
* `measurePreserving_uncurry_fin`, `blockSplit`/`blockJoin`, `measurePreserving_blockSplit`,
  `measurePreserving_blockJoin`, `parcelRelabel` — the relabelling `(ℝ^d)ⁿ ≅ ℝ^{n·d}` is
  Lebesgue-measure preserving, hence a unitary `L²((ℝ^d)ⁿ) ≅ L2d (n·d)` (`mpEquivUnitary`);
* **`parcelSectorUnitary d n : fockSector (L2dSpace d) n ≃ₗᵢ[ℂ] L2d (n * d)`** and, for
  Navier–Stokes, **`nsParcelSectorUnitary n : L²(ℝ⁶)^{⊗̂n} ≃ₗᵢ L²(ℝ^{6n})`** — exactly the
  parcel-sector space `L2d (n * 6)` of `NsFourierElimination.nsRedFockSpace`;
* `lpFiberwise`, **`nsFockUnitary`** — the whole Fock space `⊕ₙ L²(ℝ⁶)^{⊗̂n}` of the
  second-quantization chapters is unitarily equivalent to `nsRedFockSpace = ⊕ₙ L²(ℝ^{6n})`.

## Honest boundary

The identification is at the level of Hilbert spaces (with its formula on pure tensors).
The operator-level transport — that the unitary carries the sector derivation
`Σ_p 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1` on the tensor power of the Gauss–polynomial core to the parcel
operator of `nsRedFullFockHam` on its core — is not proved here, nor the identification with
the occupation-number (`ℓ²`) spelling `dGammaOp (nsSpCol …)`.
-/

namespace BookProof.L2TensorPower

open MeasureTheory BookProof.TensorCore BookProof.NsScalarVectorCurry
open BookProof.SecondQuantizationCore
open scoped TensorProduct

noncomputable section

section Isometry

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν]

/-- The scalar lift preserves inner products (Mathlib's inner product on the algebraic tensor
product). -/
theorem inner_prodTensor (s t : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)) :
    inner ℂ (prodTensor s) (prodTensor t) = inner ℂ s t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b d => simp [inner_prodMk, TensorProduct.inner_tmul]
      | add t₁ t₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
  | add s₁ s₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]

variable (μ ν) in
/-- The scalar lift as a linear isometry. -/
def prodTensorₗᵢ : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  (prodTensor (μ := μ) (ν := ν)).isometryOfInner inner_prodTensor

@[simp] theorem prodTensorₗᵢ_apply (s : TensorProduct ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν)) :
    prodTensorₗᵢ μ ν s = prodTensor s := rfl

/-- `c ↦ prodMk a c` is continuous. -/
theorem continuous_prodMk_right (a : Lp ℂ 2 μ) :
    Continuous fun c : Lp ℂ 2 ν => prodMk a c := by
  have h : (fun c : Lp ℂ 2 ν => prodMk a c) = fun c => prodTensorₗᵢ μ ν (a ⊗ₜ[ℂ] c) := rfl
  rw [h]
  refine (prodTensorₗᵢ μ ν).continuous.comp ?_
  exact AddMonoidHomClass.continuous_of_bound (TensorProduct.mk ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) a) ‖a‖
    fun c => by rw [TensorProduct.mk_apply, TensorProduct.norm_tmul]

end Isometry

variable {V : Type} [MeasurableSpace V] (μ : Measure V) [SigmaFinite μ]

/-- `L²(μ)` as a bundled inner product space. -/
def L2Space : IPSpace := ⟨Lp ℂ 2 μ⟩

/-- The `n`-fold product measure on `Fin n → V`. -/
abbrev piMeasure (n : ℕ) : Measure (Fin n → V) := Measure.pi fun _ : Fin n => μ

/-- The unitary change of variables `V^{n+1} ≅ V × Vⁿ`, `x ↦ (x 0, tail x)`, on `L²`. -/
def splitIso (n : ℕ) : Lp ℂ 2 (μ.prod (piMeasure μ n)) →ₗᵢ[ℂ] Lp ℂ 2 (piMeasure μ (n + 1)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) 0)
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0)

theorem piMeasure_zero_univ : piMeasure μ 0 Set.univ = 1 := by
  rw [piMeasure, Measure.pi_univ]
  simp

/-- The constant function `1` on the one-point space `V⁰`. -/
def onePt : Lp ℂ 2 (piMeasure μ 0) :=
  indicatorConstLp 2 MeasurableSet.univ (by rw [piMeasure_zero_univ μ]; exact ENNReal.one_ne_top)
    (1 : ℂ)

theorem norm_onePt : ‖onePt μ‖ = 1 := by
  rw [onePt, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [Measure.real, piMeasure_zero_univ μ]

/-- **The isometry `L²(μ)^{⊗n} → L²(μ^{⊗n})`.** -/
def embPow : (n : ℕ) → ((L2Space μ).pow n).carrier →ₗᵢ[ℂ] Lp ℂ 2 (piMeasure μ n)
  | 0 => LinearIsometry.toSpanSingleton ℂ (Lp ℂ 2 (piMeasure μ 0)) (norm_onePt μ)
  | n + 1 => (splitIso μ n).comp ((prodTensorₗᵢ μ (piMeasure μ n)).comp
      (TensorProduct.mapIsometry (LinearIsometry.id (E := Lp ℂ 2 μ)) (embPow n)))





/-- Every vector of `L²` of the one-point space is a multiple of `1`. -/
theorem denseRange_embPow_zero : DenseRange (embPow μ 0) := by
  refine Function.Surjective.denseRange fun g => ?_
  refine ⟨((g : (Fin 0 → V) → ℂ) default : ℂ), ?_⟩
  show ((g : (Fin 0 → V) → ℂ) default) • onePt μ = g
  refine Lp.ext ?_
  have h1 := Lp.coeFn_smul ((g : (Fin 0 → V) → ℂ) default) (onePt μ)
  have h2 : (onePt μ : (Fin 0 → V) → ℂ) =ᵐ[piMeasure μ 0] Set.indicator Set.univ fun _ => 1 :=
    indicatorConstLp_coeFn
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, Pi.smul_apply, hx2, Set.indicator_univ, smul_eq_mul, mul_one]
  exact congrArg _ (Subsingleton.elim _ _)

/-- **The range of `embPow n` is dense**, for every `n`. -/
theorem denseRange_embPow : ∀ n : ℕ, DenseRange (embPow μ n)
  | 0 => denseRange_embPow_zero μ
  | n + 1 => by
      have ih := denseRange_embPow n
      set F : TensorProduct ℂ (Lp ℂ 2 μ) ((L2Space μ).pow n).carrier →ₗ[ℂ]
          Lp ℂ 2 (μ.prod (piMeasure μ n)) :=
        (prodTensorₗᵢ μ (piMeasure μ n)).toLinearMap.comp
          (TensorProduct.mapIsometry (LinearIsometry.id (E := Lp ℂ 2 μ))
            (embPow μ n)).toLinearMap with hF
      -- the closure of the range of `F` contains the range of `prodTensor`
      have hsub : LinearMap.range (prodTensor (μ := μ) (ν := piMeasure μ n))
          ≤ (LinearMap.range F).topologicalClosure := by
        rintro _ ⟨s, rfl⟩
        induction s using TensorProduct.induction_on with
        | zero => simp
        | tmul a c =>
            simp only [prodTensor_tmul]
            have hc : c ∈ closure (Set.range (embPow μ n)) := ih.closure_eq ▸ Set.mem_univ c
            have hmap : prodMk a c ∈ closure ((fun c' => prodMk a c') '' Set.range (embPow μ n)) :=
              map_mem_closure (continuous_prodMk_right a) hc (fun y hy => Set.mem_image_of_mem _ hy)
            refine closure_mono ?_ hmap
            rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
            exact ⟨a ⊗ₜ[ℂ] t, rfl⟩
        | add s₁ s₂ h₁ h₂ =>
            rw [map_add]
            exact Submodule.add_mem _ h₁ h₂
      have hdF : DenseRange F := by
        have htop : (LinearMap.range F).topologicalClosure = ⊤ := by
          refine eq_top_iff.2 fun x _ => ?_
          have hx : x ∈ closure (Set.range (prodTensor (μ := μ) (ν := piMeasure μ n))) :=
            (denseRange_prodTensor (μ := μ) (ν := piMeasure μ n)).closure_eq ▸ Set.mem_univ x
          have hcl : closure (Set.range (prodTensor (μ := μ) (ν := piMeasure μ n)))
              ⊆ ((LinearMap.range F).topologicalClosure : Set _) :=
            closure_minimal (fun y hy => hsub hy)
              (Submodule.isClosed_topologicalClosure _)
          exact hcl hx
        have := Submodule.dense_iff_topologicalClosure_eq_top.2 htop
        simpa [DenseRange, LinearMap.coe_range] using this
      have hsurj : Function.Surjective (splitIso μ n) := by
        intro g
        refine ⟨Lp.compMeasurePreservingₗᵢ ℂ
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) 0).symm
          (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm g, ?_⟩
        refine Lp.ext ?_
        have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
        have h1 := Lp.coeFn_compMeasurePreserving
          (Lp.compMeasurePreservingₗᵢ ℂ
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) 0).symm hmp.symm g) hmp
        have h2 := (Lp.coeFn_compMeasurePreserving g hmp.symm).comp_tendsto
          hmp.quasiMeasurePreserving.tendsto_ae
        rw [splitIso]
        filter_upwards [h1, h2] with x hx1 hx2
        simp only [Function.comp_apply] at hx1 hx2
        exact hx1.trans (hx2.trans (by rw [MeasurableEquiv.symm_apply_apply]))
      have hcomp : (embPow μ (n + 1) : _ → _) = (splitIso μ n) ∘ F := rfl
      rw [DenseRange, hcomp]
      show Dense (Set.range ((splitIso μ n) ∘ (F : _ → _)))
      rw [Set.range_comp]
      exact hsurj.denseRange.dense_image (splitIso μ n).continuous hdF

/-- **The `n`-particle sector identification**: the completed `n`-fold tensor power of
`L²(μ)` is unitarily equivalent to `L²(μ^{⊗n})`, by the unique unitary extending `embPow n`
(`f₁ ⊗ ⋯ ⊗ fₙ ↦ (x ↦ f₁(x₀) ⋯ fₙ(x_{n−1}))`). -/
def tensorPowUnitary (n : ℕ) : fockSector (L2Space μ) n ≃ₗᵢ[ℂ] Lp ℂ 2 (piMeasure μ n) :=
  (LinearEquiv.refl ℂ ((L2Space μ).pow n).carrier).extendOfIsometry
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ)).toLinearMap (embPow μ n).toLinearMap
    UniformSpace.Completion.denseRange_coe (denseRange_embPow μ n)
    (fun x => by simp)



end

section Relabel

/-- **The unitary of a measure-preserving change of variables with a measure-preserving
inverse**: composition with `f` is a unitary `L²(ν) ≃ₗᵢ L²(μ)`. -/
noncomputable def mpEquivUnitary {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μa : Measure α}
    {μb : Measure β} (f : α → β) (g : β → α) (hf : MeasurePreserving f μa μb)
    (hg : MeasurePreserving g μb μa) (hgf : ∀ x, g (f x) = x) :
    Lp ℂ 2 μb ≃ₗᵢ[ℂ] Lp ℂ 2 μa :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ f hf) fun h => by
    refine ⟨Lp.compMeasurePreservingₗᵢ ℂ g hg h, ?_⟩
    refine Lp.ext ?_
    have h1 := Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreservingₗᵢ ℂ g hg h) hf
    have h2 := (Lp.coeFn_compMeasurePreserving h hg).comp_tendsto
      hf.quasiMeasurePreserving.tendsto_ae
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Function.comp_apply] at hx1 hx2
    exact hx1.trans (hx2.trans (by rw [hgf]))



/-- Uncurrying `(Fin n → Fin d → ℝ) → (Fin n × Fin d → ℝ)` preserves Lebesgue measure. -/
theorem measurePreserving_uncurry_fin (n d : ℕ) :
    MeasurePreserving (fun x : Fin n → Fin d → ℝ => Function.uncurry x)
      (volume : Measure (Fin n → Fin d → ℝ)) (volume : Measure (Fin n × Fin d → ℝ)) := by
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun x : Fin n → Fin d → ℝ => Function.uncurry x) ⁻¹' Set.univ.pi s
      = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext x
    simp [Set.mem_pi, Function.uncurry]
  have hmeas : Measurable fun x : Fin n → Fin d → ℝ => Function.uncurry x :=
    (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.measurable
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre]
  rw [show (volume : Measure (Fin n → Fin d → ℝ)) = Measure.pi fun _ => Measure.pi fun _ => volume
    from rfl, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_prod_type']

/-- The relabelling `ℝ^{n·d} → (ℝ^d)ⁿ`, `v ↦ (i ↦ (j ↦ v_{(i,j)}))`. -/
def blockSplit (n d : ℕ) (v : EuclideanSpace ℝ (Fin (n * d))) : Fin n → EuclideanSpace ℝ (Fin d) :=
  fun i => WithLp.toLp 2 fun j => WithLp.ofLp v (finProdFinEquiv (i, j))

/-- Its inverse `(ℝ^d)ⁿ → ℝ^{n·d}`. -/
def blockJoin (n d : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (n * d)) :=
  WithLp.toLp 2 fun k => WithLp.ofLp (x (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2

theorem blockJoin_blockSplit (n d : ℕ) (v : EuclideanSpace ℝ (Fin (n * d))) :
    blockJoin n d (blockSplit n d v) = v := by
  unfold blockJoin blockSplit
  simp only [Prod.mk.eta, Equiv.apply_symm_apply, WithLp.toLp_ofLp]

theorem blockSplit_blockJoin (n d : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    blockSplit n d (blockJoin n d x) = x := by
  funext i
  unfold blockJoin blockSplit
  simp only [Equiv.symm_apply_apply, WithLp.toLp_ofLp]

theorem measurePreserving_blockSplit (n d : ℕ) :
    MeasurePreserving (blockSplit n d) volume volume := by
  have h1 : MeasurePreserving (fun v : EuclideanSpace ℝ (Fin (n * d)) => WithLp.ofLp v)
      volume volume := PiLp.volume_preserving_ofLp _
  have h2 : MeasurePreserving (fun y : Fin (n * d) → ℝ => fun p : Fin n × Fin d => y (finProdFinEquiv p))
      volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (n * d) => ℝ) finProdFinEquiv).symm
  have h3 : MeasurePreserving (fun z : Fin n × Fin d → ℝ => Function.curry z) volume volume :=
    (measurePreserving_uncurry_fin n d).symm (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm
  have h4 : MeasurePreserving (fun w : Fin n → Fin d → ℝ => fun i => WithLp.toLp 2 (w i))
      (volume : Measure (Fin n → Fin d → ℝ)) (volume : Measure (Fin n → EuclideanSpace ℝ (Fin d))) :=
    volume_preserving_pi fun _ => PiLp.volume_preserving_toLp _
  exact h4.comp (h3.comp (h2.comp h1))

theorem measurePreserving_blockJoin (n d : ℕ) :
    MeasurePreserving (blockJoin n d) volume volume := by
  have hm : Measurable (blockJoin n d) := by
    unfold blockJoin
    fun_prop
  let e : EuclideanSpace ℝ (Fin (n * d)) ≃ᵐ (Fin n → EuclideanSpace ℝ (Fin d)) :=
    { toFun := blockSplit n d
      invFun := blockJoin n d
      left_inv := blockJoin_blockSplit n d
      right_inv := blockSplit_blockJoin n d
      measurable_toFun := (measurePreserving_blockSplit n d).measurable
      measurable_invFun := hm }
  exact (measurePreserving_blockSplit n d).symm e

end Relabel

section Lebesgue

open BookProof.HermiteProductCore



/-- **The Lebesgue instance**: the `n`-particle sector over `L²(ℝ^d)` is `L²((ℝ^d)ⁿ)` with
Lebesgue measure. -/
noncomputable def l2dSectorUnitary (d n : ℕ) :
    fockSector (BookProof.YangMillsNonAbelianEsa.L2dSpace d) n ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (Fin n → Vd d)) :=
  tensorPowUnitary (volume : Measure (Vd d)) n

/-- The relabelling unitary `L²((ℝ^d)ⁿ) ≅ L²(ℝ^{n·d})`, `(U f)(v) = f (blockSplit v)`. -/
noncomputable def parcelRelabel (d n : ℕ) :
    Lp ℂ 2 (volume : Measure (Fin n → Vd d)) ≃ₗᵢ[ℂ] L2d (n * d) :=
  mpEquivUnitary (blockSplit n d) (blockJoin n d) (measurePreserving_blockSplit n d)
    (measurePreserving_blockJoin n d) (blockJoin_blockSplit n d)

/-- **The parcel-sector identification**: the `n`-particle sector over `L²(ℝ^d)` is the
`n`-parcel space `L²(ℝ^{n·d})` (`L2d (n * d)`, the sector space of the Navier–Stokes parcel
Hamiltonians for `d = 6`).  On pure tensors,
`f₁ ⊗ ⋯ ⊗ fₙ ↦ (v ↦ f₁(v_{(0,·)}) ⋯ fₙ(v_{(n−1,·)}))`. -/
noncomputable def parcelSectorUnitary (d n : ℕ) :
    fockSector (BookProof.YangMillsNonAbelianEsa.L2dSpace d) n ≃ₗᵢ[ℂ] L2d (n * d) :=
  (l2dSectorUnitary d n).trans (parcelRelabel d n)

/-- The Navier–Stokes instance `d = 6`: `L²(ℝ⁶)^{⊗̂n} ≅ L²(ℝ^{6n})`. -/
noncomputable def nsParcelSectorUnitary (n : ℕ) :
    fockSector (BookProof.YangMillsNonAbelianEsa.L2dSpace 6) n ≃ₗᵢ[ℂ] L2d (n * 6) :=
  parcelSectorUnitary 6 n

theorem memℓp_two_map {ι : Type*} {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedAddCommGroup (F i)] (e : ∀ i, E i → F i) (he : ∀ i x, ‖e i x‖ = ‖x‖)
    (f : lp E 2) : Memℓp (fun i => e i (f i)) 2 :=
  memℓp_gen (by
    simpa only [he] using (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal))

/-- A family of unitaries between the fibres is a unitary between the `ℓ²` direct sums. -/
noncomputable def lpFiberwise {ι : Type*} {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℂ (F i)] (e : ∀ i, E i ≃ₗᵢ[ℂ] F i) : lp E 2 ≃ₗᵢ[ℂ] lp F 2 where
  toFun f := ⟨fun i => e i (f i), memℓp_two_map (fun i => e i) (fun i => (e i).norm_map) f⟩
  invFun g := ⟨fun i => (e i).symm (g i),
    memℓp_two_map (fun i => (e i).symm) (fun i => (e i).symm.norm_map) g⟩
  left_inv f := by ext i; simp
  right_inv g := by ext i; simp
  map_add' f g := by
    ext i
    simp only [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    ext i
    simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
  norm_map' f := by
    have hp : 0 < (2 : ENNReal).toReal := by norm_num
    change ‖(⟨fun i => e i (f i), memℓp_two_map (fun i => e i) (fun i => (e i).norm_map) f⟩ :
      lp F 2)‖ = ‖f‖
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    simp only [LinearIsometryEquiv.norm_map]

/-- **The Fock-space identification for the Navier–Stokes parcels**: the Fock space
`⊕ₙ L²(ℝ⁶)^{⊗̂n}` of the second-quantization chapters is unitarily equivalent to the parcel Fock
space `⊕ₙ L²(ℝ^{6n})` on which `nsRedFullFockHam` acts (`NsFourierElimination.nsRedFockSpace`
is by definition `lp (fun n => L2d (n * 6)) 2`). -/
noncomputable def nsFockUnitary :
    lp (fun n : ℕ => fockSector (BookProof.YangMillsNonAbelianEsa.L2dSpace 6) n) 2
      ≃ₗᵢ[ℂ] lp (fun n : ℕ => L2d (n * 6)) 2 :=
  lpFiberwise nsParcelSectorUnitary

end Lebesgue

end BookProof.L2TensorPower


