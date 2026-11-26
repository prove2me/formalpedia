-- Prove2me | solution 1 for Auto.multilinear_interpolation_convexHull_Lp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:41.670799+00:00
-- url     : https://prove2.me/submissions/8b830654-0de4-4ed7-81a2-d88368aab894

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
public import Theorems.Thm_Auto_multilinear_interpolation_convexHull
section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
private theorem aux_aeeqFunMkLinear_representative {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} :
    (aux_aeeqFunMkLinear (Y := Y) (ν := ν)).comp
      (aux_aeeqFunLinearRepresentative (Y := Y) (ν := ν)) = LinearMap.id :=
  Classical.choose_spec <|
    (aux_aeeqFunMkLinear (Y := Y) (ν := ν)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top_of_surjective _
        (aux_aeeqFunMkLinear_surjective (Y := Y) (ν := ν)))
private theorem aux_lpLinearRepresentative_mk {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} (f : Lp ℂ 2 ν) :
    AEEqFun.mk (aux_lpLinearRepresentative (Y := Y) (ν := ν) f)
      (aux_lpLinearRepresentative_stronglyMeasurable (Y := Y) (ν := ν) f).aestronglyMeasurable =
        f.1 := by
  change (aux_aeeqFunMkLinear (Y := Y) (ν := ν))
    ((aux_aeeqFunLinearRepresentative (Y := Y) (ν := ν))
      ((Lp.LpSubmodule ℂ ℂ 2 ν).subtype f)) = f.1
  have hsub : (Lp.LpSubmodule ℂ ℂ 2 ν).subtype f = f.1 := rfl
  rw [hsub]
  have h := LinearMap.congr_fun
    (aux_aeeqFunMkLinear_representative (Y := Y) (ν := ν)) f.1
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
private theorem aux_lpLinearRepresentative_ae {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} (f : Lp ℂ 2 ν) :
    aux_lpLinearRepresentative (Y := Y) (ν := ν) f =ᵐ[ν] f := by
  let r := aux_lpAEEqFunRepresentative (Y := Y) (ν := ν) f
  have hr : AEStronglyMeasurable (r : Y → ℂ) ν := r.property.aestronglyMeasurable
  calc
    aux_lpLinearRepresentative (Y := Y) (ν := ν) f =ᵐ[ν]
        AEEqFun.mk (aux_lpLinearRepresentative (Y := Y) (ν := ν) f) hr :=
      (AEEqFun.coeFn_mk _ hr).symm
    _ =ᵐ[ν] f.1 := by
      rw [aux_lpLinearRepresentative_mk (Y := Y) (ν := ν) f]
    _ =ᵐ[ν] f := Filter.EventuallyEq.rfl
private theorem aux_multilinearLpRepresentative_ae {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommMonoid (E i)] [∀ i, Module ℂ (E i)] {Y : Type*}
    [MeasurableSpace Y] {ν : Measure Y}
    (B : MultilinearMap ℂ E (Lp ℂ 2 ν)) (u : ∀ i, E i) :
    aux_multilinearLpRepresentative (Y := Y) (ν := ν) B u =ᵐ[ν] B u :=
  aux_lpLinearRepresentative_ae (Y := Y) (ν := ν) (B u)
private theorem aux_multilinearLpRepresentative_stronglyMeasurable {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommMonoid (E i)] [∀ i, Module ℂ (E i)] {Y : Type*}
    [MeasurableSpace Y] {ν : Measure Y}
    (B : MultilinearMap ℂ E (Lp ℂ 2 ν)) (u : ∀ i, E i) :
    StronglyMeasurable (aux_multilinearLpRepresentative (Y := Y) (ν := ν) B u) :=
  aux_lpLinearRepresentative_stronglyMeasurable (Y := Y) (ν := ν) (B u)
private theorem aux_multilinearLpRepresentative_memLp {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommMonoid (E i)] [∀ i, Module ℂ (E i)] {Y : Type*}
    [MeasurableSpace Y] {ν : Measure Y}
    (B : MultilinearMap ℂ E (Lp ℂ 2 ν)) (u : ∀ i, E i) :
    MemLp (aux_multilinearLpRepresentative (Y := Y) (ν := ν) B u) 2 ν :=
  MemLp.ae_eq (aux_multilinearLpRepresentative_ae (Y := Y) (ν := ν) B u).symm (Lp.memLp (B u))
private theorem aux_eLpNorm_multilinearLpRepresentative {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommMonoid (E i)] [∀ i, Module ℂ (E i)] {Y : Type*}
    [MeasurableSpace Y] {ν : Measure Y}
    (B : MultilinearMap ℂ E (Lp ℂ 2 ν)) (u : ∀ i, E i) :
    eLpNorm (aux_multilinearLpRepresentative (Y := Y) (ν := ν) B u) 2 ν =
      eLpNorm (B u : Y → ℂ) 2 ν :=
  eLpNorm_congr_ae (aux_multilinearLpRepresentative_ae (Y := Y) (ν := ν) B u)
section
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {m : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Lp ℂ 2 ν))
    (A : ℝ) (hA : 0 < A)
    (S : Set (Fin (m + 1) → ℝ))
    (hSbox : ∀ u ∈ S, ∀ i, 0 < u i ∧ u i ≤ 1)
    (hendpoint : ∀ u ∈ S, ∀ g : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (g i : X → ℂ) μ) →
        ‖B g‖ₑ ≤ ENNReal.ofReal A * ∏ i,
          eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ)
    (hzero : ∀ (u : Fin (m + 1) → ℝ), (∀ i, 0 < u i ∧ u i ≤ 1) →
      ∀ (g : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1)),
        eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ = 0 →
          ‖B g‖ₑ = 0)
    (u : Fin (m + 1) → ℝ) (hu : u ∈ convexHull ℝ S)
    (g : Fin (m + 1) → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ) :
    ‖B g‖ₑ ≤ ENNReal.ofReal A * ∏ i,
      eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ := by
  let B' := aux_multilinearLpRepresentative (Y := Y) (ν := ν) B
  have hB_measurable : ∀ r : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (r i : X → ℂ) μ) → Measurable (B' r) := by
    intro r hr
    exact (aux_multilinearLpRepresentative_stronglyMeasurable (Y := Y) (ν := ν) B r).measurable
  have hB_pair_integrable : ∀ (r : Fin (m + 1) → SimpleFunc X ℂ)
      (h : SimpleFunc Y ℂ),
      (∀ i, Integrable (r i : X → ℂ) μ) → Integrable (h : Y → ℂ) ν →
        Integrable (fun y ↦ B' r y * h y) ν := by
    intro r h hr hh
    have hBr : MemLp (B' r) 2 ν :=
      aux_multilinearLpRepresentative_memLp (Y := Y) (ν := ν) B r
    have hh2 : MemLp (h : Y → ℂ) 2 ν := by
      rw [SimpleFunc.memLp_iff_integrable (p := (2 : ENNReal)) (by norm_num)
        ENNReal.ofNat_ne_top]
      exact hh
    apply (hBr.integrable_mul hh2).congr
    filter_upwards with y
    exact Pi.mul_apply (B' r) (h : Y → ℂ) y
  have hendpoint' : ∀ w ∈ S, ∀ r : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (r i : X → ℂ) μ) →
        eLpNorm (B' r) 2 ν ≤ ENNReal.ofReal A * ∏ i,
          eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal w i) μ := by
    intro w hw r hr
    change eLpNorm (aux_multilinearLpRepresentative (Y := Y) (ν := ν) B r) 2 ν ≤ _
    rw [aux_eLpNorm_multilinearLpRepresentative]
    rw [← Lp.enorm_def]
    exact hendpoint w hw r hr
  have hzero' : ∀ (w : Fin (m + 1) → ℝ), (∀ i, 0 < w i ∧ w i ≤ 1) →
      ∀ (r : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1)),
        eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal w i) μ = 0 →
          eLpNorm (B' r) 2 ν = 0 := by
    intro w hw r i hri
    change eLpNorm (aux_multilinearLpRepresentative (Y := Y) (ν := ν) B r) 2 ν = 0
    rw [aux_eLpNorm_multilinearLpRepresentative]
    rw [← Lp.enorm_def]
    exact hzero w hw r i hri
  have h := multilinear_interpolation_convexHull B' 2 (by norm_num) A hA
    hB_measurable hB_pair_integrable S hSbox hendpoint' hzero' u hu g hg
  rw [Lp.enorm_def]
  rw [← aux_eLpNorm_multilinearLpRepresentative (Y := Y) (ν := ν) B g]
  exact h
end Auto
