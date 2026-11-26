-- Prove2me | solution 1 for Auto.multilinear_interpolation_two_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:27.353868+00:00
-- url     : https://prove2.me/submissions/46f3176a-a868-407a-b188-3910146401d8

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
public import Theorems.Thm_Auto_multilinear_interpolation_two_endpoint_normalized
section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
private theorem aux_eLpNorm_normalize_simpleFunc
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) (p : ENNReal)
    (hzero : eLpNorm (f : X → ℂ) p μ ≠ 0)
    (htop : eLpNorm (f : X → ℂ) p μ ≠ ∞) :
    eLpNorm (((eLpNorm (f : X → ℂ) p μ).toReal⁻¹ : ℂ) • f : X → ℂ) p μ = 1 := by
  let N : ENNReal := eLpNorm (f : X → ℂ) p μ
  have hNpos : 0 < N.toReal := ENNReal.toReal_pos hzero htop
  rw [eLpNorm_const_smul]
  change ‖(N.toReal⁻¹ : ℂ)‖ₑ * N = 1
  have hnorm : ‖(N.toReal⁻¹ : ℂ)‖ₑ = ENNReal.ofReal (N.toReal⁻¹) := by
    rw [← ofReal_norm]
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hNpos.le)]
  rw [hnorm, ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_toReal htop]
  exact ENNReal.inv_mul_cancel hzero htop
private theorem aux_multilinear_rescale_tail
    {m : ℕ} {X Y : Type*} [MeasurableSpace X]
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Y → ℂ))
    (g : Fin (m + 1) → SimpleFunc X ℂ) (c : Fin m → ℂ) :
    B (Fin.cons (g 0) (fun i ↦ c i • g i.succ)) =
      (∏ i, c i) • B g := by
  change B.curryLeft (g 0) (fun i ↦ c i • g i.succ) = (∏ i, c i) • B g
  rw [(B.curryLeft (g 0)).map_smul_univ]
  congr 1
  change B (Fin.cons (g 0) (fun i ↦ g i.succ)) = B g
  exact congrArg B (Fin.cons_self_tail g)
private theorem aux_enorm_prod_inv_toReal
    {m : ℕ} (N : Fin m → ENNReal)
    (hzero : ∀ i, N i ≠ 0) (htop : ∀ i, N i ≠ ∞) :
    ‖∏ i, ((N i).toReal⁻¹ : ℂ)‖ₑ = (∏ i, N i)⁻¹ := by
  have hpos : ∀ i, 0 < (N i).toReal := fun i ↦ ENNReal.toReal_pos (hzero i) (htop i)
  have hscalar : ∀ i, ‖((N i).toReal⁻¹ : ℂ)‖ₑ = (N i)⁻¹ := by
    intro i
    rw [← ofReal_norm, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (hpos i).le), ENNReal.ofReal_inv_of_pos (hpos i),
      ENNReal.ofReal_toReal (htop i)]
  calc
    ‖∏ i, ((N i).toReal⁻¹ : ℂ)‖ₑ = ENNReal.ofReal ‖∏ i, ((N i).toReal⁻¹ : ℂ)‖ :=
      (ofReal_norm _).symm
    _ = ENNReal.ofReal (∏ i, ‖((N i).toReal⁻¹ : ℂ)‖) := by rw [norm_prod]
    _ = ∏ i, ENNReal.ofReal ‖((N i).toReal⁻¹ : ℂ)‖ := by
      rw [ENNReal.ofReal_prod_of_nonneg]
      intro i hi
      exact norm_nonneg _
    _ = ∏ i, (N i)⁻¹ := by
      apply Finset.prod_congr rfl
      intro i hi
      simpa only [ofReal_norm] using hscalar i
    _ = (∏ i, N i)⁻¹ := by
      rw [ENNReal.prod_inv_distrib]
      intro i hi j hj hij
      exact Or.inl (hzero i)
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
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Y → ℂ))
    {p₀ p₁ p : Fin (m + 1) → ENNReal} {q : ENNReal} {θ M₀ M₁ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp₀ : ∀ i, 1 ≤ p₀ i) (hp₁ : ∀ i, 1 ≤ p₁ i) (hp : ∀ i, 1 ≤ p i)
    (hp_top : ∀ i, p i ≠ ∞)
    (hint : ∀ i, (p i)⁻¹ = ENNReal.ofReal (1 - θ) * (p₀ i)⁻¹ +
      ENNReal.ofReal θ * (p₁ i)⁻¹)
    (hq : 1 ≤ q) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hB_measurable : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) → Measurable (B u))
    (hB_pair_integrable : ∀ (u : Fin (m + 1) → SimpleFunc X ℂ)
      (h : SimpleFunc Y ℂ),
      (∀ i, Integrable (u i : X → ℂ) μ) → Integrable (h : Y → ℂ) ν →
        Integrable (fun y ↦ B u y * h y) ν)
    (hB_bound₀ : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) →
        eLpNorm (B u) q ν ≤ ENNReal.ofReal M₀ * ∏ i,
          eLpNorm (u i : X → ℂ) (p₀ i) μ)
    (hB_bound₁ : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) →
        eLpNorm (B u) q ν ≤ ENNReal.ofReal M₁ * ∏ i,
          eLpNorm (u i : X → ℂ) (p₁ i) μ)
    (hzero : ∀ (u : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1)),
      eLpNorm (u i : X → ℂ) (p i) μ = 0 → eLpNorm (B u) q ν = 0)
    (g : Fin (m + 1) → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ) :
    eLpNorm (B g) q ν ≤
      ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
        eLpNorm (g 0 : X → ℂ) (p 0) μ *
          ∏ i : Fin m, eLpNorm (g i.succ : X → ℂ) (p i.succ) μ := by
  let N : Fin m → ENNReal := fun i ↦ eLpNorm (g i.succ : X → ℂ) (p i.succ) μ
  by_cases hNzero : ∃ i, N i = 0
  · rcases hNzero with ⟨i, hi⟩
    have hBgzero : eLpNorm (B g) q ν = 0 := hzero g i.succ hi
    have hprodzero : ∏ i, N i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hBgzero, hprodzero]
    simp
  have hNnezero : ∀ i, N i ≠ 0 := fun i hi ↦ hNzero ⟨i, hi⟩
  by_cases hNtop : ∃ i, N i = ∞
  · rcases hNtop with ⟨i, hi⟩
    by_cases hgzero : eLpNorm (g 0 : X → ℂ) (p 0) μ = 0
    · have hBgzero : eLpNorm (B g) q ν = 0 := hzero g 0 hgzero
      rw [hBgzero]
      simp
    have hprodt : ∏ i, N i = ∞ :=
      WithTop.prod_eq_top (Finset.mem_univ i) hi (fun j hj ↦ hNnezero j)
    have hKpos : 0 < Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ :=
      mul_pos (Real.rpow_pos_of_pos hM₀ _) (Real.rpow_pos_of_pos hM₁ _)
    have hKne : ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hKpos
    calc
      eLpNorm (B g) q ν ≤ ∞ := le_top
      _ = ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (g 0 : X → ℂ) (p 0) μ * ∏ i, N i := by
        rw [hprodt, ENNReal.mul_top (mul_ne_zero hKne hgzero)]
  have hNfinite : ∀ i, N i ≠ ∞ := fun i hi ↦ hNtop ⟨i, hi⟩
  let c : Fin m → ℂ := fun i ↦ ((N i).toReal⁻¹ : ℂ)
  let g' : Fin (m + 1) → SimpleFunc X ℂ :=
    Fin.cons (g 0) (fun i ↦ c i • g i.succ)
  have hg' : ∀ i, Integrable (g' i : X → ℂ) μ := by
    intro i
    refine Fin.cases (hg 0) ?_ i
    intro j
    change Integrable (fun x ↦ c j * (g j.succ) x) μ
    exact (hg j.succ).const_mul (c j)
  have hgnorm' : ∀ i : Fin m, eLpNorm (g' i.succ : X → ℂ) (p i.succ) μ ≤ 1 := by
    intro i
    simpa only [g', c, N, Fin.cons_succ, SimpleFunc.coe_smul] using
      (aux_eLpNorm_normalize_simpleFunc (g i.succ) (p i.succ) (hNnezero i) (hNfinite i)).le
  obtain ⟨hmem, hbound⟩ := multilinear_interpolation_two_endpoint_normalized B hθ hp₀ hp₁ hp
    hp_top hint hq hM₀ hM₁ hB_measurable hB_pair_integrable hB_bound₀ hB_bound₁ g' hg' hgnorm'
  have hBg' : B g' = (∏ i, c i) • B g := by
    exact aux_multilinear_rescale_tail B g c
  have hscaled : (∏ i, N i)⁻¹ * eLpNorm (B g) q ν ≤
      ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
        eLpNorm (g 0 : X → ℂ) (p 0) μ := by
    calc
      (∏ i, N i)⁻¹ * eLpNorm (B g) q ν = eLpNorm (B g') q ν := by
        rw [hBg', eLpNorm_const_smul]
        change (∏ i, N i)⁻¹ * eLpNorm (B g) q ν =
          ‖∏ i, ((N i).toReal⁻¹ : ℂ)‖ₑ * eLpNorm (B g) q ν
        rw [aux_enorm_prod_inv_toReal N hNnezero hNfinite]
      _ ≤ ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (g' 0 : X → ℂ) (p 0) μ := hbound
      _ = ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (g 0 : X → ℂ) (p 0) μ := by simp only [g', Fin.cons_zero]
  have hprodnezero : (∏ i, N i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi ↦ hNnezero i
  have hprodfinite : (∏ i, N i) ≠ ∞ :=
    ENNReal.prod_ne_top fun i hi ↦ hNfinite i
  calc
    eLpNorm (B g) q ν ≤ (∏ i, N i) *
        (ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (g 0 : X → ℂ) (p 0) μ) :=
      (ENNReal.inv_mul_le_iff hprodnezero hprodfinite).mp hscaled
    _ = ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
        eLpNorm (g 0 : X → ℂ) (p 0) μ * ∏ i, N i := by ac_rfl
    _ = ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
        eLpNorm (g 0 : X → ℂ) (p 0) μ *
          ∏ i : Fin m, eLpNorm (g i.succ : X → ℂ) (p i.succ) μ := by rfl
end Auto
