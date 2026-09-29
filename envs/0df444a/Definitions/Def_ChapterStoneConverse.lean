-- Prove2me | Definitions.Def_ChapterStoneConverse
-- name    : ChapterStoneConverse
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:52:52.682519+00:00
-- url     : https://prove2.me/theorems/15b3aa1b-fac5-4586-8d20-18237d2bb21a
-- title:
--   Given a weakly measurable one-parameter unitary group `U` on a *separable* Hilbert space we already know (von Neumann's ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.StoneConverse`, source chapter `BookProof/ChapterStoneConverse.lean`).
--
--   Given a weakly measurable one-parameter unitary group `U` on a *separable* Hilbert space we already know (von Neumann's theorem, `ChapterStoneMeasurable`) that `U` is strongly continuous. Here we construct its **infinitesimal generator**
--
--   `A x = i (d/dt)|₀ U t x`,
--
--   defined on the domain of vectors whose orbit is differentiable at `0`, and prove that `A` is a densely defined self-adjoint operator.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneConverse.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterStoneEvolution
import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterStoneGroup
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterUnitaryTransport

import Mathlib

import Mathlib

/-!
# The general Stone theorem, part VII: the generator of a unitary group

Given a weakly measurable one-parameter unitary group `U` on a *separable* Hilbert space we
already know (von Neumann's theorem, `ChapterStoneMeasurable`) that `U` is strongly
continuous.  Here we construct its **infinitesimal generator**

`A x = i (d/dt)|₀ U t x`,

defined on the domain of vectors whose orbit is differentiable at `0`, and prove that `A`
is a densely defined self-adjoint operator.
-/

open scoped InnerProductSpace
open Filter Topology MeasureTheory

namespace BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Differentiating a Hilbert-space valued curve inside an inner product. -/
theorem hasDerivAt_inner_right {f : ℝ → H} {f' : H} {t : ℝ} (y : H) (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => ⟪y, f s⟫_ℂ) (⟪y, f'⟫_ℂ) t :=
  ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

/-- Complex conjugation may be pushed through a derivative. -/
theorem hasDerivAt_conj {g : ℝ → ℂ} {g' : ℂ} {t : ℝ} (h : HasDerivAt g g' t) :
    HasDerivAt (fun s => (starRingEnd ℂ) (g s)) ((starRingEnd ℂ) g') t :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t h

/-- A continuous linear map may be pushed through a derivative. -/
theorem hasDerivAt_clm {f : ℝ → H} {f' : H} {t : ℝ} (L : H →L[ℂ] H) (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => L (f s)) (L f') t :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

namespace WeakMeasurableUnitaryGroup

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)

/-! ## The domain and the generator -/

/-- The domain of the infinitesimal generator: the vectors whose orbit is differentiable. -/
def genDomain : Submodule ℂ H where
  carrier := {x : H | DifferentiableAt ℝ (fun t : ℝ => G.U t x) 0}
  add_mem' := by
    intro x y hx hy
    have h : (fun t : ℝ => G.U t (x + y)) = fun t : ℝ => G.U t x + G.U t y := by
      funext t; exact ContinuousLinearMap.map_add (G.U t) x y
    change DifferentiableAt ℝ (fun t : ℝ => G.U t (x + y)) 0
    rw [h]
    exact hx.add hy
  zero_mem' := by
    have h : (fun t : ℝ => G.U t (0 : H)) = fun _ : ℝ => (0 : H) := by
      funext t; exact ContinuousLinearMap.map_zero (G.U t)
    change DifferentiableAt ℝ (fun t : ℝ => G.U t (0 : H)) 0
    rw [h]
    exact differentiableAt_const _
  smul_mem' := by
    intro c x hx
    have h : (fun t : ℝ => G.U t (c • x)) = fun t : ℝ => c • G.U t x := by
      funext t; exact ContinuousLinearMap.map_smul (G.U t) c x
    change DifferentiableAt ℝ (fun t : ℝ => G.U t (c • x)) 0
    rw [h]
    exact hx.const_smul c

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem mem_genDomain_iff (x : H) :
    x ∈ G.genDomain ↔ DifferentiableAt ℝ (fun t : ℝ => G.U t x) 0 := Iff.rfl

/-- The **infinitesimal generator** `A = i d/dt|₀ U t`. -/
noncomputable def genOp : G.genDomain →ₗ[ℂ] H where
  toFun x := Complex.I • deriv (fun t : ℝ => G.U t (x : H)) 0
  map_add' := by
    intro x y
    have h : (fun t : ℝ => G.U t ((x + y : G.genDomain) : H))
        = fun t : ℝ => G.U t (x : H) + G.U t (y : H) := by
      funext t
      rw [Submodule.coe_add]
      exact ContinuousLinearMap.map_add (G.U t) _ _
    have hd : deriv (fun t : ℝ => G.U t (x : H) + G.U t (y : H)) 0
        = deriv (fun t : ℝ => G.U t (x : H)) 0 + deriv (fun t : ℝ => G.U t (y : H)) 0 :=
      (x.2.hasDerivAt.add y.2.hasDerivAt).deriv
    change Complex.I • deriv (fun t : ℝ => G.U t ((x + y : G.genDomain) : H)) 0 = _
    rw [h, hd, smul_add]
  map_smul' := by
    intro c x
    have h : (fun t : ℝ => G.U t ((c • x : G.genDomain) : H))
        = fun t : ℝ => c • G.U t (x : H) := by
      funext t
      rw [Submodule.coe_smul]
      exact ContinuousLinearMap.map_smul (G.U t) c _
    have hd : deriv (fun t : ℝ => c • G.U t (x : H)) 0
        = c • deriv (fun t : ℝ => G.U t (x : H)) 0 :=
      (x.2.hasDerivAt.const_smul c).deriv
    change Complex.I • deriv (fun t : ℝ => G.U t ((c • x : G.genDomain) : H)) 0 = _
    rw [h, hd]
    simp only [RingHom.id_apply]
    rw [smul_comm]

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem genOp_apply (x : G.genDomain) :
    G.genOp x = Complex.I • deriv (fun t : ℝ => G.U t (x : H)) 0 := rfl



omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem genOp_eq_of_hasDerivAt {x : G.genDomain} {y : H}
    (h : HasDerivAt (fun t : ℝ => G.U t (x : H)) ((-Complex.I) • y) 0) : G.genOp x = y := by
  rw [genOp_apply, h.deriv, smul_smul]
  simp

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The defining differential equation at `t = 0`. -/
theorem hasDerivAt_orbit_zero (x : G.genDomain) :
    HasDerivAt (fun t : ℝ => G.U t (x : H)) ((-Complex.I) • G.genOp x) 0 := by
  have h : DifferentiableAt ℝ (fun t : ℝ => G.U t (x : H)) 0 := x.2
  have := h.hasDerivAt
  rw [genOp_apply, smul_smul]
  simpa using this

/-! ## Invariance of the domain -/

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem apply_mem_genDomain (s : ℝ) (x : G.genDomain) : G.U s (x : H) ∈ G.genDomain := by
  have h : (fun t : ℝ => G.U t (G.U s (x : H))) = fun t : ℝ => G.U s (G.U t (x : H)) := by
    funext t
    rw [G.apply_apply, G.apply_apply, add_comm]
  rw [mem_genDomain_iff, h]
  exact (hasDerivAt_clm (G.U s) (G.hasDerivAt_orbit_zero x)).differentiableAt

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem genOp_apply_comm (s : ℝ) (x : G.genDomain) :
    G.genOp ⟨G.U s (x : H), G.apply_mem_genDomain s x⟩ = G.U s (G.genOp x) := by
  refine G.genOp_eq_of_hasDerivAt ?_
  have h : (fun t : ℝ => G.U t (G.U s (x : H))) = fun t : ℝ => G.U s (G.U t (x : H)) := by
    funext t
    rw [G.apply_apply, G.apply_apply, add_comm]
  rw [h]
  have := hasDerivAt_clm (G.U s) (G.hasDerivAt_orbit_zero x)
  simpa using this

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The Schrödinger equation at an arbitrary time. -/
theorem hasDerivAt_orbit (x : G.genDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => G.U s (x : H)) ((-Complex.I) • G.U t (G.genOp x)) t := by
  have hz : HasDerivAt (fun u : ℝ => G.U t (G.U u (x : H)))
      ((-Complex.I) • G.U t (G.genOp x)) (t - t) := by
    have h0 := hasDerivAt_clm (G.U t) (G.hasDerivAt_orbit_zero x)
    rw [map_smul] at h0
    simpa using h0
  have hshift : HasDerivAt (fun s : ℝ => G.U t (G.U (s - t) (x : H)))
      ((-Complex.I) • G.U t (G.genOp x)) t := HasDerivAt.comp_sub_const t t hz
  refine hshift.congr_of_eventuallyEq ?_
  filter_upwards with s
  rw [G.apply_apply]
  ring_nf

/-! ## The averaged vectors lie in the domain -/

/-- The Bochner average `∫₀ᵃ U t x dt`. -/
noncomputable def bAvg (x : H) (a : ℝ) : H := ∫ t in (0 : ℝ)..a, G.U t x

theorem hasDerivAt_bAvg (x : H) (a : ℝ) :
    HasDerivAt (fun u : ℝ => G.bAvg x u) (G.U a x) a := by
  have hc : Continuous fun t : ℝ => G.U t x := G.continuous_apply x
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 a)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem apply_bAvg (s a : ℝ) (x : H) :
    G.U s (G.bAvg x a) = G.bAvg x (s + a) - G.bAvg x s := by
  have hc : Continuous fun t : ℝ => G.U t x := G.continuous_apply x
  have h1 : G.U s (G.bAvg x a) = ∫ t in (0 : ℝ)..a, G.U s (G.U t x) := by
    rw [bAvg]
    exact ((G.U s).intervalIntegral_comp_comm (hc.intervalIntegrable 0 a)).symm
  have h2 : (∫ t in (0 : ℝ)..a, G.U s (G.U t x)) = ∫ t in (0 : ℝ)..a, G.U (s + t) x := by
    congr 1
    funext t
    rw [G.apply_apply]
  have h3 : (∫ t in (0 : ℝ)..a, G.U (s + t) x) = ∫ u in (s + 0)..(s + a), G.U u x :=
    intervalIntegral.integral_comp_add_left (f := fun u => G.U u x) (a := (0 : ℝ)) (b := a) s
  rw [h1, h2, h3, add_zero, bAvg, bAvg]
  exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 (s + a))
    (hc.intervalIntegrable 0 s)).symm

theorem bAvg_mem_genDomain (x : H) (a : ℝ) : G.bAvg x a ∈ G.genDomain := by
  have h : (fun s : ℝ => G.U s (G.bAvg x a))
      = fun s : ℝ => G.bAvg x (s + a) - G.bAvg x s := by
    funext s; exact G.apply_bAvg s a x
  rw [mem_genDomain_iff, h]
  have hfa : HasDerivAt (fun u : ℝ => G.bAvg x u) (G.U a x) (0 + a) := by
    simpa using G.hasDerivAt_bAvg x a
  have h1 : HasDerivAt (fun s : ℝ => G.bAvg x (s + a)) (G.U a x) 0 :=
    HasDerivAt.comp_add_const 0 a hfa
  have h2 : HasDerivAt (fun s : ℝ => G.bAvg x s) (G.U 0 x) 0 := G.hasDerivAt_bAvg x 0
  exact (h1.sub h2).differentiableAt



/-! ## Density of the domain -/

theorem norm_bAvg_sub_smul_le (x : H) (a C : ℝ)
    (hC : ∀ t ∈ Set.uIcc (0 : ℝ) a, ‖G.U t x - x‖ ≤ C) :
    ‖G.bAvg x a - (a : ℂ) • x‖ ≤ C * |a| := by
  have hc : Continuous fun t : ℝ => G.U t x := G.continuous_apply x
  have hconst : (∫ _t in (0 : ℝ)..a, x) = (a : ℂ) • x := by
    rw [intervalIntegral.integral_const]
    simp [Complex.coe_smul]
  have hsub : G.bAvg x a - (a : ℂ) • x = ∫ t in (0 : ℝ)..a, (G.U t x - x) := by
    rw [bAvg, ← hconst,
      intervalIntegral.integral_sub (hc.intervalIntegrable 0 a)
        (intervalIntegrable_const)]
  rw [hsub]
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := a) (C := C) (f := fun t => G.U t x - x)
    (fun t ht => hC t (by simpa [Set.uIoc, Set.uIcc] using Set.Ioc_subset_Icc_self ht))
  simpa using this

theorem denseDomain : Dense ((G.genDomain : Submodule ℂ H) : Set H) := by
  refine Metric.dense_iff.mpr ?_
  intro x r hr
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ ⦃t : ℝ⦄, dist t 0 < δ → dist (G.U t x) x < r / 2 := by
    have h := Metric.tendsto_nhds.mp (G.tendsto_apply_zero x) (r / 2) (by linarith)
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨δ, hδ, hb⟩ := h
    exact ⟨δ, hδ, fun t ht => hb ht⟩
  set a : ℝ := δ / 2 with ha
  have ha0 : 0 < a := by positivity
  have haδ : a < δ := by rw [ha]; linarith
  have hbound : ∀ t ∈ Set.uIcc (0 : ℝ) a, ‖G.U t x - x‖ ≤ r / 2 := by
    intro t ht
    rw [Set.uIcc_of_le ha0.le] at ht
    have hdt : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact lt_of_le_of_lt ht.2 haδ
    have := hball hdt
    rw [dist_eq_norm] at this
    exact this.le
  have hkey := G.norm_bAvg_sub_smul_le x a (r / 2) hbound
  have hne : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  refine ⟨((a : ℂ)⁻¹) • G.bAvg x a, ?_, Submodule.smul_mem _ _ (G.bAvg_mem_genDomain x a)⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have heq : ((a : ℂ)⁻¹) • G.bAvg x a - x = ((a : ℂ)⁻¹) • (G.bAvg x a - (a : ℂ) • x) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [heq, norm_smul]
  have hn : ‖((a : ℂ)⁻¹)‖ = a⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
  rw [hn]
  calc a⁻¹ * ‖G.bAvg x a - (a : ℂ) • x‖ ≤ a⁻¹ * (r / 2 * a) := by
        have h := mul_le_mul_of_nonneg_left hkey (le_of_lt (inv_pos.mpr ha0))
        rwa [abs_of_pos ha0] at h
    _ = r / 2 := by field_simp
    _ < r := by linarith

/-! ## Symmetry -/

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem symmetric : BookProof.ChapterUnitaryTransport.IsSymmetricOn G.genDomain G.genOp := by
  intro psi phi
  have hx := G.hasDerivAt_orbit_zero psi
  have hy := G.hasDerivAt_orbit_zero phi
  have hf : HasDerivAt (fun t : ℝ => ⟪(phi : H), G.U t (psi : H)⟫_ℂ)
      (⟪(phi : H), (-Complex.I) • G.genOp psi⟫_ℂ) 0 :=
    hasDerivAt_inner_right (phi : H) hx
  have hyneg : HasDerivAt (fun t : ℝ => G.U (-t) (phi : H))
      ((-1 : ℝ) • ((-Complex.I) • G.genOp phi)) 0 := by
    have h := HasDerivAt.scomp (0 : ℝ) (by simpa using hy) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using h
  have hg : HasDerivAt (fun t : ℝ => ⟪(psi : H), G.U (-t) (phi : H)⟫_ℂ)
      (⟪(psi : H), (-1 : ℝ) • ((-Complex.I) • G.genOp phi)⟫_ℂ) 0 :=
    hasDerivAt_inner_right (psi : H) hyneg
  have hEq : (fun t : ℝ => (starRingEnd ℂ) ⟪(psi : H), G.U (-t) (phi : H)⟫_ℂ)
      = fun t : ℝ => ⟪(phi : H), G.U t (psi : H)⟫_ℂ := by
    funext t
    rw [inner_conj_symm]
    exact (G.inner_adjoint t (phi : H) (psi : H)).symm
  have hfg : HasDerivAt (fun t : ℝ => ⟪(phi : H), G.U t (psi : H)⟫_ℂ)
      ((starRingEnd ℂ) ⟪(psi : H), (-1 : ℝ) • ((-Complex.I) • G.genOp phi)⟫_ℂ) 0 :=
    hEq ▸ hasDerivAt_conj hg
  have hsm : ((-1 : ℝ) • ((-Complex.I) • G.genOp phi)) = Complex.I • G.genOp phi := by
    rw [← Complex.coe_smul, smul_smul]
    norm_num
  have h := hf.unique hfg
  rw [hsm, inner_smul_right, inner_smul_right, map_mul] at h
  have hIne : (-Complex.I) ≠ 0 := by simp
  have hconjI : (starRingEnd ℂ) Complex.I = -Complex.I := by simp
  rw [hconjI] at h
  have key : ⟪(phi : H), G.genOp psi⟫_ℂ
      = (starRingEnd ℂ) ⟪(psi : H), G.genOp phi⟫_ℂ := mul_left_cancel₀ hIne h
  rw [inner_conj_symm] at key
  rw [← inner_conj_symm (G.genOp psi) (phi : H), ← inner_conj_symm (psi : H) (G.genOp phi), key]

/-! ## Self-adjointness -/

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- Weak convergence together with the bound `‖v i‖ ≤ ‖w‖` forces strong convergence. -/
theorem tendsto_of_weak_of_norm_le {ι : Type*} {l : Filter ι} {v : ι → H} {w : H}
    {D : Set H} (hD : Dense D) (hbd : ∀ᶠ i in l, ‖v i‖ ≤ ‖w‖)
    (hweak : ∀ x ∈ D, Tendsto (fun i => ⟪x, v i⟫_ℂ) l (𝓝 (⟪x, w⟫_ℂ))) :
    Tendsto v l (𝓝 w) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / 3 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨x, hxD, hxw⟩ : ∃ x ∈ D, dist w x < δ :=
    Metric.mem_closure_iff.mp (hD w) δ hδ
  have hre : Tendsto (fun i => (⟪x, v i⟫_ℂ).re) l (𝓝 ((⟪x, w⟫_ℂ).re)) :=
    (Complex.continuous_re.tendsto _).comp (hweak x hxD)
  have hev : ∀ᶠ i in l, (⟪x, w⟫_ℂ).re - δ ^ 2 / 2 < (⟪x, v i⟫_ℂ).re :=
    hre.eventually (eventually_gt_nhds (by nlinarith))
  filter_upwards [hbd, hev] with i hbi hei
  have hsq : ‖v i - x‖ ^ 2 = ‖v i‖ ^ 2 - 2 * (⟪v i, x⟫_ℂ).re + ‖x‖ ^ 2 := by
    simpa using norm_sub_sq (𝕜 := ℂ) (v i) x
  have hwsq : ‖w - x‖ ^ 2 = ‖w‖ ^ 2 - 2 * (⟪w, x⟫_ℂ).re + ‖x‖ ^ 2 := by
    simpa using norm_sub_sq (𝕜 := ℂ) w x
  have hswap1 : (⟪v i, x⟫_ℂ).re = (⟪x, v i⟫_ℂ).re := by
    rw [← inner_conj_symm (v i) x, Complex.conj_re]
  have hswap2 : (⟪w, x⟫_ℂ).re = (⟪x, w⟫_ℂ).re := by
    rw [← inner_conj_symm w x, Complex.conj_re]
  have hwx : ‖w - x‖ < δ := by rwa [← dist_eq_norm]
  have hwx2 : ‖w‖ ^ 2 - 2 * (⟪x, w⟫_ℂ).re + ‖x‖ ^ 2 < δ ^ 2 := by
    rw [← hswap2, ← hwsq]
    nlinarith [norm_nonneg (w - x)]
  have hlt : ‖v i - x‖ ^ 2 < (2 * δ) ^ 2 := by
    rw [hsq, hswap1]
    nlinarith [norm_nonneg (v i), norm_nonneg w]
  have hvx : ‖v i - x‖ < 2 * δ := by
    have h1 : (0 : ℝ) ≤ ‖v i - x‖ := norm_nonneg _
    nlinarith
  calc dist (v i) w ≤ ‖v i - x‖ + ‖x - w‖ := by
        rw [dist_eq_norm]
        simpa using norm_sub_le_norm_sub_add_norm_sub (v i) x w
    _ < 2 * δ + δ := by
        have : ‖x - w‖ < δ := by rw [norm_sub_rev, ← dist_eq_norm]; exact hxw
        linarith
    _ = ε := by rw [hδdef]; ring

/-! ## Self-adjointness -/

theorem selfAdjoint : BookProof.ChapterUnitaryTransport.IsSelfAdjointOn G.genDomain G.genOp := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro phi ⟨eta, heta⟩
    -- the matrix coefficient `K u = ⟪φ, U u x⟫` and its derivative
    have hK : ∀ x : G.genDomain, ∀ s : ℝ,
        HasDerivAt (fun u : ℝ => ⟪phi, G.U u (x : H)⟫_ℂ)
          ((-Complex.I) * ⟪eta, G.U s (x : H)⟫_ℂ) s := by
      intro x s
      have h1 := hasDerivAt_inner_right phi (G.hasDerivAt_orbit x s)
      have h2 : ⟪phi, (-Complex.I) • G.U s (G.genOp x)⟫_ℂ
          = (-Complex.I) * ⟪eta, G.U s (x : H)⟫_ℂ := by
        rw [inner_smul_right]
        congr 1
        have hcomm := G.genOp_apply_comm s x
        have hz := heta ⟨G.U s (x : H), G.apply_mem_genDomain s x⟩
        rw [hcomm] at hz
        conv_lhs => rw [← inner_conj_symm]
        rw [hz, inner_conj_symm]
      rw [← h2]
      exact h1
    have hKbd : ∀ x : G.genDomain, ∀ s : ℝ,
        ‖(-Complex.I) * ⟪eta, G.U s (x : H)⟫_ℂ‖ ≤ ‖eta‖ * ‖(x : H)‖ := by
      intro x s
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      calc ‖⟪eta, G.U s (x : H)⟫_ℂ‖ ≤ ‖eta‖ * ‖G.U s (x : H)‖ := norm_inner_le_norm _ _
        _ = ‖eta‖ * ‖(x : H)‖ := by rw [G.norm_map]
    have hMVT : ∀ (x : G.genDomain) (t : ℝ),
        ‖⟪phi, G.U t (x : H)⟫_ℂ - ⟪phi, (x : H)⟫_ℂ‖ ≤ (‖eta‖ * ‖(x : H)‖) * |t| := by
      intro x t
      have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun u : ℝ => ⟪phi, G.U u (x : H)⟫_ℂ)
        (f' := fun s : ℝ => (-Complex.I) * ⟪eta, G.U s (x : H)⟫_ℂ)
        (C := ‖eta‖ * ‖(x : H)‖)
        (fun s _ => (hK x s).hasDerivWithinAt) (fun s _ => hKbd x s)
        (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
      simpa using h
    -- the weak Lipschitz bound, first on the domain then everywhere
    have hconj : ∀ (t : ℝ) (x : H), ⟪x, G.U t phi - phi⟫_ℂ
        = (starRingEnd ℂ) (⟪phi, G.U (-t) x⟫_ℂ - ⟪phi, x⟫_ℂ) := by
      intro t x
      rw [map_sub, inner_conj_symm, inner_conj_symm, inner_sub_right]
      congr 1
      exact G.inner_adjoint t x phi
    have hb2 : ∀ (t : ℝ) (x : G.genDomain),
        ‖⟪(x : H), G.U t phi - phi⟫_ℂ‖ ≤ (|t| * ‖eta‖) * ‖(x : H)‖ := by
      intro t x
      rw [hconj t (x : H), RCLike.norm_conj]
      have := hMVT x (-t)
      rw [abs_neg] at this
      calc ‖⟪phi, G.U (-t) (x : H)⟫_ℂ - ⟪phi, (x : H)⟫_ℂ‖ ≤ (‖eta‖ * ‖(x : H)‖) * |t| := this
        _ = (|t| * ‖eta‖) * ‖(x : H)‖ := by ring
    have hb3 : ∀ (t : ℝ) (x : H),
        ‖⟪x, G.U t phi - phi⟫_ℂ‖ ≤ (|t| * ‖eta‖) * ‖x‖ := by
      intro t
      have hclosed : IsClosed
          {x : H | ‖⟪x, G.U t phi - phi⟫_ℂ‖ ≤ (|t| * ‖eta‖) * ‖x‖} :=
        isClosed_le ((continuous_id.inner continuous_const).norm)
          (continuous_const.mul continuous_norm)
      have hsub : ((G.genDomain : Submodule ℂ H) : Set H)
          ⊆ {x : H | ‖⟪x, G.U t phi - phi⟫_ℂ‖ ≤ (|t| * ‖eta‖) * ‖x‖} :=
        fun x hx => hb2 t ⟨x, hx⟩
      intro x
      have hall := hclosed.closure_subset_iff.mpr hsub
      rw [G.denseDomain.closure_eq] at hall
      exact hall (Set.mem_univ x)
    have hLip : ∀ t : ℝ, ‖G.U t phi - phi‖ ≤ |t| * ‖eta‖ := by
      intro t
      exact norm_le_of_inner_self_bound (by positivity) (hb3 t _)
    -- weak convergence of the difference quotients
    set w : H := (-Complex.I) • eta with hw
    have hweak : ∀ x ∈ ((G.genDomain : Submodule ℂ H) : Set H),
        Tendsto (fun t : ℝ => ⟪x, t⁻¹ • (G.U t phi - phi)⟫_ℂ) (𝓝[≠] (0 : ℝ))
          (𝓝 (⟪x, w⟫_ℂ)) := by
      intro x hx
      have hMd : HasDerivAt (fun u : ℝ => ⟪phi, G.U (-u) x⟫_ℂ)
          (Complex.I * ⟪eta, x⟫_ℂ) 0 := by
        have h0 := hK ⟨x, hx⟩ 0
        rw [G.apply_zero] at h0
        have h := HasDerivAt.scomp (0 : ℝ) (by simpa using h0) (hasDerivAt_neg (0 : ℝ))
        simp only [Function.comp_def] at h
        convert h using 1
        · rfl
        · norm_num
      have hslope := hasDerivAt_iff_tendsto_slope.mp hMd
      have hcj : Tendsto
          (fun t : ℝ => (starRingEnd ℂ) (slope (fun u : ℝ => ⟪phi, G.U (-u) x⟫_ℂ) 0 t))
          (𝓝[≠] (0 : ℝ)) (𝓝 ((starRingEnd ℂ) (Complex.I * ⟪eta, x⟫_ℂ))) :=
        (Complex.continuous_conj.tendsto _).comp hslope
      have hfun : ∀ t : ℝ, ⟪x, t⁻¹ • (G.U t phi - phi)⟫_ℂ
          = (starRingEnd ℂ) (slope (fun u : ℝ => ⟪phi, G.U (-u) x⟫_ℂ) 0 t) := by
        intro t
        simp only [slope, vsub_eq_sub, sub_zero, neg_zero, G.apply_zero]
        rw [← Complex.coe_smul, inner_smul_right, hconj t x, ← Complex.coe_smul,
          smul_eq_mul, map_mul, Complex.conj_ofReal]
      have hlim : (starRingEnd ℂ) (Complex.I * ⟪eta, x⟫_ℂ) = ⟪x, w⟫_ℂ := by
        rw [hw, inner_smul_right, map_mul, inner_conj_symm]
        simp
      rw [← hlim]
      exact hcj.congr (fun t => (hfun t).symm)
    have hbdd : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), ‖t⁻¹ • (G.U t phi - phi)‖ ≤ ‖w‖ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := ht
      have hwn : ‖w‖ = ‖eta‖ := by
        rw [hw, norm_smul, norm_neg, Complex.norm_I, one_mul]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, hwn]
      have habs : (0 : ℝ) < |t| := abs_pos.mpr ht0
      calc |t|⁻¹ * ‖G.U t phi - phi‖ ≤ |t|⁻¹ * (|t| * ‖eta‖) :=
            mul_le_mul_of_nonneg_left (hLip t) (by positivity)
        _ = ‖eta‖ := by field_simp
    have hstrong := tendsto_of_weak_of_norm_le G.denseDomain hbdd hweak
    have hderiv : HasDerivAt (fun t : ℝ => G.U t phi) w 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      exact hstrong.congr (fun t => by simp [slope, G.apply_zero])
    exact hderiv.differentiableAt
  · intro phi hphi
    exact ⟨G.genOp ⟨phi, hphi⟩, fun psi => G.symmetric psi ⟨phi, hphi⟩⟩


/-- The self-adjoint generator of a weakly measurable unitary group on a separable
Hilbert space. -/
noncomputable def gen : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H where
  domain := G.genDomain
  op := G.genOp
  denseDomain := G.denseDomain
  symmetric := G.symmetric
  selfAdjoint := G.selfAdjoint


/-! ## Uniqueness: the group is the Stone group of its generator -/









end WeakMeasurableUnitaryGroup

end BookProof.ChapterStoneMeasurable


