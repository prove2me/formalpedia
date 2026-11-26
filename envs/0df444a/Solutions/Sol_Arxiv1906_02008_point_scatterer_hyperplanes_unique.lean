-- Prove2me | solution 1 for Arxiv1906_02008.point_scatterer_hyperplanes_unique
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T09:40:01.011832+00:00
-- url     : https://prove2.me/submissions/eb6b89f6-dc45-4fe4-8c2d-17aa7037c7c0

import Mathlib
import Definitions.Def_Arxiv1906_02008_Basic

open MeasureTheory Set
open scoped RealInnerProductSpace Topology

noncomputable section
namespace PS
open Arxiv1906_02008

def χ (a : ℝ) : Multiplicative ℝ →* ℂ where
  toFun x := Complex.exp (Complex.I * (x.toAdd : ℂ) * a)
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Complex.ofReal_add]; rw [← Complex.exp_add]; ring_nf

lemma χ_inj : Function.Injective χ := by
  intro a b h
  have hf : (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ) * a)) = (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ) * b)) := by
    funext t; exact DFunLike.congr_fun h (Multiplicative.ofAdd t)
  have hd : ∀ c : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ) * c)) (Complex.I * c) 0 := by
    intro c
    have := (((Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).const_mul Complex.I).mul_const (c : ℂ)).cexp
    simpa using this
  have h1 := hd a
  rw [hf] at h1
  have := h1.unique (hd b)
  have : (a : ℂ) = b := mul_left_cancel₀ Complex.I_ne_zero this
  exact_mod_cast this

lemma sums_eq {M M' : ℕ} (c : Fin M → ℝ) (τ : Fin M → ℂ) (c' : Fin M' → ℝ) (τ' : Fin M' → ℂ)
    (km kp : ℝ) (hk : km < kp)
    (h : ∀ k ∈ Ioo km kp, ∑ m, τ m * Complex.exp (Complex.I * (k : ℂ) * c m) =
      ∑ m, τ' m * Complex.exp (Complex.I * (k : ℂ) * c' m)) :
    ∀ t : ℝ, ∑ m, τ m * Complex.exp (Complex.I * (t : ℂ) * c m) =
      ∑ m, τ' m * Complex.exp (Complex.I * (t : ℂ) * c' m) := by
  set g : ℂ → ℂ := fun w => ∑ m, τ m * Complex.exp (Complex.I * w * c m) -
    ∑ m, τ' m * Complex.exp (Complex.I * w * c' m)
  have hg : AnalyticOnNhd ℂ g univ := by
    have : Differentiable ℂ g := by simp only [g]; fun_prop
    exact this.differentiableOn.analyticOnNhd isOpen_univ
  set x0 := (km + kp) / 2
  have hev : ∀ᶠ x in 𝓝[≠] x0, x ∈ Ioo km kp :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by simp only [x0]; linarith) (by simp only [x0]; linarith))
  have htend : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x0) (𝓝[≠] (x0 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by
        simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢; exact_mod_cast hx)
  have hfr : ∃ᶠ w in 𝓝[≠] (x0 : ℂ), g w = 0 :=
    htend.frequently (hev.frequently.mono fun x hx => by simp only [g]; rw [h x hx, sub_self])
  have := hg.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ _) hfr
  intro t
  have := this (mem_univ (t : ℂ))
  simp only [g, Pi.zero_apply] at this
  exact sub_eq_zero.mp this

end PS

open Arxiv1906_02008 PS in
theorem solution {n : ℕ} (hn : n = 2 ∨ n = 3)
    (km kp : ℝ) (hkm : 0 < km) (hk : km < kp)
    (xh θ : Rn n) (hxh : ‖xh‖ = 1) (hθ : ‖θ‖ = 1) (hne : xh ≠ θ)
    (M M' : ℕ) (z : Fin M → Rn n) (τ : Fin M → ℂ) (z' : Fin M' → Rn n) (τ' : Fin M' → ℂ)
    (hτ : ∀ m, (∑ m' ∈ Finset.univ.filter (fun m' => ⟪z m', θ - xh⟫ = ⟪z m, θ - xh⟫), τ m') ≠ 0)
    (hτ' : ∀ m, (∑ m' ∈ Finset.univ.filter (fun m' => ⟪z' m', θ - xh⟫ = ⟪z' m, θ - xh⟫), τ' m') ≠ 0)
    (hdata : ∀ k ∈ Ioo km kp, pointFarField z τ xh θ k = pointFarField z' τ' xh θ k) :
    Set.range (fun m => hyperplane xh θ (-⟪z m, θ - xh⟫)) =
      Set.range (fun m => hyperplane xh θ (-⟪z' m, θ - xh⟫)) := by
  classical
  set a : Fin M → ℝ := fun m => ⟪z m, θ - xh⟫ with ha
  set a' : Fin M' → ℝ := fun m => ⟪z' m, θ - xh⟫ with ha'
  have hall := sums_eq a τ a' τ' km kp hk (fun k hk' => hdata k hk')
  set C : ℝ → ℂ := fun c => ∑ m ∈ Finset.univ.filter (fun m => a m = c), τ m with hC
  set C' : ℝ → ℂ := fun c => ∑ m ∈ Finset.univ.filter (fun m => a' m = c), τ' m with hC'
  set A : Finset ℝ := Finset.univ.image a ∪ Finset.univ.image a'
  have LI : LinearIndependent ℂ (fun c : ℝ => ((χ c : Multiplicative ℝ →* ℂ) : Multiplicative ℝ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp χ χ_inj
  have hzero : ∑ c ∈ A, (C c - C' c) • ((χ c : Multiplicative ℝ →* ℂ) : Multiplicative ℝ → ℂ) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e1 : ∑ c ∈ A, C c * χ c x = ∑ m, τ m * χ (a m) x := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := A) (g := a)
        (fun m _ => Finset.mem_union_left _ (Finset.mem_image_of_mem a (Finset.mem_univ m)))]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [(Finset.mem_filter.mp hm).2]
    have e2 : ∑ c ∈ A, C' c * χ c x = ∑ m, τ' m * χ (a' m) x := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := A) (g := a')
        (fun m _ => Finset.mem_union_right _ (Finset.mem_image_of_mem a' (Finset.mem_univ m)))]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [(Finset.mem_filter.mp hm).2]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e1, e2, sub_eq_zero]
    exact hall x.toAdd
  have hCC : ∀ c ∈ A, C c = C' c := fun c hc =>
    sub_eq_zero.mp (linearIndependent_iff'.mp LI A (fun c => C c - C' c) hzero c hc)
  ext H
  constructor
  · rintro ⟨m, rfl⟩
    have h1 : C (a m) ≠ 0 := hτ m
    rw [hCC _ (Finset.mem_union_left _ (Finset.mem_image_of_mem a (Finset.mem_univ m)))] at h1
    obtain ⟨m', hm', -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    refine ⟨m', ?_⟩
    have : a' m' = a m := (Finset.mem_filter.mp hm').2
    simp only [ha, ha'] at this
    simp only [this]
  · rintro ⟨m, rfl⟩
    have h1 : C' (a' m) ≠ 0 := hτ' m
    rw [← hCC _ (Finset.mem_union_right _ (Finset.mem_image_of_mem a' (Finset.mem_univ m)))] at h1
    obtain ⟨m', hm', -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    refine ⟨m', ?_⟩
    have : a m' = a' m := (Finset.mem_filter.mp hm').2
    simp only [ha, ha'] at this
    simp only [this]
