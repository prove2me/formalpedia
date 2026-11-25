-- Prove2me | solution 1 for Arxiv1003_4724.true_dielectric_dipole_limit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T16:00:59.458456+00:00
-- url     : https://prove2.me/submissions/78e0a9b0-2d04-450e-aab0-e485f22f93a3

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology
namespace Arxiv1003_4724

theorem static_conductivity_dipole_correlation {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A]
    (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A)
    (hM : IsLongWaveModel ω τ Dip Cur) (hbar V : ℝ) (hhbar : 0 < hbar) (hV : 0 < V)
    (sigmaSt : ℝ) (hsig : 0 ≤ sigmaSt)
    (hint : IntegrableOn (sigmaCorr ω τ hbar V Dip Cur) (Set.Ioi 0))
    (h14 : Tendsto (sigma0 ω τ hbar V Dip Cur) (𝓝[≠] (0 : ℝ)) (𝓝 (sigmaSt : ℂ))) :
    Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, sigmaCorr ω τ hbar V Dip Cur s) atTop
        (𝓝 (sigmaSt : ℂ)) ∧
      Tendsto (dipoleCorr ω τ hbar V Dip) atTop (𝓝 (sigmaSt : ℂ))  := by
  obtain ⟨hst, hdyn, -, hsa, hder, hcc⟩ := hM
  have hmem1 : ∀ β : Fin 3, Cur β ∈ ({Dip β, Cur β} : Set A) := fun β => by simp
  have hmem2 : ∀ β : Fin 3, Dip β ∈ ({Dip β, Cur β} : Set A) := fun β => by simp
  have hcont : Continuous (sigmaCorr ω τ hbar V Dip Cur) := by
    unfold sigmaCorr
    exact continuous_const.mul (continuous_finset_sum _ fun β _ =>
      (hcc β (Cur β) (hmem1 β) (Dip β) (hmem2 β)).1)
  -- step 1: the integral over (0,∞) equals sigmaSt
  have hlim0 : Tendsto (sigma0 ω τ hbar V Dip Cur) (𝓝 0)
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), sigmaCorr ω τ hbar V Dip Cur t)) := by
    unfold sigma0
    have := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Set.Ioi (0:ℝ))) (l := 𝓝 (0:ℝ))
      (F := fun x t => Complex.exp (Complex.I * x * t) * sigmaCorr ω τ hbar V Dip Cur t)
      (f := sigmaCorr ω τ hbar V Dip Cur)
      (fun t => ‖sigmaCorr ω τ hbar V Dip Cur t‖)
      (Eventually.of_forall fun x => (Continuous.aestronglyMeasurable (by fun_prop)))
      (Eventually.of_forall fun x => Eventually.of_forall fun t => by
        rw [norm_mul, Complex.norm_exp]
        simp)
      hint.norm
      (Eventually.of_forall fun t => by
        have : Tendsto (fun x : ℝ => Complex.exp (Complex.I * x * t)) (𝓝 0)
            (𝓝 (Complex.exp (Complex.I * ((0:ℝ):ℂ) * t))) :=
          ((by fun_prop : Continuous fun x : ℝ => Complex.exp (Complex.I * x * t)).tendsto 0)
        simpa using this.mul_const (sigmaCorr ω τ hbar V Dip Cur t))
    exact this
  have hval : (∫ t in Set.Ioi (0 : ℝ), sigmaCorr ω τ hbar V Dip Cur t) = (sigmaSt : ℂ) :=
    tendsto_nhds_unique (hlim0.mono_left nhdsWithin_le_nhds) h14
  have h1 : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, sigmaCorr ω τ hbar V Dip Cur s) atTop
      (𝓝 (sigmaSt : ℂ)) := by
    rw [← hval]
    exact intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  refine ⟨h1, ?_⟩
  -- step 2: dipoleCorr' = sigmaCorr and dipoleCorr 0 = 0
  have hcd : ∀ β : Fin 3, ∀ t, HasDerivAt (commCorr ω τ (Dip β) (Dip β))
      (commCorr ω τ (Cur β) (Dip β) t) t := by
    intro β t
    have h := ((hder β (Dip β) t).1).sub ((hder β (Dip β) t).2)
    have e : commCorr ω τ (Dip β) (Dip β) = fun s => ω (τ s (Dip β) * Dip β) - ω (Dip β * τ s (Dip β)) := by
      funext s; simp [commCorr, Ring.lie_def]
    rw [e]
    exact h.congr_deriv (by simp [commCorr, Ring.lie_def])
  have hdd : ∀ t, HasDerivAt (dipoleCorr ω τ hbar V Dip) (sigmaCorr ω τ hbar V Dip Cur t) t := by
    intro t
    have := (HasDerivAt.sum (u := Finset.univ) fun β _ => hcd β t).const_mul
      (Complex.I / (3 * hbar * V))
    unfold dipoleCorr sigmaCorr
    exact this
  have hd0 : dipoleCorr ω τ hbar V Dip 0 = 0 := by
    unfold dipoleCorr commCorr
    simp only [hdyn.1, Ring.lie_def, sub_self, map_zero, Finset.sum_const_zero, mul_zero]
  refine h1.congr fun t => ?_
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hdd s) (hcont.intervalIntegrable _ _),
    hd0, sub_zero]

theorem true_dielectric_dipole_limit {A ι Par : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι] (F : Filter Par) [F.NeBot]
    (ω : Par → A →ₗ[ℂ] ℂ) (τ : Par → ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Par → Fin 3 → A)
    (hM : ∀ l, IsLongWaveModel (ω l) (τ l) (Dip l) (Cur l))
    (N : Par → ι → A) (hN : ∀ l a, IsSelfAdjoint (N l a)) (z : ι → ℝ) (e hbar : ℝ)
    (he : 0 < e) (hhbar : 0 < hbar) (T V : Par → ℝ) (hT : ∀ l, 0 < T l) (hV : ∀ l, 0 < V l)
    (sigmaSt : Par → ℝ) (hsig : ∀ l, 0 ≤ sigmaSt l)
    (hint : ∀ l, IntegrableOn (sigmaCorr (ω l) (τ l) hbar (V l) (Dip l) (Cur l)) (Set.Ioi 0))
    (h14 : ∀ l, Tendsto (sigma0 (ω l) (τ l) hbar (V l) (Dip l) (Cur l)) (𝓝[≠] (0 : ℝ))
      (𝓝 (sigmaSt l : ℂ)))
    (h37 : Tendsto (fun l => kappaSq (ω l) (N l) z e (T l) (V l)) F (𝓝 0))
    (h36 : Tendsto sigmaSt F (𝓝 0)) :
    ∃ D : Par → ℂ, (∀ l, Tendsto (dipoleCorr (ω l) (τ l) hbar (V l) (Dip l)) atTop (𝓝 (D l))) ∧
      Tendsto D F (𝓝 0)  := by
  refine ⟨fun l => (sigmaSt l : ℂ), fun l => ?_, ?_⟩
  · exact (static_conductivity_dipole_correlation (ω l) (τ l) (Dip l) (Cur l) (hM l) hbar (V l)
      hhbar (hV l) (sigmaSt l) (hsig l) (hint l) (h14 l)).2
  · have h := (Complex.continuous_ofReal.tendsto 0).comp h36
    rw [Complex.ofReal_zero] at h
    exact h

end Arxiv1003_4724
open Arxiv1003_4724 in
theorem solution {A ι Par : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι] (F : Filter Par) [F.NeBot]
    (ω : Par → A →ₗ[ℂ] ℂ) (τ : Par → ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Par → Fin 3 → A)
    (hM : ∀ l, IsLongWaveModel (ω l) (τ l) (Dip l) (Cur l))
    (N : Par → ι → A) (hN : ∀ l a, IsSelfAdjoint (N l a)) (z : ι → ℝ) (e hbar : ℝ)
    (he : 0 < e) (hhbar : 0 < hbar) (T V : Par → ℝ) (hT : ∀ l, 0 < T l) (hV : ∀ l, 0 < V l)
    (sigmaSt : Par → ℝ) (hsig : ∀ l, 0 ≤ sigmaSt l)
    (hint : ∀ l, IntegrableOn (sigmaCorr (ω l) (τ l) hbar (V l) (Dip l) (Cur l)) (Set.Ioi 0))
    (h14 : ∀ l, Tendsto (sigma0 (ω l) (τ l) hbar (V l) (Dip l) (Cur l)) (𝓝[≠] (0 : ℝ))
      (𝓝 (sigmaSt l : ℂ)))
    (h37 : Tendsto (fun l => kappaSq (ω l) (N l) z e (T l) (V l)) F (𝓝 0))
    (h36 : Tendsto sigmaSt F (𝓝 0)) :
    ∃ D : Par → ℂ, (∀ l, Tendsto (dipoleCorr (ω l) (τ l) hbar (V l) (Dip l)) atTop (𝓝 (D l))) ∧
      Tendsto D F (𝓝 0) :=
  true_dielectric_dipole_limit F ω τ Dip Cur hM N hN z e hbar he hhbar T V hT hV sigmaSt hsig hint h14 h37 h36
