-- Prove2me | solution 1 for Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c413e28a-0367-5df6-83c0-c8c5d955f6f5

import Mathlib
import Theorems.Thm_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential
import Theorems.Thm_Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr
import Theorems.Thm_Complex_exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential

set_option autoImplicit false

open Topology
open Polynomial
open scoped Polynomial.Bivariate

theorem A0Aux.contDiff_evalEval (q : ℂ[X][Y]) : ContDiff ℂ ⊤ (fun p : ℂ × ℂ => q.evalEval p.1 p.2) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    have : (fun v : ℂ × ℂ => (p + q).evalEval v.1 v.2) =
        (fun v : ℂ × ℂ => p.evalEval v.1 v.2) + fun v : ℂ × ℂ => q.evalEval v.1 v.2 := by
      funext v; simp [evalEval_add]
    rw [this]; exact hp.add hq
  | monomial n a =>
    have : (fun v : ℂ × ℂ => (monomial n a).evalEval v.1 v.2) = fun v : ℂ × ℂ => aeval v.1 a * v.2 ^ n := by
      funext v
      rw [← C_mul_X_pow_eq_monomial, evalEval_mul, evalEval_pow, evalEval_C, evalEval_X, coe_aeval_eq_eval]
    rw [this]
    exact ((contDiff_aeval a ⊤).comp contDiff_fst).mul (contDiff_snd.pow n)

theorem A0Aux.differentiableOn_evalEval_comp (q : ℂ[X][Y]) {φ : ℂ → ℂ} {U : Set ℂ} (hφ : DifferentiableOn ℂ φ U) :
    DifferentiableOn ℂ (fun z => q.evalEval z (φ z)) U := by
  have h1 : Differentiable ℂ (fun p : ℂ × ℂ => q.evalEval p.1 p.2) := (A0Aux.contDiff_evalEval q).differentiable (by simp)
  exact h1.comp_differentiableOn (differentiableOn_id.prodMk hφ)

theorem solution
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    (hrank : Module.rank S (KaehlerDifferential ℂ S) = 1)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : S)
    (hdt : KaehlerDifferential.D ℂ S t ∉ (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S))) :
    ∃ (r : ℝ) (𝒰 : Set (S →ₐ[ℂ] ℂ)), 0 < r ∧ σ₀ ∈ 𝒰 ∧
      Set.BijOn (fun σ : S →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r) ∧
      (∀ s : S, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t)) ∧

      (∀ σ ∈ 𝒰, ∃ (fs : Finset S) (ε : ℝ), 0 < ε ∧
        ∀ σ' : S →ₐ[ℂ] ℂ, (∀ s ∈ fs, ‖σ' s - σ s‖ < ε) → σ' ∈ 𝒰) := by
  classical

  obtain ⟨g, hg, hSE⟩ := Algebra.exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential
    S hsm hrank σ₀ t hdt
  letI instA : Algebra (Polynomial ℂ) (Localization.Away g) :=
    ((algebraMap S (Localization.Away g)).comp (Polynomial.aeval t).toRingHom).toAlgebra
  haveI : Algebra.IsStandardEtale (Polynomial ℂ) (Localization.Away g) := hSE
  haveI : IsScalarTower ℂ (Polynomial ℂ) (Localization.Away g) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    show algebraMap ℂ (Localization.Away g) c = (algebraMap S (Localization.Away g)) ((Polynomial.aeval t) (algebraMap ℂ (Polynomial ℂ) c))
    rw [Polynomial.algebraMap_eq, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply]

  obtain ⟨x, F, G, hpt, hinjc, hsurjc, hrepr⟩ :=
    Algebra.IsStandardEtale.exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr ℂ (Localization.Away g)
  have hXt : algebraMap (Polynomial ℂ) (Localization.Away g) Polynomial.X = algebraMap S (Localization.Away g) t := by
    show (algebraMap S (Localization.Away g)) (Polynomial.aeval t Polynomial.X) = _
    rw [Polynomial.aeval_X]
  simp only [hXt] at hpt hinjc hsurjc hrepr

  let ι : S →ₐ[ℂ] (Localization.Away g) := IsScalarTower.toAlgHom ℂ S (Localization.Away g)
  have hι : ∀ s : S, ι s = algebraMap S (Localization.Away g) s := fun s => rfl
  have hunit : ∀ (σ : S →ₐ[ℂ] ℂ), σ g ≠ 0 → ∀ y : Submonoid.powers g, IsUnit (σ y) := by
    rintro σ hσ ⟨y, n, rfl⟩
    rw [map_pow]; exact (isUnit_iff_ne_zero.2 hσ).pow n
  let L : ∀ (σ : S →ₐ[ℂ] ℂ), σ g ≠ 0 → ((Localization.Away g) →ₐ[ℂ] ℂ) := fun σ hσ =>
    IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := σ) (hunit σ hσ)
  have hL : ∀ (σ : S →ₐ[ℂ] ℂ) (hσ : σ g ≠ 0) (s : S), L σ hσ (algebraMap S (Localization.Away g) s) = σ s := fun σ hσ s => by
    show IsLocalization.liftAlgHom _ _ = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]; rfl
  have hLcomp : ∀ (σ : S →ₐ[ℂ] ℂ) (hσ : σ g ≠ 0), (L σ hσ).comp ι = σ := fun σ hσ =>
    AlgHom.ext fun s => hL σ hσ s
  have hτg : ∀ τ : (Localization.Away g) →ₐ[ℂ] ℂ, (τ.comp ι) g ≠ 0 := by
    intro τ
    show τ (algebraMap S (Localization.Away g) g) ≠ 0
    exact ((IsLocalization.Away.algebraMap_isUnit g).map τ).ne_zero
  have hcompL : ∀ τ : (Localization.Away g) →ₐ[ℂ] ℂ, L (τ.comp ι) (hτg τ) = τ := by
    intro τ
    apply AlgHom.coe_ringHom_injective
    refine IsLocalization.ringHom_ext (Submonoid.powers g) ?_
    ext s
    exact hL (τ.comp ι) (hτg τ) s

  obtain ⟨⟨a, ⟨gn, n, rfl⟩⟩, hax⟩ := IsLocalization.surj (Submonoid.powers g) x

  have hxval : ∀ τ : (Localization.Away g) →ₐ[ℂ] ℂ, τ x = (τ.comp ι) a / ((τ.comp ι) g) ^ n := by
    intro τ
    have h1 := congrArg τ hax
    rw [map_mul, map_pow (algebraMap S (Localization.Away g)), map_pow] at h1
    rw [eq_div_iff (pow_ne_zero _ (hτg τ))]
    exact h1

  let τ₀ : (Localization.Away g) →ₐ[ℂ] ℂ := L σ₀ hg
  have hτ₀ : ∀ s : S, τ₀ (algebraMap S (Localization.Away g) s) = σ₀ s := hL σ₀ hg
  obtain ⟨hF0, hG0, hD0⟩ := hpt τ₀
  rw [hτ₀] at hF0 hG0 hD0

  obtain ⟨r, ρ, φ, hr, hρ, hφ0, hφd, hφF, hφuniq⟩ :=
    Complex.exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero F (σ₀ t) (τ₀ x) hF0 hD0

  have hGcont : ContinuousAt (fun z => G.evalEval z (φ z)) (σ₀ t) := by
    have hφc : ContinuousAt φ (σ₀ t) := (hφd.differentiableAt (Metric.ball_mem_nhds _ hr)).continuousAt
    exact ((A0Aux.contDiff_evalEval G).continuous.continuousAt).comp (continuousAt_id.prodMk hφc)
  have hGnbhd : ∀ᶠ z in 𝓝 (σ₀ t), G.evalEval z (φ z) ≠ 0 := by
    refine hGcont.eventually_ne ?_
    rw [hφ0]; exact hG0
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhds_iff.1 hGnbhd
  set r' := min r r₁ with hr'
  have hr'pos : 0 < r' := lt_min hr hr₁
  have hb1 : ∀ z ∈ Metric.ball (σ₀ t) r', z ∈ Metric.ball (σ₀ t) r := fun z hz =>
    Metric.ball_subset_ball (min_le_left _ _) hz
  have hb2 : ∀ z ∈ Metric.ball (σ₀ t) r', G.evalEval z (φ z) ≠ 0 := fun z hz =>
    hr₁sub (Metric.ball_subset_ball (min_le_right _ _) hz)

  set 𝒱 : Set ((Localization.Away g) →ₐ[ℂ] ℂ) := {τ | τ (algebraMap S (Localization.Away g) t) ∈ Metric.ball (σ₀ t) r' ∧ τ x ∈ Metric.ball (τ₀ x) ρ} with h𝒱
  set 𝒰 : Set (S →ₐ[ℂ] ℂ) := (fun τ : (Localization.Away g) →ₐ[ℂ] ℂ => τ.comp ι) '' 𝒱 with h𝒰

  have hφτ : ∀ τ ∈ 𝒱, τ x = φ (τ (algebraMap S (Localization.Away g) t)) := by
    intro τ hτ
    exact hφuniq _ (hb1 _ hτ.1) _ hτ.2 (hpt τ).1
  refine ⟨r', 𝒰, hr'pos, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨τ₀, ⟨?_, ?_⟩, hLcomp σ₀ hg⟩
    · rw [hτ₀]; exact Metric.mem_ball_self hr'pos
    · exact Metric.mem_ball_self hρ
  ·
    refine ⟨?_, ?_, ?_⟩
    · rintro σ ⟨τ, hτ, rfl⟩
      show τ (ι t) ∈ _
      exact hτ.1
    · rintro σ ⟨τ, hτ, rfl⟩ σ' ⟨τ', hτ', rfl⟩ heq
      change τ (ι t) = τ' (ι t) at heq
      have hx' : τ x = τ' x := by
        rw [hφτ τ hτ, hφτ τ' hτ']
        exact congrArg φ heq
      rw [hinjc τ τ' heq hx']
    · intro z hz
      obtain ⟨hw, hFz⟩ := hφF z (hb1 z hz)
      obtain ⟨τ, hτt, hτx⟩ := hsurjc z (φ z) hFz (hb2 z hz)
      refine ⟨τ.comp ι, ⟨τ, ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · rw [hτt]; exact hz
      · rw [hτx]; exact hw
      · show τ (ι t) = z
        rw [hι, hτt]
  ·
    intro s
    obtain ⟨h, k, hk⟩ := hrepr (algebraMap S (Localization.Away g) s)
    refine ⟨fun z => h.evalEval z (φ z) / (G.evalEval z (φ z)) ^ k, ?_, ?_⟩
    · refine (A0Aux.differentiableOn_evalEval_comp h (hφd.mono fun z hz => hb1 z hz)).div
        ((A0Aux.differentiableOn_evalEval_comp G (hφd.mono fun z hz => hb1 z hz)).pow k) fun z hz => ?_
      exact pow_ne_zero _ (hb2 z hz)
    · rintro σ ⟨τ, hτ, rfl⟩
      show τ (algebraMap S (Localization.Away g) s) =
        h.evalEval (τ (algebraMap S (Localization.Away g) t)) (φ (τ (algebraMap S (Localization.Away g) t))) /
          (G.evalEval (τ (algebraMap S (Localization.Away g) t)) (φ (τ (algebraMap S (Localization.Away g) t)))) ^ k
      rw [← hφτ τ hτ, eq_div_iff (pow_ne_zero _ ?_)]
      · exact hk τ
      · rw [hφτ τ hτ]; exact hb2 _ hτ.1
  ·
    rintro σ ⟨τ, hτ, rfl⟩

    set V : Set (ℂ × ℂ × ℂ) := {p | p.1 ≠ 0 ∧ p.2.1 ∈ Metric.ball (σ₀ t) r' ∧ p.2.2 / p.1 ^ n ∈ Metric.ball (τ₀ x) ρ} with hV
    have hVopen : IsOpen V := by
      have h1 : IsOpen {p : ℂ × ℂ × ℂ | p.1 ≠ 0} := isOpen_ne_fun continuous_fst continuous_const
      have hc : ContinuousOn (fun p : ℂ × ℂ × ℂ => p.2.2 / p.1 ^ n) {p : ℂ × ℂ × ℂ | p.1 ≠ 0} :=
        (continuous_snd.comp continuous_snd).continuousOn.div ((continuous_fst.pow n).continuousOn)
          fun p hp => pow_ne_zero _ hp
      have h3 : IsOpen {p : ℂ × ℂ × ℂ | p.1 ≠ 0 ∧ p.2.2 / p.1 ^ n ∈ Metric.ball (τ₀ x) ρ} :=
        hc.isOpen_inter_preimage h1 Metric.isOpen_ball
      have h2 : IsOpen {p : ℂ × ℂ × ℂ | p.2.1 ∈ Metric.ball (σ₀ t) r'} :=
        Metric.isOpen_ball.preimage (continuous_fst.comp continuous_snd)
      have : V = {p : ℂ × ℂ × ℂ | p.1 ≠ 0 ∧ p.2.2 / p.1 ^ n ∈ Metric.ball (τ₀ x) ρ} ∩ {p | p.2.1 ∈ Metric.ball (σ₀ t) r'} := by
        ext p; simp only [hV, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
      rw [this]; exact h3.inter h2
    have hPV : ((τ.comp ι) g, (τ.comp ι) t, (τ.comp ι) a) ∈ V := by
      refine ⟨hτg τ, ?_, ?_⟩
      · show τ (ι t) ∈ _; exact hτ.1
      · show (τ.comp ι) a / (τ.comp ι) g ^ n ∈ _
        rw [← hxval τ]; exact hτ.2
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hVopen _ hPV
    refine ⟨{g, t, a}, ε, hε, fun σ' hσ' => ?_⟩
    have hg' := hσ' g (by simp)
    have ht' := hσ' t (by simp)
    have ha' := hσ' a (by simp)
    have hmem : (σ' g, σ' t, σ' a) ∈ V := by
      apply hεsub
      rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff]
      exact ⟨by rwa [dist_eq_norm], by rwa [dist_eq_norm], by rwa [dist_eq_norm]⟩
    obtain ⟨hg0, ht0, ha0⟩ := hmem
    dsimp only at hg0 ht0 ha0
    refine ⟨L σ' hg0, ⟨?_, ?_⟩, hLcomp σ' hg0⟩
    · rw [hL σ' hg0]; exact ht0
    · rw [hxval (L σ' hg0), hLcomp σ' hg0]; exact ha0

end S_Algebra_exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential
end P2MW
export P2MW.S_Algebra_exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential (solution)
