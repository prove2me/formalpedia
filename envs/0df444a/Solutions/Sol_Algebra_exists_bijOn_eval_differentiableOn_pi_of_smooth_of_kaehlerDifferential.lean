-- Prove2me | solution 1 for Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/93635b34-d54c-5cf4-961d-98deb8af28b3

import Mathlib
import Theorems.Thm_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential
import Theorems.Thm_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial
import Theorems.Thm_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential

set_option autoImplicit false

open Topology
open Polynomial

namespace K1Aux

theorem contDiff_eval {n : ℕ} (a : MvPolynomial (Fin n) ℂ) : ContDiff ℂ ⊤ (fun z : Fin n → ℂ => MvPolynomial.eval z a) :=
  (AnalyticOnNhd.eval_mvPolynomial a).contDiff

theorem contDiff_mapEval {n : ℕ} (q : Polynomial (MvPolynomial (Fin n) ℂ)) :
    ContDiff ℂ ⊤ (fun p : (Fin n → ℂ) × ℂ => (q.map (MvPolynomial.eval p.1)).eval p.2) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    have : (fun v : (Fin n → ℂ) × ℂ => ((p + q).map (MvPolynomial.eval v.1)).eval v.2) =
        (fun v : (Fin n → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) +
          fun v : (Fin n → ℂ) × ℂ => (q.map (MvPolynomial.eval v.1)).eval v.2 := by
      funext v; simp [Polynomial.map_add]
    rw [this]; exact hp.add hq
  | monomial m a =>
    have : (fun v : (Fin n → ℂ) × ℂ => ((monomial m a).map (MvPolynomial.eval v.1)).eval v.2) =
        fun v : (Fin n → ℂ) × ℂ => MvPolynomial.eval v.1 a * v.2 ^ m := by
      funext v
      rw [Polynomial.map_monomial, ← C_mul_X_pow_eq_monomial, eval_mul, eval_pow, eval_C, eval_X]
    rw [this]
    exact ((contDiff_eval a).comp contDiff_fst).mul (contDiff_snd.pow m)

theorem differentiableOn_mapEval_comp {n : ℕ} (q : Polynomial (MvPolynomial (Fin n) ℂ)) {φ : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hφ : DifferentiableOn ℂ φ U) :
    DifferentiableOn ℂ (fun z => (q.map (MvPolynomial.eval z)).eval (φ z)) U := by
  have h1 : Differentiable ℂ (fun p : (Fin n → ℂ) × ℂ => (q.map (MvPolynomial.eval p.1)).eval p.2) :=
    (contDiff_mapEval q).differentiable (by simp)
  exact h1.comp_differentiableOn (differentiableOn_id.prodMk hφ)

end K1Aux

theorem solution
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    {n : ℕ} (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : Fin n → S)
    (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
        Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
    ∃ (r : ℝ) (𝒰 : Set (S →ₐ[ℂ] ℂ)), 0 < r ∧ σ₀ ∈ 𝒰 ∧
      Set.BijOn (fun σ : S →ₐ[ℂ] ℂ => fun i : Fin n => σ (t i)) 𝒰
        (Metric.ball (fun i : Fin n => σ₀ (t i)) r) ∧
      (∀ s : S, ∃ F : (Fin n → ℂ) → ℂ,
        DifferentiableOn ℂ F (Metric.ball (fun i : Fin n => σ₀ (t i)) r) ∧
        ∀ σ ∈ 𝒰, σ s = F (fun i : Fin n => σ (t i))) ∧

      (∀ σ ∈ 𝒰, ∃ (fs : Finset S) (ε : ℝ), 0 < ε ∧
        ∀ σ' : S →ₐ[ℂ] ℂ, (∀ s ∈ fs, ‖σ' s - σ s‖ < ε) → σ' ∈ 𝒰) := by
  classical

  obtain ⟨g, hg, hSE⟩ := Algebra.exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential S hsm hrank σ₀ t hdt
  letI instA : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g) :=
    ((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI : Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) (Localization.Away g) := hSE
  have halg : ∀ p : MvPolynomial (Fin n) ℂ, algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away g) p =
      algebraMap S (Localization.Away g) (MvPolynomial.aeval t p) := fun p => rfl
  haveI : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) (Localization.Away g) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [halg, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]

  obtain ⟨x, F, G, hpt, hinjc, hsurjc, hrepr⟩ := Algebra.IsStandardEtale.exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial ℂ (n := n) (Localization.Away g)
  have hXt : ∀ i : Fin n, algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away g) (MvPolynomial.X i) =
      algebraMap S (Localization.Away g) (t i) := by
    intro i; rw [halg, MvPolynomial.aeval_X]
  simp only [hXt] at hpt hinjc hsurjc hrepr

  let ι : S →ₐ[ℂ] (Localization.Away g) := IsScalarTower.toAlgHom ℂ S (Localization.Away g)
  have hι : ∀ s : S, ι s = algebraMap S (Localization.Away g) s := fun s => rfl
  have hunit : ∀ (σ : S →ₐ[ℂ] ℂ), σ g ≠ 0 → ∀ y : Submonoid.powers g, IsUnit (σ y) := by
    rintro σ hσ ⟨y, m, rfl⟩
    rw [map_pow]; exact (isUnit_iff_ne_zero.2 hσ).pow m
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

  obtain ⟨⟨a, ⟨gm, m, rfl⟩⟩, hax⟩ := IsLocalization.surj (Submonoid.powers g) x
  have hxval : ∀ τ : (Localization.Away g) →ₐ[ℂ] ℂ, τ x = (τ.comp ι) a / ((τ.comp ι) g) ^ m := by
    intro τ
    have h1 := congrArg τ hax
    rw [map_mul, map_pow (algebraMap S (Localization.Away g)), map_pow] at h1
    rw [eq_div_iff (pow_ne_zero _ (hτg τ))]
    exact h1

  have hcoord : ∀ τ : (Localization.Away g) →ₐ[ℂ] ℂ, (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))) =
      fun i : Fin n => (τ.comp ι) (t i) := fun τ => rfl

  let τ₀ : (Localization.Away g) →ₐ[ℂ] ℂ := L σ₀ hg
  have hτ₀ : ∀ s : S, τ₀ (algebraMap S (Localization.Away g) s) = σ₀ s := hL σ₀ hg
  obtain ⟨hF0, hG0, hD0⟩ := hpt τ₀
  simp only [hτ₀] at hF0 hG0 hD0

  obtain ⟨r, ρ, φ, hr, hρ, hφ0, hφd, -, hφF, hφuniq⟩ :=
    Complex.exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi F (fun i : Fin n => σ₀ (t i)) (τ₀ x) hF0 hD0

  have hGcont : ContinuousAt (fun z : Fin n → ℂ => (G.map (MvPolynomial.eval z)).eval (φ z)) (fun i : Fin n => σ₀ (t i)) := by
    have hφc : ContinuousAt φ (fun i : Fin n => σ₀ (t i)) := (hφd.differentiableAt (Metric.ball_mem_nhds _ hr)).continuousAt
    exact ((K1Aux.contDiff_mapEval G).continuous.continuousAt).comp (continuousAt_id.prodMk hφc)
  have hGnbhd : ∀ᶠ z in 𝓝 (fun i : Fin n => σ₀ (t i)), (G.map (MvPolynomial.eval z)).eval (φ z) ≠ 0 := by
    refine hGcont.eventually_ne ?_
    rw [hφ0]; exact hG0
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhds_iff.1 hGnbhd
  set r' := min r r₁ with hr'
  have hr'pos : 0 < r' := lt_min hr hr₁
  have hb1 : ∀ z ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r', z ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r := fun z hz =>
    Metric.ball_subset_ball (min_le_left _ _) hz
  have hb2 : ∀ z ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r', (G.map (MvPolynomial.eval z)).eval (φ z) ≠ 0 := fun z hz =>
    hr₁sub (Metric.ball_subset_ball (min_le_right _ _) hz)

  set 𝒱 : Set ((Localization.Away g) →ₐ[ℂ] ℂ) :=
    {τ | (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))) ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r' ∧
      τ x ∈ Metric.ball (τ₀ x) ρ} with h𝒱
  set 𝒰 : Set (S →ₐ[ℂ] ℂ) := (fun τ : (Localization.Away g) →ₐ[ℂ] ℂ => τ.comp ι) '' 𝒱 with h𝒰

  have hφτ : ∀ τ ∈ 𝒱, τ x = φ (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))) := by
    intro τ hτ
    exact hφuniq _ (hb1 _ hτ.1) _ hτ.2 (hpt τ).1
  refine ⟨r', 𝒰, hr'pos, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨τ₀, ⟨?_, ?_⟩, hLcomp σ₀ hg⟩
    · simp only [hτ₀]; exact Metric.mem_ball_self hr'pos
    · exact Metric.mem_ball_self hρ
  ·
    refine ⟨?_, ?_, ?_⟩
    · rintro σ ⟨τ, hτ, rfl⟩
      exact hτ.1
    · rintro σ ⟨τ, hτ, rfl⟩ σ' ⟨τ', hτ', rfl⟩ heq
      change (fun i : Fin n => τ (ι (t i))) = fun i : Fin n => τ' (ι (t i)) at heq
      have hx' : τ x = τ' x := by
        rw [hφτ τ hτ, hφτ τ' hτ']
        exact congrArg φ heq
      rw [hinjc τ τ' (fun i => congrFun heq i) hx']
    · intro z hz
      obtain ⟨hw, hFz⟩ := hφF z (hb1 z hz)
      obtain ⟨τ, hτt, hτx⟩ := hsurjc z (φ z) hFz (hb2 z hz)
      have hzt : (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))) = z := funext hτt
      refine ⟨τ.comp ι, ⟨τ, ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · rw [hzt]; exact hz
      · rw [hτx]; exact hw
      · exact hzt
  ·
    intro s
    obtain ⟨h, k, hk⟩ := hrepr (algebraMap S (Localization.Away g) s)
    refine ⟨fun z => (h.map (MvPolynomial.eval z)).eval (φ z) / ((G.map (MvPolynomial.eval z)).eval (φ z)) ^ k, ?_, ?_⟩
    · have hφ' : DifferentiableOn ℂ φ (Metric.ball (fun i : Fin n => σ₀ (t i)) r') := hφd.mono fun z hz => hb1 z hz
      have hden : DifferentiableOn ℂ (fun z : Fin n → ℂ => ((G.map (MvPolynomial.eval z)).eval (φ z)) ^ k)
          (Metric.ball (fun i : Fin n => σ₀ (t i)) r') := by
        have := (K1Aux.differentiableOn_mapEval_comp G hφ').pow k
        simpa only [Pi.pow_def] using this
      have hfun : (fun z : Fin n → ℂ => (h.map (MvPolynomial.eval z)).eval (φ z) / ((G.map (MvPolynomial.eval z)).eval (φ z)) ^ k) =
          fun z => (h.map (MvPolynomial.eval z)).eval (φ z) * (((G.map (MvPolynomial.eval z)).eval (φ z)) ^ k)⁻¹ := by
        funext z; rw [div_eq_mul_inv]
      rw [hfun]
      exact (K1Aux.differentiableOn_mapEval_comp h hφ').mul (hden.inv fun z hz => pow_ne_zero _ (hb2 z hz))
    · rintro σ ⟨τ, hτ, rfl⟩
      show τ (algebraMap S (Localization.Away g) s) =
        (h.map (MvPolynomial.eval (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))))).eval
            (φ (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i)))) /
          ((G.map (MvPolynomial.eval (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))))).eval
            (φ (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))))) ^ k
      rw [← hφτ τ hτ, eq_div_iff (pow_ne_zero _ ?_)]
      · exact hk τ
      · rw [hφτ τ hτ]; exact hb2 _ hτ.1
  ·
    rintro σ ⟨τ, hτ, rfl⟩
    set V : Set (ℂ × (Fin n → ℂ) × ℂ) :=
      {p | p.1 ≠ 0 ∧ p.2.1 ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r' ∧ p.2.2 / p.1 ^ m ∈ Metric.ball (τ₀ x) ρ} with hV
    have hVopen : IsOpen V := by
      have h1 : IsOpen {p : ℂ × (Fin n → ℂ) × ℂ | p.1 ≠ 0} := isOpen_ne_fun continuous_fst continuous_const
      have hc : ContinuousOn (fun p : ℂ × (Fin n → ℂ) × ℂ => p.2.2 / p.1 ^ m) {p : ℂ × (Fin n → ℂ) × ℂ | p.1 ≠ 0} :=
        (continuous_snd.comp continuous_snd).continuousOn.div ((continuous_fst.pow m).continuousOn)
          fun p hp => pow_ne_zero _ hp
      have h3 : IsOpen {p : ℂ × (Fin n → ℂ) × ℂ | p.1 ≠ 0 ∧ p.2.2 / p.1 ^ m ∈ Metric.ball (τ₀ x) ρ} :=
        hc.isOpen_inter_preimage h1 Metric.isOpen_ball
      have h2 : IsOpen {p : ℂ × (Fin n → ℂ) × ℂ | p.2.1 ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r'} :=
        Metric.isOpen_ball.preimage (continuous_fst.comp continuous_snd)
      have : V = {p : ℂ × (Fin n → ℂ) × ℂ | p.1 ≠ 0 ∧ p.2.2 / p.1 ^ m ∈ Metric.ball (τ₀ x) ρ} ∩
          {p | p.2.1 ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r'} := by
        ext p; simp only [hV, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
      rw [this]; exact h3.inter h2
    have hPV : ((τ.comp ι) g, (fun i : Fin n => (τ.comp ι) (t i)), (τ.comp ι) a) ∈ V := by
      refine ⟨hτg τ, ?_, ?_⟩
      · exact hτ.1
      · show (τ.comp ι) a / (τ.comp ι) g ^ m ∈ _
        rw [← hxval τ]; exact hτ.2
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hVopen _ hPV
    refine ⟨insert g (insert a (Finset.univ.image t)), ε, hε, fun σ' hσ' => ?_⟩
    have hg' := hσ' g (by simp)
    have ha' := hσ' a (by simp)
    have ht' : ∀ i : Fin n, ‖σ' (t i) - (τ.comp ι) (t i)‖ < ε := fun i => hσ' (t i) (by simp)
    have hmem : (σ' g, (fun i : Fin n => σ' (t i)), σ' a) ∈ V := by
      apply hεsub
      rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff]
      refine ⟨by rwa [dist_eq_norm], ?_, by rwa [dist_eq_norm]⟩
      rw [dist_pi_lt_iff hε]
      intro i; rw [dist_eq_norm]; exact ht' i
    obtain ⟨hg0, ht0, ha0⟩ := hmem
    dsimp only at hg0 ht0 ha0
    refine ⟨L σ' hg0, ⟨?_, ?_⟩, hLcomp σ' hg0⟩
    · simp only [hL σ' hg0]; exact ht0
    · rw [hxval (L σ' hg0), hLcomp σ' hg0]; exact ha0

end S_Algebra_exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential
end P2MW
export P2MW.S_Algebra_exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential (solution)
