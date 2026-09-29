-- Prove2me | solution 1 for Algebra.exists_forall_mem_of_norm_sub_lt_of_bijOn_of_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/2c31f9b6-86bc-59dd-861d-cc45b16409e2

import Mathlib
import Theorems.Thm_Algebra_exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_forall_mem_of_norm_sub_lt_of_bijOn_of_differentiableOn

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Topology Filter

noncomputable section

namespace AptAnalysis

theorem exists_linearMap_D_eq_one
    (Sc : Type) [CommRing Sc] [Algebra ℂ Sc]
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ))
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰) :
    ∃ lam : KaehlerDifferential ℂ Sc →ₗ[Sc] Sc ⧸ RingHom.ker σ₁.toRingHom,
      lam (KaehlerDifferential.D ℂ Sc t) = 1 ∧
      ∀ n ∈ (RingHom.ker σ₁.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)), lam n = 0 := by
  classical
  set 𝔪 : Ideal Sc := RingHom.ker σ₁.toRingHom with h𝔪def
  set z₁ : ℂ := σ₁ t with hz₁def
  have hz₁ : z₁ ∈ Metric.ball (σ₀ t) r := hbij.mapsTo hσ₁
  have hnhds : Metric.ball (σ₀ t) r ∈ 𝓝 z₁ := Metric.isOpen_ball.mem_nhds hz₁
  choose F hF using hhol
  have hFd : ∀ s, DifferentiableAt ℂ (F s) z₁ := fun s => (hF s).1.differentiableAt hnhds
  have hFval : ∀ s, F s z₁ = σ₁ s := fun s => ((hF s).2 σ₁ hσ₁).symm
  have honball : ∀ {g g' : ℂ → ℂ}, (∀ σ ∈ 𝒰, g (σ t) = g' (σ t)) → g =ᶠ[𝓝 z₁] g' := by
    intro g g' h
    refine Filter.eventuallyEq_of_mem hnhds (fun z hz => ?_)
    obtain ⟨σ, hσ, rfl⟩ := hbij.surjOn hz
    exact h σ hσ
  set d : Sc → ℂ := fun s => deriv (F s) z₁ with hddef
  have hd_mul : ∀ a b : Sc, d (a * b) = σ₁ a * d b + σ₁ b * d a := by
    intro a b
    have heq : F (a * b) =ᶠ[𝓝 z₁] (fun z => F a z * F b z) :=
      honball (fun σ hσ => by rw [← (hF _).2 σ hσ, ← (hF a).2 σ hσ, ← (hF b).2 σ hσ, map_mul])
    show deriv (F (a * b)) z₁ = _
    rw [heq.deriv_eq, deriv_fun_mul (hFd a) (hFd b), hFval, hFval]
    ring
  have hd_add : ∀ a b : Sc, d (a + b) = d a + d b := by
    intro a b
    have heq : F (a + b) =ᶠ[𝓝 z₁] (fun z => F a z + F b z) :=
      honball (fun σ hσ => by rw [← (hF _).2 σ hσ, ← (hF a).2 σ hσ, ← (hF b).2 σ hσ, map_add])
    show deriv (F (a + b)) z₁ = _
    rw [heq.deriv_eq, deriv_fun_add (hFd a) (hFd b)]
  have hd_smul : ∀ (c : ℂ) (a : Sc), d (c • a) = c * d a := by
    intro c a
    have heq : F (c • a) =ᶠ[𝓝 z₁] (fun z => c * F a z) :=
      honball (fun σ hσ => by rw [← (hF _).2 σ hσ, ← (hF a).2 σ hσ, map_smul, smul_eq_mul])
    show deriv (F (c • a)) z₁ = _
    rw [heq.deriv_eq, deriv_const_mul c (hFd a)]
  have hd_t : d t = 1 := by
    have heq : F t =ᶠ[𝓝 z₁] (fun z => z) := honball (fun σ hσ => by rw [← (hF t).2 σ hσ])
    show deriv (F t) z₁ = 1
    rw [heq.deriv_eq, deriv_id'']
  set ι : ℂ →+* Sc ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp (algebraMap ℂ Sc) with hιdef
  have hmk : ∀ s : Sc, Ideal.Quotient.mk 𝔪 s = ι (σ₁ s) := by
    intro s
    show Ideal.Quotient.mk 𝔪 s = Ideal.Quotient.mk 𝔪 (algebraMap ℂ Sc (σ₁ s))
    rw [Ideal.Quotient.eq]
    show s - algebraMap ℂ Sc (σ₁ s) ∈ RingHom.ker σ₁.toRingHom
    rw [RingHom.mem_ker]
    simp
  have hsmulC : ∀ (c : ℂ) (q : Sc ⧸ 𝔪), c • q = ι c * q := by
    intro c q
    rw [Algebra.smul_def]
    congr 1
  have hsmulS : ∀ (a : Sc) (q : Sc ⧸ 𝔪), a • q = Ideal.Quotient.mk 𝔪 a * q := by
    intro a q
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  let Dpt : Derivation ℂ Sc (Sc ⧸ 𝔪) :=
    { toFun := fun s => ι (d s)
      map_add' := fun a b => by simp only [hd_add, map_add]
      map_smul' := fun c a => by simp only [hd_smul, map_mul, RingHom.id_apply, hsmulC]
      map_one_eq_zero' := by
        show ι (d 1) = 0
        have h : d 1 = d 1 + d 1 := by simpa using hd_mul 1 1
        have : d 1 = 0 := by linear_combination -h
        rw [this, map_zero]
      leibniz' := fun a b => by
        show ι (d (a * b)) = a • ι (d b) + b • ι (d a)
        rw [hsmulS, hsmulS, hmk a, hmk b, hd_mul, map_add, map_mul, map_mul] }
  refine ⟨Dpt.liftKaehlerDifferential, ?_, ?_⟩
  · rw [Derivation.liftKaehlerDifferential_comp_D]
    show ι (d t) = 1
    rw [hd_t, map_one]
  · intro n hn
    refine Submodule.smul_induction_on hn (fun a ha ω _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, hsmulS, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
    · rw [map_add, hx, hy, add_zero]

theorem D_notMem_ker_smul_top
    (Sc : Type) [CommRing Sc] [Algebra ℂ Sc]
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ))
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰) :
    KaehlerDifferential.D ℂ Sc t ∉ (RingHom.ker σ₁.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) := by
  obtain ⟨lam, h1, h0⟩ := exists_linearMap_D_eq_one Sc t σ₀ r 𝒰 hbij hhol σ₁ hσ₁
  intro hmem
  haveI : (RingHom.ker σ₁.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective σ₁.toRingHom (fun c => ⟨algebraMap ℂ Sc c, σ₁.commutes c⟩)
  haveI : Nontrivial (Sc ⧸ RingHom.ker σ₁.toRingHom) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
  have := h0 _ hmem
  rw [h1] at this
  exact one_ne_zero this

theorem mem_branch_of_near
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰) :
    ∃ (fs : Finset Sc) (δ : ℝ), 0 < δ ∧
      ∀ τ : Sc →ₐ[ℂ] ℂ, (∀ s ∈ fs, ‖τ s - σ₁ s‖ < δ) → τ ∈ 𝒰 := by
  classical

  have hnot := D_notMem_ker_smul_top Sc t σ₀ r 𝒰 hbij hhol σ₁ hσ₁
  obtain ⟨r', 𝒰', hr', hσ₁', hbij', -, hopen'⟩ :=
    Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential Sc hSc hΩ σ₁ t hnot
  obtain ⟨fs', ε', hε', hval'⟩ := hopen' σ₁ hσ₁'

  set z₁ : ℂ := σ₁ t with hz₁def
  have hz₁ : z₁ ∈ Metric.ball (σ₀ t) r := hbij.mapsTo hσ₁
  have hnhds : Metric.ball (σ₀ t) r ∈ 𝓝 z₁ := Metric.isOpen_ball.mem_nhds hz₁
  choose F hF using hhol
  have hFval : ∀ s, F s z₁ = σ₁ s := fun s => ((hF s).2 σ₁ hσ₁).symm
  have hFc : ∀ s, ContinuousAt (F s) z₁ := fun s => ((hF s).1.differentiableAt hnhds).continuousAt
  have hev : ∀ᶠ z in 𝓝 z₁, z ∈ Metric.ball (σ₀ t) r ∧ z ∈ Metric.ball z₁ r' ∧ ∀ s ∈ fs', ‖F s z - F s z₁‖ < ε' := by
    refine Filter.Eventually.and hnhds (Filter.Eventually.and (Metric.ball_mem_nhds z₁ hr') ?_)
    rw [Filter.eventually_all_finset]
    intro s _
    have := (hFc s).preimage_mem_nhds (Metric.ball_mem_nhds (F s z₁) hε')
    filter_upwards [this] with z hz
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev

  have hbranch : ∀ z ∈ Metric.ball z₁ δ₁, ∃ σ ∈ 𝒰, σ t = z ∧ σ ∈ 𝒰' := by
    intro z hz
    obtain ⟨hzr, -, hclose⟩ := hball z hz
    obtain ⟨σ, hσ, hσt⟩ := hbij.surjOn hzr
    refine ⟨σ, hσ, hσt, hval' σ (fun s hs => ?_)⟩
    rw [(hF s).2 σ hσ, ← hFval s]
    have : σ t = z := hσt
    rw [this]
    exact hclose s hs
  refine ⟨insert t fs', min ε' δ₁, lt_min hε' hδ₁, fun τ hτ => ?_⟩
  have hτ' : τ ∈ 𝒰' := hval' τ (fun s hs => lt_of_lt_of_le (hτ s (Finset.mem_insert_of_mem hs)) (min_le_left _ _))
  have hτt : τ t ∈ Metric.ball z₁ δ₁ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le (hτ t (Finset.mem_insert_self t fs')) (min_le_right _ _)
  obtain ⟨σ, hσ, hσt, hσ'⟩ := hbranch (τ t) hτt
  have : τ = σ := hbij'.injOn hτ' hσ' (by simp [hσt])
  rw [this]; exact hσ

end AptAnalysis

theorem solution
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰) :
    ∃ (fs : Finset Sc) (δ : ℝ), 0 < δ ∧
      ∀ τ : Sc →ₐ[ℂ] ℂ, (∀ s ∈ fs, ‖τ s - σ₁ s‖ < δ) →
        τ ∈ 𝒰 ∧ ∀ σ ∈ 𝒰, σ t = τ t → σ = τ := by
  obtain ⟨fs, δ, hδ, h⟩ := AptAnalysis.mem_branch_of_near Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol σ₁ hσ₁
  exact ⟨fs, δ, hδ, fun τ hτ => ⟨h τ hτ, fun σ hσ hσt => hbij.injOn hσ (h τ hτ) hσt⟩⟩

end
end S_Algebra_exists_forall_mem_of_norm_sub_lt_of_bijOn_of_differentiableOn
end P2MW
export P2MW.S_Algebra_exists_forall_mem_of_norm_sub_lt_of_bijOn_of_differentiableOn (solution)
