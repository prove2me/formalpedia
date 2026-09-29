-- Prove2me | solution 1 for AlgebraicGeometry.SmoothOfRelativeDimension.exists_relChart_differentiableOn_appLE_of_analyticChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0f7be322-afc6-5e28-8584-2c15ab28522d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_le_etaleCoordinates_cons_algebraMap_of_point
import Theorems.Thm_Algebra_exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_appLE_of_forall_section
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom
import Theorems.Thm_Algebra_exists_forall_mem_of_norm_sub_lt_of_bijOn_of_differentiableOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_relChart_differentiableOn_appLE_of_analyticChart
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

namespace P2mWs30RelAChart

theorem appLE_top_top {X Y : Scheme} (g : X ⟶ Y) (h : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) :
    g.appLE ⊤ ⊤ h = g.appTop := by
  show _ = g.app ⊤
  rw [Scheme.Hom.app_eq_appLE]
  rfl

theorem appLE_apply_congr {X Y : Scheme} {p q : X ⟶ Y} (e : p = q) (V : Y.Opens)
    (hp : ⊤ ≤ p ⁻¹ᵁ V) (hq : ⊤ ≤ q ⁻¹ᵁ V) (x : Γ(Y, V)) :
    (p.appLE V ⊤ hp) x = (q.appLE V ⊤ hq) x := by
  subst e; rfl

theorem specMap_algHom_comp {Sc : Type} [CommRing Sc] [Algebra ℂ Sc] (σ : Sc →ₐ[ℂ] ℂ) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc)) = 𝟙 _ := by
  rw [← Spec.map_comp]
  have : CommRingCat.ofHom (algebraMap ℂ Sc) ≫ CommRingCat.ofHom σ.toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    ext x
    simp
  rw [this, Spec.map_id]

theorem eval_algebraMap {k : Type} [CommRing k] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of k))
    (P : Spec (CommRingCat.of k) ⟶ X) (hP : P ≫ π = 𝟙 _) (U : X.Opens) (hPU : ⊤ ≤ P ⁻¹ᵁ U)
    (z : k) :
    letI := π.sectionsAlgebra U
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((P.appLE U ⊤ hPU).hom (algebraMap k Γ(X, U) z)) =
      z := by
  letI := π.sectionsAlgebra U
  show (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((P.appLE U ⊤ hPU).hom
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ π.appLE ⊤ U le_top).hom z)) = z
  have h1 : π.appLE ⊤ U le_top ≫ P.appLE U ⊤ hPU = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE, appLE_top_top, hP, Scheme.Hom.id_appTop]
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (π.appLE ⊤ U le_top ≫ P.appLE U ⊤ hPU) ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom = 𝟙 _ := by
    rw [h1]; simp
  have := congrArg (fun φ => φ.hom z) h3
  simpa using this

theorem eval_comp_algebraMap {k A : Type} [CommRing k] [CommRing A] {X : Scheme.{0}}
    (π : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* k)
    (P : Spec (CommRingCat.of k) ⟶ X) (hP : P ≫ π = Spec.map (CommRingCat.ofHom σ))
    (U : X.Opens) (hPU : ⊤ ≤ P ⁻¹ᵁ U) (a : A) :
    letI := π.sectionsAlgebra U
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((P.appLE U ⊤ hPU).hom (algebraMap A Γ(X, U) a)) =
      σ a := by
  letI := π.sectionsAlgebra U
  show (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((P.appLE U ⊤ hPU).hom
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ π.appLE ⊤ U le_top).hom a)) = σ a
  have h1 : π.appLE ⊤ U le_top ≫ P.appLE U ⊤ hPU = (Spec.map (CommRingCat.ofHom σ)).appTop := by
    rw [Scheme.Hom.appLE_comp_appLE, appLE_top_top, hP]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (π.appLE ⊤ U le_top ≫ P.appLE U ⊤ hPU) ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom = CommRingCat.ofHom σ := by
    rw [h1, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have := congrArg (fun φ => φ.hom a) h2
  simpa using this

theorem appLE_top_apply_eq_algebraMap {A : Type} [CommRing A] {X : Scheme.{0}}
    (π : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens) (a' : Γ(Spec (CommRingCat.of A), ⊤)) :
    letI := π.sectionsAlgebra U
    (π.appLE ⊤ U le_top) a' = algebraMap A Γ(X, U) ((Scheme.ΓSpecIso (CommRingCat.of A)).hom a') := by
  letI := π.sectionsAlgebra U
  show (π.appLE ⊤ U le_top).hom a' = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ π.appLE ⊤ U le_top).hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a')
  have h := congrArg (fun φ => φ.hom a') (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id
  simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] at h ⊢
  rw [h]

theorem comp_eq_specMap_of_eval {Sc : Type} [CommRing Sc] [Algebra ℂ Sc] {G : Scheme.{0}}
    (f : G ⟶ Spec (CommRingCat.of Sc)) (U : G.Opens) (p : Spec (CommRingCat.of ℂ) ⟶ G)
    (hpU : ⊤ ≤ p ⁻¹ᵁ U) (hp1 : p ≫ (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))) = 𝟙 _) (σ : Sc →ₐ[ℂ] ℂ)
    (heval : letI := f.sectionsAlgebra U
      ∀ a : Sc, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE U ⊤ hpU) (algebraMap Sc Γ(G, U) a)) = σ a) :
    p ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  letI := f.sectionsAlgebra U
  have KP := (AlgebraicGeometry.IsAffineOpen.eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))) ⊤ (isAffineOpen_top _)).1
  refine KP (p ≫ f) (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by rw [Category.assoc]; exact hp1)
    (specMap_algHom_comp σ) le_top le_top ?_
  apply CommRingCat.hom_ext
  ext a'
  have h1 : (p ≫ f).appLE ⊤ ⊤ le_top = f.appLE ⊤ U le_top ≫ p.appLE U ⊤ hpU :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 : (Spec.map (CommRingCat.ofHom σ.toRingHom)).appLE ⊤ ⊤ le_top ≫
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of Sc)).hom ≫ CommRingCat.ofHom σ.toRingHom := by
    rw [appLE_top_top, Scheme.ΓSpecIso_naturality]
  rw [h1, h2]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE U ⊤ hpU) ((f.appLE ⊤ U le_top) a')) =
    σ.toRingHom ((Scheme.ΓSpecIso (CommRingCat.of Sc)).hom a')
  rw [appLE_top_apply_eq_algebraMap f U a', heval]
  rfl

theorem dist_finCons_lt_iff {n : ℕ} (a a' : ℂ) (b b' : Fin n → ℂ) {R : ℝ} (hR : 0 < R) :
    dist (Fin.cons a b : Fin (n + 1) → ℂ) (Fin.cons a' b') < R ↔ dist a a' < R ∧ dist b b' < R := by
  rw [dist_pi_lt_iff hR, dist_pi_lt_iff hR, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem differentiableOn_comp_finCons {n : ℕ} {F : (Fin (n + 1) → ℂ) → ℂ} {z₁ : ℂ} {v₀ : Fin n → ℂ}
    {R ρ : ℝ} (hF : DifferentiableOn ℂ F (Metric.ball (Fin.cons z₁ v₀) R)) (hρ : ρ ≤ R) (hρ0 : 0 < ρ) :
    DifferentiableOn ℂ (fun p : ℂ × (Fin n → ℂ) => F (Fin.cons p.1 p.2))
      {p : ℂ × (Fin n → ℂ) | p.1 ∈ Metric.ball z₁ ρ ∧ p.2 ∈ Metric.ball v₀ ρ} := by
  have hcons : Differentiable ℂ (fun p : ℂ × (Fin n → ℂ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ)) := by
    refine differentiable_pi.mpr ?_
    refine Fin.cases ?_ ?_
    · simpa using differentiable_fst
    · intro i
      simpa using (differentiable_pi.mp differentiable_snd i)
  refine hF.comp hcons.differentiableOn ?_
  intro p hp
  rw [Metric.mem_ball, dist_finCons_lt_iff _ _ _ _ (hρ0.trans_le hρ)]
  exact ⟨(Metric.mem_ball.mp hp.1).trans_le hρ, (Metric.mem_ball.mp hp.2).trans_le hρ⟩

end P2mWs30RelAChart

open P2mWs30RelAChart in
theorem solution

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    {G : Scheme.{0}} (f : G ⟶ Spec (CommRingCat.of Sc)) {g : ℕ} (hsm : SmoothOfRelativeDimension g f)
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰)
    (hdt₁ : ((RingHom.ker σ₁.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) ⊔
        Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} = ⊤))
    (P₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom σ₁.toRingHom)) f) :
    ∃ (ε ρ' : ℝ) (_ : 0 < ε) (_ : 0 < ρ') (_ : Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₀ t) r)
      (U : G.Opens) (_ : IsAffineOpen U) (s : Fin g → Γ(G, U)) (v₀ : Fin g → ℂ)
      (ψ : (Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ G))
      (hU : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ⊤ ≤ (ψ σ v) ⁻¹ᵁ U)
      (hP₀U : ⊤ ≤ P₀.1 ⁻¹ᵁ U),

      (∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ',
        ψ σ v ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom)) ∧

      ψ σ₁ v₀ = P₀.1 ∧

      (∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₁ t) ε) (v : Fin g → ℂ) (hv : v ∈ Metric.ball v₀ ρ')
        (i : Fin g), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ σ v).appLE U ⊤ (hU σ hσ hz v hv)) (s i)) = v i) ∧

      (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₀ ρ' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ σ p.2) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin g → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₀ ρ' ∧
            ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ σ p.2) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ∀ (hV : ⊤ ≤ (ψ σ v) ⁻¹ᵁ V),
            F (σ t, v) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ σ v).appLE V ⊤ hV) φ)) ∧

      (∃ (fs : Finset (Γ(G, U))) (η : ℝ), 0 < η ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε →
          ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
            (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P).1.appLE U ⊤ hP) φ) - (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P₀).1.appLE U ⊤ hP₀U) φ)‖ < η) →
            ∃ v ∈ Metric.ball v₀ ρ', ψ σ v = P.1) := by
  classical
  obtain ⟨P₀, hP₀⟩ := P₀
  haveI := hsm

  obtain ⟨U, hUaff, -, hP₀U, htower, hdom, hft, hsmB, hrankB, χ₀, s, hχ₀, hχ₀Sc, hdt⟩ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_le_etaleCoordinates_cons_algebraMap_of_point
      Sc hSc hΩ t f hsm σ₁ hdt₁ P₀ hP₀ ⊤ le_top
  letI instSc : Algebra Sc Γ(G, U) := f.sectionsAlgebra U
  letI instC : Algebra ℂ Γ(G, U) := (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))).sectionsAlgebra U
  haveI := htower
  haveI := hdom
  haveI := hft
  have hP₀C : P₀ ≫ (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))) = 𝟙 _ := by
    rw [← Category.assoc, hP₀, specMap_algHom_comp]

  let φ : Sc →ₐ[ℂ] Γ(G, U) := IsScalarTower.toAlgHom ℂ Sc Γ(G, U)
  have hφ : ∀ a, φ a = algebraMap Sc Γ(G, U) a := fun a => rfl

  set tt : Fin (g + 1) → Γ(G, U) := Fin.cons (algebraMap Sc Γ(G, U) t) s with htt
  obtain ⟨r₁, 𝒰B, hr₁, hχ₀U, hbijB, hholB, hopenB⟩ :=
    Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential Γ(G, U) hsmB hrankB χ₀ tt
      hdt

  set co : (Γ(G, U) →ₐ[ℂ] ℂ) → (Fin (g + 1) → ℂ) := fun χ => fun i => χ (tt i) with hco
  set v₀ : Fin g → ℂ := fun i => χ₀ (s i) with hv₀
  have hw₀ : co χ₀ = Fin.cons (σ₁ t) v₀ := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hco, htt, hχ₀Sc]
    · simp [hco, htt, hv₀]

  haveI : Nonempty (Γ(G, U) →ₐ[ℂ] ℂ) := ⟨χ₀⟩
  set Φ : (Fin (g + 1) → ℂ) → (Γ(G, U) →ₐ[ℂ] ℂ) := Function.invFunOn co 𝒰B with hΦ
  have hΦmem : ∀ w ∈ Metric.ball (co χ₀) r₁, Φ w ∈ 𝒰B := fun w hw =>
    Function.invFunOn_mem (hbijB.surjOn hw)
  have hcoΦ : ∀ w ∈ Metric.ball (co χ₀) r₁, co (Φ w) = w := fun w hw =>
    Function.invFunOn_eq (hbijB.surjOn hw)
  have hΦco : ∀ χ ∈ 𝒰B, Φ (co χ) = χ := fun χ hχ => hbijB.injOn.leftInvOn_invFunOn hχ

  choose Fb hFb hFbval using hholB
  have hΦval : ∀ (b : Γ(G, U)), ∀ w ∈ Metric.ball (co χ₀) r₁, Φ w b = Fb b w := by
    intro b w hw
    have h := hcoΦ w hw
    simp only [hco] at h
    rw [hFbval b (Φ w) (hΦmem w hw), h]
  have hcont : ∀ b : Γ(G, U), ContinuousOn (fun w => Φ w b) (Metric.ball (co χ₀) r₁) := fun b =>
    ((hFb b).continuousOn).congr (fun w hw => hΦval b w hw)

  obtain ⟨fsb, δb, hδb, hbranch⟩ :=
    Algebra.exists_forall_mem_of_norm_sub_lt_of_bijOn_of_differentiableOn Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol
      σ₁ hσ₁

  obtain ⟨ρ, hρ0, hρr₁, hρclose⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r₁ ∧
      ∀ w ∈ Metric.ball (co χ₀) ρ, ∀ a ∈ fsb, ‖Φ w (φ a) - σ₁ a‖ < δb := by
    have hev : ∀ᶠ w in 𝓝 (co χ₀), ∀ a ∈ fsb, ‖Φ w (φ a) - σ₁ a‖ < δb := by
      rw [Filter.eventually_all_finset]
      intro a _
      have hca : ContinuousAt (fun w => Φ w (φ a)) (co χ₀) :=
        (hcont (φ a)).continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₁))
      have h0 : Φ (co χ₀) (φ a) = σ₁ a := by rw [hΦco χ₀ hχ₀U, hφ, hχ₀Sc]
      have := (Metric.tendsto_nhds.mp hca) δb hδb
      refine this.mono fun w hw => ?_
      dsimp only at hw
      rwa [h0, dist_eq_norm] at hw
    obtain ⟨δ', hδ', hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨min δ' r₁, lt_min hδ' hr₁, min_le_right _ _, fun w hw a ha => ?_⟩
    exact hball w (Metric.ball_subset_ball (min_le_left _ _) hw) a ha

  have hρsub : Metric.ball (co χ₀) ρ ⊆ Metric.ball (co χ₀) r₁ := Metric.ball_subset_ball hρr₁
  have hcomp : ∀ w ∈ Metric.ball (co χ₀) ρ, (Φ w).comp φ ∈ 𝒰 ∧
      ∀ σ ∈ 𝒰, σ t = Φ w (φ t) → σ = (Φ w).comp φ := by
    intro w hw
    exact hbranch ((Φ w).comp φ) (fun a ha => hρclose w hw a ha)

  have hmemρ : ∀ (σ : Sc →ₐ[ℂ] ℂ) (v : Fin g → ℂ), σ t ∈ Metric.ball (σ₁ t) ρ →
      v ∈ Metric.ball v₀ ρ → (Fin.cons (σ t) v : Fin (g + 1) → ℂ) ∈ Metric.ball (co χ₀) ρ := by
    intro σ v hz hv
    rw [Metric.mem_ball, hw₀, dist_finCons_lt_iff _ _ _ _ hρ0]
    exact ⟨hz, hv⟩
  have hcons0 : ∀ (z : ℂ) (v : Fin g → ℂ), (Fin.cons z v : Fin (g + 1) → ℂ) 0 = z := fun z v => rfl
  have hfirst : ∀ (σ : Sc →ₐ[ℂ] ℂ) (v : Fin g → ℂ), σ t ∈ Metric.ball (σ₁ t) ρ →
      v ∈ Metric.ball v₀ ρ → Φ (Fin.cons (σ t) v) (φ t) = σ t := by
    intro σ v hz hv
    have := congrFun (hcoΦ _ (hρsub (hmemρ σ v hz hv))) 0
    simp [hco, htt] at this
    exact this
  have hcoord : ∀ (σ : Sc →ₐ[ℂ] ℂ) (v : Fin g → ℂ), σ t ∈ Metric.ball (σ₁ t) ρ →
      v ∈ Metric.ball v₀ ρ → ∀ i : Fin g, Φ (Fin.cons (σ t) v) (s i) = v i := by
    intro σ v hz hv i
    have := congrFun (hcoΦ _ (hρsub (hmemρ σ v hz hv))) (Fin.succ i)
    simpa [hco, htt] using this
  have hover : ∀ σ ∈ 𝒰, ∀ (v : Fin g → ℂ), σ t ∈ Metric.ball (σ₁ t) ρ → v ∈ Metric.ball v₀ ρ →
      (Φ (Fin.cons (σ t) v)).comp φ = σ := by
    intro σ hσ v hz hv
    exact ((hcomp _ (hmemρ σ v hz hv)).2 σ hσ (hfirst σ v hz hv).symm).symm

  have KP := AlgebraicGeometry.IsAffineOpen.eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))) U hUaff
  have hcompat : ∀ χ : Γ(G, U) →ₐ[ℂ] ℂ,
      χ.toRingHom.comp ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))).appLE ⊤ U le_top).hom =
        RingHom.id ℂ := by
    intro χ
    ext z
    exact χ.commutes z
  choose pt hpt1 hptU hpteval using fun χ : Γ(G, U) →ₐ[ℂ] ℂ => KP.2 χ.toRingHom (hcompat χ)
  have hptval : ∀ (χ : Γ(G, U) →ₐ[ℂ] ℂ) (b : Γ(G, U)),
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((pt χ).appLE U ⊤ (hptU χ)) b) = χ b := by
    intro χ b
    have := congrArg (fun ν : Γ(G, U) →+* ℂ => ν b) (hpteval χ)
    simpa using this

  have hpt_unique : ∀ (q : Spec (CommRingCat.of ℂ) ⟶ G) (hq1 : q ≫ (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))) = 𝟙 _) (hqU : ⊤ ≤ q ⁻¹ᵁ U)
      (χ : Γ(G, U) →ₐ[ℂ] ℂ),
      (∀ b : Γ(G, U), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((q.appLE U ⊤ hqU) b) = χ b) → pt χ = q := by
    intro q hq1 hqU χ hqval
    refine KP.1 (pt χ) q (hpt1 χ) hq1 (hptU χ) hqU ?_
    apply CommRingCat.hom_ext
    ext b
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((pt χ).appLE U ⊤ (hptU χ)) b) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((q.appLE U ⊤ hqU) b)
    rw [hptval, hqval]

  set ψ : (Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ G) :=
    fun σ v => pt (Φ (Fin.cons (σ t) v)) with hψ

  have hballsub : Metric.ball (σ₁ t) ρ ⊆ Metric.ball (σ₀ t) r := by
    intro z hz
    have hm : (Fin.cons z v₀ : Fin (g + 1) → ℂ) ∈ Metric.ball (co χ₀) ρ := by
      rw [Metric.mem_ball, hw₀, dist_finCons_lt_iff _ _ _ _ hρ0]
      exact ⟨hz, Metric.mem_ball_self hρ0⟩
    have h1 := (hcomp _ hm).1
    have h2 := hbij.mapsTo h1
    have h3 : (Φ (Fin.cons z v₀)).comp φ t = z := by
      have := congrFun (hcoΦ _ (hρsub hm)) 0
      simp [hco, htt] at this
      exact this
    simpa [h3] using h2

  haveI : Nonempty (Sc →ₐ[ℂ] ℂ) := ⟨σ₀⟩
  set σbr : ℂ → (Sc →ₐ[ℂ] ℂ) := Function.invFunOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 with hσbr
  have hσbr_mem : ∀ z ∈ Metric.ball (σ₀ t) r, σbr z ∈ 𝒰 := fun z hz =>
    Function.invFunOn_mem (hbij.surjOn hz)
  have hσbr_t : ∀ z ∈ Metric.ball (σ₀ t) r, σbr z t = z := fun z hz =>
    Function.invFunOn_eq (f := fun σ : Sc →ₐ[ℂ] ℂ => σ t) (hbij.surjOn hz)
  have hσbr_eq : ∀ σ ∈ 𝒰, σbr (σ t) = σ := fun σ hσ =>
    hbij.injOn.leftInvOn_invFunOn (f := fun σ : Sc →ₐ[ℂ] ℂ => σ t) hσ
  set BE : Set (ℂ × (Fin g → ℂ)) :=
    {p | p.1 ∈ Metric.ball (σ₁ t) ρ ∧ p.2 ∈ Metric.ball v₀ ρ} with hBE
  have hBEopen : IsOpen BE :=
    (Metric.isOpen_ball.preimage continuous_fst).inter (Metric.isOpen_ball.preimage continuous_snd)
  let ψE : ℂ × (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))) :=
    fun p => ⟨ψ (σbr p.1) p.2, hpt1 _⟩
  have hψEU : ∀ p ∈ BE, ⊤ ≤ (ψE p).1 ⁻¹ᵁ U := fun p _ => hptU _
  have hANhyp : ∀ b : Γ(G, U), ∃ F : ℂ × (Fin g → ℂ) → ℂ, DifferentiableOn ℂ F BE ∧
      ∀ (p : ℂ × (Fin g → ℂ)) (hp : p ∈ BE),
        F p = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((ψE p).1).appLE U ⊤ (hψEU p hp)) b) := by
    intro b
    refine ⟨fun p => Fb b (Fin.cons p.1 p.2), ?_, ?_⟩
    · have hFb' : DifferentiableOn ℂ (Fb b) (Metric.ball (Fin.cons (σ₁ t) v₀) r₁) := by
        rw [← hw₀]; exact hFb b
      exact differentiableOn_comp_finCons hFb' hρr₁ hρ0
    · intro p hp
      have hz : p.1 ∈ Metric.ball (σ₀ t) r := hballsub hp.1
      have ht : σbr p.1 t = p.1 := hσbr_t _ hz
      have hm : (Fin.cons p.1 p.2 : Fin (g + 1) → ℂ) ∈ Metric.ball (co χ₀) ρ := by
        rw [Metric.mem_ball, hw₀, dist_finCons_lt_iff _ _ _ _ hρ0]; exact hp
      show Fb b (Fin.cons p.1 p.2) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (((pt (Φ (Fin.cons (σbr p.1 t) p.2))).appLE U ⊤ (hptU _)) b)
      rw [hptval, ht, hΦval b _ (hρsub hm)]
  have hAN := AlgebraicGeometry.IsAffineOpen.isOpen_and_exists_differentiableOn_appLE_of_forall_section
    (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))) U hUaff BE hBEopen ψE hψEU hANhyp
  have hseteq : ∀ V : G.Opens,
      {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ρ ∧ p.2 ∈ Metric.ball v₀ ρ ∧
        ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ σ p.2) ⁻¹ᵁ V} = {p | p ∈ BE ∧ ⊤ ≤ (ψE p).1 ⁻¹ᵁ V} := by
    intro V
    ext p
    constructor
    · rintro ⟨h1, h2, σ, hσ, hσt, hV⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      have hs : σbr p.1 = σ := by rw [← hσt, hσbr_eq σ hσ]
      show ⊤ ≤ (ψ (σbr p.1) p.2) ⁻¹ᵁ V
      rw [hs]; exact hV
    · rintro ⟨⟨h1, h2⟩, hV⟩
      exact ⟨h1, h2, σbr p.1, hσbr_mem _ (hballsub h1), hσbr_t _ (hballsub h1), hV⟩

  refine ⟨ρ, ρ, hρ0, hρ0, hballsub, U, hUaff, s, v₀, ψ, fun σ _ _ v _ => hptU _, hP₀U,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro σ hσ hz v hv
    refine comp_eq_specMap_of_eval f U _ (hptU _) (hpt1 _) σ (fun a => ?_)
    have h := AlgHom.congr_fun (hover σ hσ v hz hv) a
    rw [AlgHom.comp_apply, hφ] at h
    rw [hptval]
    exact h
  ·
    show pt (Φ (Fin.cons (σ₁ t) v₀)) = P₀
    rw [← hw₀, hΦco χ₀ hχ₀U]
    exact hpt_unique P₀ hP₀C hP₀U χ₀ (fun b => (hχ₀ b).symm)
  ·
    intro σ hσ hz v hv i
    show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (((pt (Φ (Fin.cons (σ t) v))).appLE U ⊤ (hptU _)) (s i)) = v i
    rw [hptval]
    exact hcoord σ v hz hv i
  ·
    intro V φV
    obtain ⟨hopenV, F, hF, hFval⟩ := hAN V φV
    rw [hseteq V]
    refine ⟨hopenV, F, hF, ?_⟩
    intro σ hσ hz v hv hV
    have hmem : ((σ t, v) : ℂ × (Fin g → ℂ)) ∈ BE := ⟨hz, hv⟩
    have e : (ψE (σ t, v)).1 = ψ σ v := by
      show ψ (σbr (σ t)) v = ψ σ v
      rw [hσbr_eq σ hσ]
    have hV' : ⊤ ≤ (ψE (σ t, v)).1 ⁻¹ᵁ V := by rw [e]; exact hV
    rw [hFval (σ t, v) hV' hmem]
    exact congrArg _ (appLE_apply_congr e V hV' hV φV)
  ·
    obtain ⟨fs₀, ε₀, hε₀, hfs₀⟩ := hopenB χ₀ hχ₀U
    refine ⟨fs₀ ∪ Finset.univ.image s, min ε₀ ρ, lt_min hε₀ hρ0, ?_⟩
    intro σ hσ hz P hP hclose
    obtain ⟨P, hPσ⟩ := P
    have hP1 : P ≫ (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))) = 𝟙 _ := by
      rw [← Category.assoc, hPσ, specMap_algHom_comp]
    let χP : Γ(G, U) →ₐ[ℂ] ℂ :=
      { toRingHom := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (P.appLE U ⊤ hP).hom
        commutes' := fun z => eval_algebraMap (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))) P hP1 U hP z }
    have hχPval : ∀ b : Γ(G, U),
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.appLE U ⊤ hP) b) = χP b := fun b => rfl
    have hχPSc : ∀ a : Sc, χP (algebraMap Sc Γ(G, U) a) = σ a := fun a =>
      eval_comp_algebraMap f σ.toRingHom P hPσ U hP a
    have hχPU : χP ∈ 𝒰B := by
      refine hfs₀ χP fun b hb => ?_
      have := hclose b (Finset.mem_union_left _ hb)
      rw [hχPval, ← hχ₀ b] at this
      exact this.trans_le (min_le_left _ _)
    set v : Fin g → ℂ := fun i => χP (s i) with hv
    have hvmem : v ∈ Metric.ball v₀ ρ := by
      rw [Metric.mem_ball, dist_pi_lt_iff hρ0]
      intro i
      have := hclose (s i) (Finset.mem_union_right _ (Finset.mem_image_of_mem s (Finset.mem_univ i)))
      rw [hχPval, ← hχ₀ (s i), ← dist_eq_norm] at this
      exact this.trans_le (min_le_right _ _)
    have hcoP : co χP = Fin.cons (σ t) v := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hco, htt, hχPSc]
      · simp [hco, htt, hv]
    refine ⟨v, hvmem, ?_⟩
    show pt (Φ (Fin.cons (σ t) v)) = P
    rw [← hcoP, hΦco χP hχPU]
    exact hpt_unique P hP1 hP χP hχPval

end S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_relChart_differentiableOn_appLE_of_analyticChart
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_relChart_differentiableOn_appLE_of_analyticChart (solution)
