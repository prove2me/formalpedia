-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3adcfd49-f34a-5d81-b73e-1a4d6e07a8fe

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology

theorem solution
    {X Y : Scheme.{0}} (g : X ⟶ Y) [IsClosedImmersion g]
    (π : (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ X)) (v₀ : Fin 2 → ℂ)

    (hcont : ∀ W : X.Opens, ⊤ ≤ (π v₀) ⁻¹ᵁ W → ∃ ε' : ℝ, 0 < ε' ∧ ∀ v ∈ Metric.ball v₀ ε', ⊤ ≤ (π v) ⁻¹ᵁ W)

    (U : X.Opens) (f₁ f₂ : Γ(X, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ)) (F : (Fin 2 → ℂ) → (Fin 2 → ℂ))
    (hε : 0 < ε) (hU : ∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (π v) ⁻¹ᵁ U)
    (hF : ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (π v) ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
      F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v).appLE U ⊤ h) f₁), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v).appLE U ⊤ h) f₂)])
    (hD : HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀) :
    ∃ (V : Y.Opens) (f₂' f₃' : Γ(Y, V)) (ε' : ℝ) (F' : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
      0 < ε' ∧
      (∀ v ∈ Metric.ball v₀ ε', ⊤ ≤ (π v ≫ g) ⁻¹ᵁ V) ∧
      (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ (π v ≫ g) ⁻¹ᵁ V), v ∈ Metric.ball v₀ ε' →
        F' v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v ≫ g).appLE V ⊤ h) f₂'), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π v ≫ g).appLE V ⊤ h) f₃')]) ∧
      HasFDerivAt F' (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀ := by
  classical

  let p₀ : ↥(Spec (CommRingCat.of ℂ)) := default
  have hp : ∀ p : ↥(Spec (CommRingCat.of ℂ)), p = p₀ := fun p => Subsingleton.elim _ _
  have hle_iff : ∀ (Z : Scheme.{0}) (q : Spec (CommRingCat.of ℂ) ⟶ Z) (W : Z.Opens),
      ⊤ ≤ q ⁻¹ᵁ W ↔ q.base p₀ ∈ W := by
    intro Z q W
    constructor
    · intro h; exact h (x := p₀) trivial
    · intro h p _; rw [hp p]; exact h
  set x₀ : ↥X := (π v₀).base p₀ with hx₀
  have hx₀U : x₀ ∈ U := (hle_iff X (π v₀) U).mp (hU v₀ (Metric.mem_ball_self hε))

  obtain ⟨W, hW, hgxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := g.base x₀) (U := ⊤) trivial
  have hWpre : IsAffineOpen (g ⁻¹ᵁ W) := hW.preimage g
  have hx₀W : x₀ ∈ g ⁻¹ᵁ W := hgxW
  obtain ⟨rbar, hrbar_le, hx₀r⟩ :=
    hWpre.exists_basicOpen_le (V := U ⊓ g ⁻¹ᵁ W) ⟨x₀, ⟨hx₀U, hx₀W⟩⟩ hx₀W

  have hsurj : ∀ (V : Y.Opens), IsAffineOpen V → Function.Surjective (g.app V) := by
    intro V hV
    haveI : IsAffine V := hV
    haveI : IsClosedImmersion (g ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsClosedImmersion g› V
    have h1 := (IsClosedImmersion.isAffine_surjective_of_isAffine (g ∣_ V)).2
    rw [Scheme.Hom.appTop, morphismRestrict_app'] at h1
    have e₁ : V.ι ''ᵁ ⊤ = V := V.ι_image_top
    have e₂ : (g ⁻¹ᵁ V).ι ''ᵁ ⊤ = g ⁻¹ᵁ V := (g ⁻¹ᵁ V).ι_image_top
    have h2 := (Scheme.Hom.appLE_congr g _ e₁ e₂ (fun φ => Function.Surjective φ)).mp h1
    rwa [Scheme.Hom.appLE_eq_app] at h2
  obtain ⟨r, hr⟩ := hsurj W hW rbar

  have hVpre : g ⁻¹ᵁ Y.basicOpen r = X.basicOpen rbar := by
    rw [Scheme.preimage_basicOpen, hr]
  have hVU : g ⁻¹ᵁ Y.basicOpen r ≤ U := hVpre.le.trans (hrbar_le.trans inf_le_left)
  have hx₀V : x₀ ∈ g ⁻¹ᵁ Y.basicOpen r := by rw [hVpre]; exact hx₀r
  obtain ⟨f₂', hf₂'⟩ := hsurj (Y.basicOpen r) (hW.basicOpen r) (X.presheaf.map (homOfLE hVU).op f₁)
  obtain ⟨f₃', hf₃'⟩ := hsurj (Y.basicOpen r) (hW.basicOpen r) (X.presheaf.map (homOfLE hVU).op f₂)

  obtain ⟨ε₁, hε₁, hball⟩ := hcont (g ⁻¹ᵁ Y.basicOpen r) ((hle_iff X (π v₀) _).mpr hx₀V)
  refine ⟨Y.basicOpen r, f₂', f₃', min ε ε₁, F, lt_min hε hε₁, ?_, ?_, hD⟩
  · intro v hv
    have hv₁ : v ∈ Metric.ball v₀ ε₁ := Metric.ball_subset_ball (min_le_right _ _) hv
    exact hball v hv₁
  · intro v h hv
    have hvε : v ∈ Metric.ball v₀ ε := Metric.ball_subset_ball (min_le_left _ _) hv
    have hU' : ⊤ ≤ (π v) ⁻¹ᵁ U := hU v hvε
    rw [hF v hU' hvε]
    have key : ∀ (fj : Γ(X, U)) (fj' : Γ(Y, Y.basicOpen r)),
        g.app (Y.basicOpen r) fj' = X.presheaf.map (homOfLE hVU).op fj →
        ((π v ≫ g).appLE (Y.basicOpen r) ⊤ h) fj' = ((π v).appLE U ⊤ hU') fj := by
      intro fj fj' hfj
      rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, hfj, ← CommRingCat.comp_apply,
        Scheme.Hom.map_appLE]
    rw [key f₁ f₂' hf₂', key f₂ f₃' hf₃']

end S_AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_hasFDerivAt_appLE_comp_of_hasFDerivAt_appLE (solution)
