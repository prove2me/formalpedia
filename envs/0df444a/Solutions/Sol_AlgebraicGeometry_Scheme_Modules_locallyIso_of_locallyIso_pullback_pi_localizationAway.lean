-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.locallyIso_of_locallyIso_pullback_pi_localizationAway
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4502a60e-8cb8-57fa-89ea-aed3dbba23f0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_locallyIso_of_locallyIso_pullback_pi_localizationAway

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f₁ : X₁ ⟶ Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i))))
    (c : X₁ ⟶ X) (hc : IsPullback c f₁ f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i))))))
    (L M : X.Modules)
    (h : ∀ s₁ : ↥(Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))),
      ∃ U₁ : (Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))).Opens, s₁ ∈ U₁ ∧
        Nonempty ((Scheme.Modules.pullback (f₁ ⁻¹ᵁ U₁).ι).obj ((Scheme.Modules.pullback c).obj L) ≅
          (Scheme.Modules.pullback (f₁ ⁻¹ᵁ U₁).ι).obj ((Scheme.Modules.pullback c).obj M))) :
    ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M) := by
  classical
  intro s

  obtain ⟨i, hi⟩ : ∃ i, r i ∉ s.asIdeal := by
    by_contra hall
    push Not at hall
    have hle : Ideal.span (Set.range r) ≤ s.asIdeal := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
    rw [hr, top_le_iff] at hle
    exact s.isPrime.ne_top hle

  let Sᵢ := Localization.Away (r i)
  let ℓ := Spec.map (CommRingCat.ofHom (algebraMap S Sᵢ))
  let j := Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i : Fin k => Localization.Away (r i)) i))
  let π := Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i))))
  have hjπ : j ≫ π = ℓ := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext fun x => rfl)
  haveI : IsOpenImmersion ℓ := inferInstance

  obtain ⟨s', hs'⟩ : s ∈ Set.range ℓ.base := by
    change s ∈ Set.range (PrimeSpectrum.comap (algebraMap S Sᵢ))
    rw [PrimeSpectrum.localization_away_comap_range Sᵢ (r i)]
    exact hi
  obtain ⟨U₁, hs₁, ⟨Φ⟩⟩ := h (j.base s')

  let W : (Spec (CommRingCat.of Sᵢ)).Opens := j ⁻¹ᵁ U₁
  let U : (Spec (CommRingCat.of S)).Opens := ℓ ''ᵁ W
  have hsU : s ∈ U := ⟨s', hs₁, hs'⟩
  refine ⟨U, hsU, ?_⟩

  have hrange : Set.range ((f ⁻¹ᵁ U).ι ≫ f).base ⊆ Set.range ℓ.base := by
    rintro _ ⟨x, rfl⟩
    have hx : f.base x.1 ∈ U := x.2
    obtain ⟨y, -, hy⟩ := hx
    refine ⟨y, ?_⟩
    show ℓ.base y = f.base ((f ⁻¹ᵁ U).ι.base x)
    exact hy

  let m := IsOpenImmersion.lift ℓ ((f ⁻¹ᵁ U).ι ≫ f) hrange
  have hm : m ≫ ℓ = (f ⁻¹ᵁ U).ι ≫ f := IsOpenImmersion.lift_fac _ _ _

  have w : (f ⁻¹ᵁ U).ι ≫ f = (m ≫ j) ≫ π := by rw [Category.assoc, hjπ, hm]
  let ρ₀ := hc.lift (f ⁻¹ᵁ U).ι (m ≫ j) w
  have hρ₀c : ρ₀ ≫ c = (f ⁻¹ᵁ U).ι := hc.lift_fst _ _ _
  have hρ₀f : ρ₀ ≫ f₁ = m ≫ j := hc.lift_snd _ _ _

  have hmem : ∀ x, ρ₀.base x ∈ f₁ ⁻¹ᵁ U₁ := by
    intro x
    show f₁.base (ρ₀.base x) ∈ U₁
    have e1 : (ρ₀ ≫ f₁).base x = (m ≫ j).base x := by rw [hρ₀f]
    change f₁.base (ρ₀.base x) = j.base (m.base x) at e1
    rw [e1]
    have h1 : ℓ.base (m.base x) ∈ ℓ ''ᵁ W := by
      have e2 : (m ≫ ℓ).base x = ((f ⁻¹ᵁ U).ι ≫ f).base x := by rw [hm]
      change ℓ.base (m.base x) = f.base ((f ⁻¹ᵁ U).ι.base x) at e2
      rw [e2]
      exact x.2
    have h2 : m.base x ∈ ℓ ⁻¹ᵁ (ℓ ''ᵁ W) := h1
    rw [Scheme.Hom.preimage_image_eq] at h2
    exact h2
  have hrange₁ : Set.range ρ₀.base ⊆ Set.range (f₁ ⁻¹ᵁ U₁).ι.base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨ρ₀.base x, hmem x⟩, rfl⟩
  let ρ := IsOpenImmersion.lift (f₁ ⁻¹ᵁ U₁).ι ρ₀ hrange₁
  have hρ : ρ ≫ (f₁ ⁻¹ᵁ U₁).ι = ρ₀ := IsOpenImmersion.lift_fac _ _ _
  have key : (f ⁻¹ᵁ U).ι = ρ ≫ (f₁ ⁻¹ᵁ U₁).ι ≫ c := by rw [← Category.assoc, hρ, hρ₀c]

  exact ⟨(Scheme.Modules.pullbackCongr key).app L ≪≫
    ((Scheme.Modules.pullbackComp ρ ((f₁ ⁻¹ᵁ U₁).ι ≫ c)).app L).symm ≪≫
    (Scheme.Modules.pullback ρ).mapIso (((Scheme.Modules.pullbackComp (f₁ ⁻¹ᵁ U₁).ι c).app L).symm ≪≫ Φ ≪≫
      (Scheme.Modules.pullbackComp (f₁ ⁻¹ᵁ U₁).ι c).app M) ≪≫
    (Scheme.Modules.pullbackComp ρ ((f₁ ⁻¹ᵁ U₁).ι ≫ c)).app M ≪≫
    (Scheme.Modules.pullbackCongr key.symm).app M⟩

end
end S_AlgebraicGeometry_Scheme_Modules_locallyIso_of_locallyIso_pullback_pi_localizationAway
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_locallyIso_of_locallyIso_pullback_pi_localizationAway (solution)
