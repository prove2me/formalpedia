-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_hom_comp_eq_isPullback_of_comp_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b5c73494-b5d1-54c5-bdb3-f4243f895910

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_hom_comp_eq_isPullback_of_comp_of_locally

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

namespace G2BCCompareLocal

theorem mul_val_congr' {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T₀ : Scheme.{u}} {t₁ t₂ : T₀ ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst h; cases Subtype.ext hx; cases Subtype.ext hy; rfl

end G2BCCompareLocal

open G2BCCompareLocal in
theorem solution
    {g d n : ℕ} {S C C' : Type u} [CommRing S] [CommRing C] [CommRing C'] (ρ : S →+* C) (σ : C →+* C')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n C) (v' : PolarisedAbelianScheme g d n C')
    (gv : v.A ⟶ u.A) (hgv : CategoryTheory.IsPullback gv v.f u.f (Spec.map (CommRingCat.ofHom ρ)))
    (hgvmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C)) (x y : SchemeHomOver t' v.f),
      (v.L.mul t' x y).1 ≫ gv =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ρ))
          ⟨x.1 ≫ gv, by rw [Category.assoc, hgv.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gv, by rw [Category.assoc, hgv.w, ← Category.assoc, y.2]⟩).1)
    (hgvP : ∀ i, (v.P i).1 ≫ gv = Spec.map (CommRingCat.ofHom ρ) ≫ (u.P i).1)
    (hgvpol : Nonempty ((Scheme.Modules.pullback gv).obj u.pol ≅ v.pol))
    (gv' : v'.A ⟶ u.A) (hgv' : CategoryTheory.IsPullback gv' v'.f u.f (Spec.map (CommRingCat.ofHom (σ.comp ρ))))
    (hgv'mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C')) (x y : SchemeHomOver t' v'.f),
      (v'.L.mul t' x y).1 ≫ gv' =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (σ.comp ρ)))
          ⟨x.1 ≫ gv', by rw [Category.assoc, hgv'.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gv', by rw [Category.assoc, hgv'.w, ← Category.assoc, y.2]⟩).1)
    (hgv'P : ∀ i, (v'.P i).1 ≫ gv' = Spec.map (CommRingCat.ofHom (σ.comp ρ)) ≫ (u.P i).1)
    (hgv'pol : ∀ s : ↥(Spec (CommRingCat.of C')), ∃ U : (Spec (CommRingCat.of C')).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (v'.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback gv').obj u.pol) ≅
        (Scheme.Modules.pullback (v'.f ⁻¹ᵁ U).ι).obj v'.pol)) :
    ∃ (c : v'.A ⟶ v.A) (_ : c ≫ gv = gv') (hc : CategoryTheory.IsPullback c v'.f v.f (Spec.map (CommRingCat.ofHom σ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C')) (x y : SchemeHomOver t' v'.f),
        (v'.L.mul t' x y).1 ≫ c =
          (v.L.mul (t' ≫ Spec.map (CommRingCat.ofHom σ))
            ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ i, (v'.P i).1 ≫ c = Spec.map (CommRingCat.ofHom σ) ≫ (v.P i).1) ∧
      (∀ s : ↥(Spec (CommRingCat.of C')), ∃ U : (Spec (CommRingCat.of C')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (v'.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback c).obj v.pol) ≅
          (Scheme.Modules.pullback (v'.f ⁻¹ᵁ U).ι).obj v'.pol)) := by
  have hbase : Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom ρ) = Spec.map (CommRingCat.ofHom (σ.comp ρ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hw : gv' ≫ u.f = (v'.f ≫ Spec.map (CommRingCat.ofHom σ)) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [hgv'.w, Category.assoc, hbase]
  let c : v'.A ⟶ v.A := hgv.lift gv' (v'.f ≫ Spec.map (CommRingCat.ofHom σ)) hw
  have hc₁ : c ≫ gv = gv' := hgv.lift_fst _ _ _
  have hc₂ : c ≫ v.f = v'.f ≫ Spec.map (CommRingCat.ofHom σ) := hgv.lift_snd _ _ _

  have hc : IsPullback c v'.f v.f (Spec.map (CommRingCat.ofHom σ)) := by
    refine IsPullback.of_right ?_ hc₂ hgv
    rw [hc₁, hbase]
    exact hgv'
  refine ⟨c, hc₁, hc, ?_, ?_, ?_⟩
  ·
    intro T t' x y
    apply hgv.hom_ext
    · rw [Category.assoc, hc₁, hgv'mul, hgvmul]
      exact mul_val_congr' u.L (by rw [Category.assoc, hbase]) _ _ _ _
        (by simp only [Category.assoc, hc₁]) (by simp only [Category.assoc, hc₁])
    · have l1 : ((v'.L.mul t' x y).1 ≫ c) ≫ v.f = t' ≫ Spec.map (CommRingCat.ofHom σ) := by
        rw [Category.assoc, hc₂, ← Category.assoc, (v'.L.mul t' x y).2]
      exact l1.trans (v.L.mul _ _ _).2.symm
  ·
    intro i
    apply hgv.hom_ext
    · rw [Category.assoc, hc₁, hgv'P, Category.assoc, hgvP, ← Category.assoc, hbase]
    · rw [Category.assoc, hc₂, ← Category.assoc, (v'.P i).2, Category.id_comp, Category.assoc, (v.P i).2,
        Category.comp_id]
  ·
    intro s
    obtain ⟨U, hs, ⟨i⟩⟩ := hgv'pol s
    let j : (Scheme.Modules.pullback c).obj v.pol ≅ (Scheme.Modules.pullback gv').obj u.pol :=
      ((Scheme.Modules.pullback c).mapIso hgvpol.some).symm ≪≫ (Scheme.Modules.pullbackComp c gv).app u.pol ≪≫
        (Scheme.Modules.pullbackCongr hc₁).app u.pol
    exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso j ≪≫ i⟩⟩

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_hom_comp_eq_isPullback_of_comp_of_locally
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_hom_comp_eq_isPullback_of_comp_of_locally (solution)
