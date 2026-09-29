-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/300be889-99db-5194-b3ed-a110a267b204

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_over_of_forall_schemeHomOver

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace G2AffYonedaHom

noncomputable def specHom {A B : CommRingCat.{u}} (g : Spec A ⟶ Spec B) : (B : Type u) →+* (A : Type u) :=
  (Spec.preimage g).hom

theorem specMap_specHom {A B : CommRingCat.{u}} (g : Spec A ⟶ Spec B) :
    Spec.map (CommRingCat.ofHom (specHom g)) = g := by
  rw [specHom, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem ringHom_eq_of_specMap_eq {A B : Type u} [CommRing A] [CommRing B] {φ ψ : A →+* B}
    (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

variable {R : Type u} [CommRing R] {Z₁ Z₂ : Scheme.{u}}
  (ζ₁ : Z₁ ⟶ Spec (CommRingCat.of R)) (ζ₂ : Z₂ ⟶ Spec (CommRingCat.of R))
  (e : ∀ (T : Type u) [CommRing T] (φ : R →+* T),
    SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁ → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₂)

def E (T : Type u) [CommRing T] (φ : R →+* T) (a : Spec (CommRingCat.of T) ⟶ Z₁)
    (ha : a ≫ ζ₁ = Spec.map (CommRingCat.ofHom φ)) : Spec (CommRingCat.of T) ⟶ Z₂ :=
  (e T φ ⟨a, ha⟩).1

theorem E_comp (T : Type u) [CommRing T] (φ : R →+* T) (a : Spec (CommRingCat.of T) ⟶ Z₁)
    (ha : a ≫ ζ₁ = Spec.map (CommRingCat.ofHom φ)) : E ζ₁ ζ₂ e T φ a ha ≫ ζ₂ = Spec.map (CommRingCat.ofHom φ) :=
  (e T φ ⟨a, ha⟩).2

theorem E_congr (T : Type u) [CommRing T] {φ φ' : R →+* T} (h : φ = φ') {a a' : Spec (CommRingCat.of T) ⟶ Z₁}
    (haa : a = a') (ha : a ≫ ζ₁ = Spec.map (CommRingCat.ofHom φ)) (ha' : a' ≫ ζ₁ = Spec.map (CommRingCat.ofHom φ')) :
    E ζ₁ ζ₂ e T φ a ha = E ζ₁ ζ₂ e T φ' a' ha' := by
  subst h haa; rfl

variable (he : ∀ (T T' : Type u) [CommRing T] [CommRing T'] (φ : R →+* T) (ψ : T →+* T')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
      (e T' (ψ.comp φ) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by
          rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩).1 =
        Spec.map (CommRingCat.ofHom ψ) ≫ (e T φ x).1)

include he in
theorem E_natural (T T' : Type u) [CommRing T] [CommRing T'] (φ : R →+* T) (ψ : T →+* T')
    (a : Spec (CommRingCat.of T) ⟶ Z₁) (ha : a ≫ ζ₁ = Spec.map (CommRingCat.ofHom φ)) :
    Spec.map (CommRingCat.ofHom ψ) ≫ E ζ₁ ζ₂ e T φ a ha =
      E ζ₁ ζ₂ e T' (ψ.comp φ) (Spec.map (CommRingCat.ofHom ψ) ≫ a)
        (by rw [Category.assoc, ha, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :=
  (he T T' φ ψ ⟨a, ha⟩).symm

theorem E_eq_of_eq (T : Type u) [CommRing T] (φ φ' : R →+* T) (a a' : Spec (CommRingCat.of T) ⟶ Z₁)
    (ha : a ≫ ζ₁ = Spec.map (CommRingCat.ofHom φ)) (ha' : a' ≫ ζ₁ = Spec.map (CommRingCat.ofHom φ'))
    (haa : a = a') : E ζ₁ ζ₂ e T φ a ha = E ζ₁ ζ₂ e T φ' a' ha' := by
  have hφ : φ = φ' := ringHom_eq_of_specMap_eq (by rw [← ha, ← ha', haa])
  exact E_congr ζ₁ ζ₂ e T hφ haa ha ha'

noncomputable def chart (j : Z₁.affineOpenCover.I₀) :
    Spec (CommRingCat.of (Z₁.affineOpenCover.X j : Type u)) ⟶ Z₁ :=
  Z₁.affineOpenCover.f j

noncomputable def chartHom (j : Z₁.affineOpenCover.I₀) : R →+* (Z₁.affineOpenCover.X j : Type u) :=
  specHom (chart (Z₁ := Z₁) j ≫ ζ₁)

theorem chart_comp (j : Z₁.affineOpenCover.I₀) :
    chart (Z₁ := Z₁) j ≫ ζ₁ = Spec.map (CommRingCat.ofHom (chartHom ζ₁ j)) := by
  rw [chartHom, specMap_specHom]

noncomputable def piece (j : Z₁.affineOpenCover.I₀) : Spec (CommRingCat.of (Z₁.affineOpenCover.X j : Type u)) ⟶ Z₂ :=
  E ζ₁ ζ₂ e _ (chartHom ζ₁ j) (chart j) (chart_comp ζ₁ j)

include he in

theorem comp_E {B : CommRingCat.{u}} (T : Type u) [CommRing T] (φ : R →+* T)
    (a : Spec (CommRingCat.of T) ⟶ Z₁) (ha : a ≫ ζ₁ = Spec.map (CommRingCat.ofHom φ))
    (g : Spec B ⟶ Spec (CommRingCat.of T)) :
    g ≫ E ζ₁ ζ₂ e T φ a ha =
      E ζ₁ ζ₂ e (B : Type u) ((specHom g).comp φ) (g ≫ a)
        (by rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_specHom, Category.assoc, ha]) := by
  have h := E_natural ζ₁ ζ₂ e he T (B : Type u) φ (specHom g) a ha
  calc g ≫ E ζ₁ ζ₂ e T φ a ha = Spec.map (CommRingCat.ofHom (specHom g)) ≫ E ζ₁ ζ₂ e T φ a ha := by
        rw [specMap_specHom]
    _ = _ := h
    _ = _ := E_congr ζ₁ ζ₂ e _ rfl (by rw [specMap_specHom]) _ _

include he in

set_option backward.isDefEq.respectTransparency false in
theorem piece_compat (i j : Z₁.affineOpenCover.I₀) :
    pullback.fst (chart (Z₁ := Z₁) i) (chart j) ≫ piece ζ₁ ζ₂ e i =
      pullback.snd (chart (Z₁ := Z₁) i) (chart j) ≫ piece ζ₁ ζ₂ e j := by
  refine (pullback (chart (Z₁ := Z₁) i) (chart j)).affineOpenCover.openCover.hom_ext _ _ fun k => ?_
  rw [← Category.assoc, ← Category.assoc, piece, piece, comp_E ζ₁ ζ₂ e he, comp_E ζ₁ ζ₂ e he]
  exact E_eq_of_eq ζ₁ ζ₂ e _ _ _ _ _ _ _ (by rw [Category.assoc, Category.assoc, pullback.condition])

include he in

noncomputable def glue : Z₁ ⟶ Z₂ :=
  Z₁.affineCover.glueMorphisms (fun j => piece ζ₁ ζ₂ e j) (fun i j => piece_compat ζ₁ ζ₂ e he i j)

include he in
theorem chart_glue (j : Z₁.affineOpenCover.I₀) : chart j ≫ glue ζ₁ ζ₂ e he = piece ζ₁ ζ₂ e j :=
  Z₁.affineCover.ι_glueMorphisms _ _ j

include he in

theorem comp_glue (T : Type u) [CommRing T] (φ : R →+* T) (a : Spec (CommRingCat.of T) ⟶ Z₁)
    (ha : a ≫ ζ₁ = Spec.map (CommRingCat.ofHom φ)) :
    a ≫ glue ζ₁ ζ₂ e he = E ζ₁ ζ₂ e T φ a ha := by
  refine Scheme.Cover.hom_ext (Z₁.affineCover.pullback₁ a) _ _ fun j => ?_
  refine (pullback a (Z₁.affineCover.f j)).affineOpenCover.openCover.hom_ext _ _ fun k => ?_
  try dsimp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
    PreZeroHypercover.pullback₁_f]
  let g₁ : Spec ((pullback a (Z₁.affineCover.f j)).affineOpenCover.X k) ⟶ Spec (CommRingCat.of T) :=
    (pullback a (Z₁.affineCover.f j)).affineOpenCover.f k ≫ pullback.fst a (Z₁.affineCover.f j)
  let g₂ : Spec ((pullback a (Z₁.affineCover.f j)).affineOpenCover.X k) ⟶
      Spec (CommRingCat.of (Z₁.affineOpenCover.X j : Type u)) :=
    (pullback a (Z₁.affineCover.f j)).affineOpenCover.f k ≫ pullback.snd a (Z₁.affineCover.f j)
  have hg : g₁ ≫ a = g₂ ≫ chart j := by
    show ((pullback a (Z₁.affineCover.f j)).affineOpenCover.f k ≫ pullback.fst a (Z₁.affineCover.f j)) ≫ a =
      ((pullback a (Z₁.affineCover.f j)).affineOpenCover.f k ≫ pullback.snd a (Z₁.affineCover.f j)) ≫ Z₁.affineCover.f j
    rw [Category.assoc, Category.assoc, pullback.condition]
  have h1 := comp_E ζ₁ ζ₂ e he T φ a ha g₁
  have h2 : g₂ ≫ piece ζ₁ ζ₂ e j = _ := comp_E ζ₁ ζ₂ e he _ (chartHom ζ₁ j) (chart j) (chart_comp ζ₁ j) g₂
  calc (pullback a (Z₁.affineCover.f j)).affineOpenCover.f k ≫ pullback.fst a (Z₁.affineCover.f j) ≫ a ≫ glue ζ₁ ζ₂ e he
      = g₁ ≫ a ≫ glue ζ₁ ζ₂ e he := by simp only [g₁, Category.assoc]
    _ = g₂ ≫ chart j ≫ glue ζ₁ ζ₂ e he := by rw [← Category.assoc, hg, Category.assoc]
    _ = g₂ ≫ piece ζ₁ ζ₂ e j := by rw [chart_glue ζ₁ ζ₂ e he]
    _ = _ := h2
    _ = _ := E_eq_of_eq ζ₁ ζ₂ e _ _ _ _ _ _ _ hg.symm
    _ = g₁ ≫ E ζ₁ ζ₂ e T φ a ha := h1.symm
    _ = _ := by simp only [g₁, Category.assoc]; rfl

include he in
theorem glue_comp : glue ζ₁ ζ₂ e he ≫ ζ₂ = ζ₁ := by
  refine Z₁.affineCover.hom_ext _ _ fun j => ?_
  show chart j ≫ glue ζ₁ ζ₂ e he ≫ ζ₂ = chart j ≫ ζ₁
  rw [← Category.assoc, chart_glue ζ₁ ζ₂ e he, piece, E_comp, chart_comp]

end G2AffYonedaHom

open G2AffYonedaHom in
theorem solution
    {R : Type u} [CommRing R] {Z₁ Z₂ : Scheme.{u}}
    (ζ₁ : Z₁ ⟶ Spec (CommRingCat.of R)) (ζ₂ : Z₂ ⟶ Spec (CommRingCat.of R))
    (e : ∀ (T : Type u) [CommRing T] (φ : R →+* T),
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁ → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₂)
    (he : ∀ (T T' : Type u) [CommRing T] [CommRing T'] (φ : R →+* T) (ψ : T →+* T')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
      (e T' (ψ.comp φ) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by
          rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩).1 =
        Spec.map (CommRingCat.ofHom ψ) ≫ (e T φ x).1) :
    ∃ ε : Z₁ ⟶ Z₂, ε ≫ ζ₂ = ζ₁ ∧
      (∀ (T : Type u) [CommRing T] (φ : R →+* T) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
        x.1 ≫ ε = (e T φ x).1) ∧
      ∀ ε' : Z₁ ⟶ Z₂, (∀ (T : Type u) [CommRing T] (φ : R →+* T) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
        x.1 ≫ ε' = (e T φ x).1) → ε' = ε := by
  classical
  have h12 : ∀ (T : Type u) [CommRing T] (φ : R →+* T) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
      x.1 ≫ glue ζ₁ ζ₂ e he = (e T φ x).1 := fun T _ φ x => comp_glue ζ₁ ζ₂ e he T φ x.1 x.2
  refine ⟨glue ζ₁ ζ₂ e he, glue_comp ζ₁ ζ₂ e he, h12, fun ε' hε' => ?_⟩
  refine Z₁.affineCover.hom_ext _ _ fun j => ?_
  show chart j ≫ ε' = chart j ≫ glue ζ₁ ζ₂ e he
  rw [hε' _ (chartHom ζ₁ j) ⟨chart j, chart_comp ζ₁ j⟩, h12 _ (chartHom ζ₁ j) ⟨chart j, chart_comp ζ₁ j⟩]

end S_AlgebraicGeometry_Scheme_existsUnique_hom_over_of_forall_schemeHomOver
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_over_of_forall_schemeHomOver (solution)
