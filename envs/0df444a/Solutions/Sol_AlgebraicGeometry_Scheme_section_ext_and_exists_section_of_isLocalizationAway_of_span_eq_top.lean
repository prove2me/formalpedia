-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d19dc735-169e-546f-b41a-0d081f681137

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (n : ℕ) (c : Fin n → S) (hc : Ideal.span (Set.range c) = ⊤)
    (L : Fin n → Type u) [∀ i, CommRing (L i)] [∀ i, Algebra S (L i)] [∀ i, IsLocalization.Away (c i) (L i)]
    (L₂ : Fin n → Fin n → Type u) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra S (L₂ i j)]
    [∀ i j, IsLocalization.Away (c i * c j) (L₂ i j)]
    (l : ∀ i j, L i →+* L₂ i j) (r : ∀ i j, L j →+* L₂ i j)
    (hl : ∀ i j, (l i j).comp (algebraMap S (L i)) = algebraMap S (L₂ i j))
    (hr : ∀ i j, (r i j).comp (algebraMap S (L j)) = algebraMap S (L₂ i j)) :
    (∀ s s' : Spec (CommRingCat.of S) ⟶ A, s ≫ f = 𝟙 _ → s' ≫ f = 𝟙 _ →
        (∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (L i))) ≫ s =
          Spec.map (CommRingCat.ofHom (algebraMap S (L i))) ≫ s') → s = s') ∧
    (∀ s : ∀ i, Spec (CommRingCat.of (L i)) ⟶ A,
        (∀ i, s i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (L i)))) →
        (∀ i j, Spec.map (CommRingCat.ofHom (l i j)) ≫ s i = Spec.map (CommRingCat.ofHom (r i j)) ≫ s j) →
        ∃ sec : Spec (CommRingCat.of S) ⟶ A, sec ≫ f = 𝟙 _ ∧
          ∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (L i))) ≫ sec = s i) := by
  classical

  haveI hoi : ∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (L i)))) :=
    fun i => IsOpenImmersion.of_isLocalization (c i)
  have hrange : ∀ i, Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (L i)))) =
      ((PrimeSpectrum.basicOpen (c i) : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) :=
    fun i => PrimeSpectrum.localization_away_comap_range (L i) (c i)
  have hcov : ∀ x : ↥(Spec (CommRingCat.of S)), ∃ (i : Fin n) (y : ↥(Spec (CommRingCat.of (L i)))),
      Spec.map (CommRingCat.ofHom (algebraMap S (L i))) y = x := by
    intro x
    have : ∃ i, c i ∉ x.asIdeal := by
      by_contra! h; apply x.2.ne_top; rwa [← top_le_iff, ← hc, Ideal.span_le, Set.range_subset_iff]
    obtain ⟨i, hi⟩ := this
    have hx : (x : PrimeSpectrum S) ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (L i)))) := by
      rw [hrange i]; exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, hy⟩
  let 𝒰 : (Spec (CommRingCat.of S)).OpenCover :=
    Scheme.Cover.mkOfCovers (Fin n) (fun i => Spec (CommRingCat.of (L i)))
      (fun i => Spec.map (CommRingCat.ofHom (algebraMap S (L i)))) hcov
  refine ⟨fun s s' _ _ h => Scheme.Cover.hom_ext 𝒰 s s' (fun i => h i), ?_⟩
  intro s hs hcompat

  have hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ s i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ s j := by
    intro i j
    have hli : Spec.map (CommRingCat.ofHom (l i j)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (L i))) =
        Spec.map (CommRingCat.ofHom (algebraMap S (L₂ i j))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl]
    have hrj : Spec.map (CommRingCat.ofHom (r i j)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (L j))) =
        Spec.map (CommRingCat.ofHom (algebraMap S (L₂ i j))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
    let u : Spec (CommRingCat.of (L₂ i j)) ⟶ pullback (𝒰.f i) (𝒰.f j) :=
      pullback.lift (Spec.map (CommRingCat.ofHom (l i j))) (Spec.map (CommRingCat.ofHom (r i j)))
        (by show _ ≫ Spec.map _ = _ ≫ Spec.map _; rw [hli, hrj])
    haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (L₂ i j)))) := IsOpenImmersion.of_isLocalization (c i * c j)
    haveI : IsOpenImmersion (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) := inferInstance
    have hrg : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (L₂ i j)))) =
        Set.range (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) := by
      rw [Scheme.Pullback.range_fst_comp]
      show Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (L₂ i j)))) =
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (L i)))) ∩ Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (L j))))
      rw [hrange i, hrange j]
      exact (PrimeSpectrum.localization_away_comap_range (L₂ i j) (c i * c j)).trans
        (by rw [PrimeSpectrum.basicOpen_mul]; rfl)
    have hu : u = (IsOpenImmersion.isoOfRangeEq _ _ hrg).hom := by
      apply IsOpenImmersion.lift_uniq
      show u ≫ (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) = Spec.map (CommRingCat.ofHom (algebraMap S (L₂ i j)))
      rw [← Category.assoc, pullback.lift_fst]; exact hli
    haveI : IsIso u := by rw [hu]; infer_instance
    rw [← cancel_epi u, ← Category.assoc, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    exact hcompat i j
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 s hf, ?_, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 s hf i⟩
  apply Scheme.Cover.hom_ext 𝒰
  intro i
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, Category.comp_id]
  exact hs i

end S_AlgebraicGeometry_Scheme_section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_section_ext_and_exists_section_of_isLocalizationAway_of_span_eq_top (solution)
