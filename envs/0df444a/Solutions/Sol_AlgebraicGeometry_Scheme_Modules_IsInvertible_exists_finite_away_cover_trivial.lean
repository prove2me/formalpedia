-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_finite_away_cover_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/04352c4e-860a-583d-9e00-c33344e2bf28

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_piEvalRingHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_finite_away_cover_trivial
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace BenchQED0

variable {S : Type u} [CommRing S]

theorem exists_away_trivial (N : (Spec (CommRingCat.of S)).Modules) (hN : Scheme.Modules.IsInvertible N)
    (x : Spec (CommRingCat.of S)) :
    ∃ r : S, x ∈ PrimeSpectrum.basicOpen r ∧
      Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).obj N ≅
        SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf) := by
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hN.exists_trivialization x
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
  refine ⟨r, hxr, ⟨?_⟩⟩
  let ι := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))
  have hrange : Set.range ι.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    intro y hy
    apply hrU
    have : Set.range ι.base = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S)) := by
      erw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    rw [this] at hy
    exact hy
  let g := IsOpenImmersion.lift U.ι ι hrange
  have hg : g ≫ U.ι = ι := IsOpenImmersion.lift_fac _ _ _
  exact (Scheme.Modules.pullbackCongr hg.symm).app N ≪≫ ((Scheme.Modules.pullbackComp g U.ι).app N).symm ≪≫
    (Scheme.Modules.pullback g).mapIso eU ≪≫ Scheme.Modules.pullbackUnitIso g

theorem faithfullyFlat_pi_away {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤) :
    Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i)) := by
  classical
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨inferInstance, fun I hI => ?_⟩

  have hpow : ∀ i, ∃ n : ℕ, r i ^ n ∈ I := by
    intro i
    have h1 : (1 : ∀ j : Fin k, Localization.Away (r j)) ∈ I • (⊤ : Submodule S (∀ j : Fin k, Localization.Away (r j))) := by
      rw [hI]; trivial

    have hmap : (1 : Localization.Away (r i)) ∈ I.map (algebraMap S (Localization.Away (r i))) := by
      have key : ∀ z ∈ I • (⊤ : Submodule S (∀ j : Fin k, Localization.Away (r j))),
          z i ∈ I.map (algebraMap S (Localization.Away (r i))) := by
        intro z hz
        refine Submodule.smul_induction_on hz ?_ ?_
        · intro a ha m _
          rw [Pi.smul_apply, Algebra.smul_def]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
        · intro z w hz hw
          rw [Pi.add_apply]; exact Ideal.add_mem _ hz hw
      simpa using key 1 h1
    obtain ⟨⟨a, m⟩, ham⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (r i)) _).mp hmap

    obtain ⟨p, hp⟩ := (Submonoid.mem_powers_iff _ _).mp m.2
    rw [one_mul] at ham
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (r i)) _).mp ham
    obtain ⟨q, hq⟩ := (Submonoid.mem_powers_iff _ _).mp hc
    refine ⟨q + p, ?_⟩
    have : c * (m : S) = c * a := hc'
    rw [pow_add, hq, hp, this]
    exact I.mul_mem_left _ a.2
  choose n hn using hpow

  have htop : Ideal.span ((fun x => x ^ (Finset.univ.sup n)) '' Set.range r) = ⊤ :=
    Ideal.span_pow_eq_top _ hr _
  rw [eq_top_iff, ← htop]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  have hle : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  show r i ^ (Finset.univ.sup n) ∈ I
  rw [hd, pow_add]
  exact I.mul_mem_right _ (hn i)

theorem main (N : (Spec (CommRingCat.of S)).Modules) (hN : Scheme.Modules.IsInvertible N) :
    ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧
      (∀ i, Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))).obj N ≅
        SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away (r i)))).ringCatSheaf)) ∧
      Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i)) ∧
      Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i)))))).obj N ≅
        SheafOfModules.unit (Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))).ringCatSheaf) := by
  classical
  choose r hr htriv using fun x => exists_away_trivial N hN x
  have hcover : (Set.univ : Set (Spec (CommRingCat.of S))) ⊆ ⋃ x, (PrimeSpectrum.basicOpen (r x) : Set (PrimeSpectrum S)) :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hr x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (PrimeSpectrum.basicOpen (r x) : Set (PrimeSpectrum S))) (fun x => (PrimeSpectrum.basicOpen (r x)).isOpen) hcover
  let e : Fin t.card ≃ t := t.equivFin.symm
  let r' : Fin t.card → S := fun i => r (e i).1
  have hspan : Ideal.span (Set.range r') = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, eq_top_iff]
    intro x _
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ (PrimeSpectrum.basicOpen (r y) : Set (PrimeSpectrum S)) := by
      simpa [Set.mem_iUnion] using ht (Set.mem_univ x)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e.symm ⟨y, hy⟩, ?_⟩
    show x ∈ PrimeSpectrum.basicOpen (r (e (e.symm ⟨y, hy⟩)).1)
    rw [Equiv.apply_symm_apply]
    exact hxy
  refine ⟨t.card, r', hspan, fun i => htriv _, faithfullyFlat_pi_away r' hspan, ?_⟩

  let A : Fin t.card → Type u := fun i => Localization.Away (r' i)
  let ιT := Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin t.card, A i)))
  refine AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_piEvalRingHom A
    ((Scheme.Modules.pullback ιT).obj N) (fun i => ?_)
  obtain ⟨ei⟩ := htriv (e i).1
  have hcomp : Spec.map (CommRingCat.ofHom (Pi.evalRingHom A i)) ≫ ιT =
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r' i)))) := by
    rw [← Spec.map_comp]
    congr 1
  exact ⟨(Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr hcomp).app N ≪≫ ei⟩

end BenchQED0

theorem solution
    {S : Type u} [CommRing S] (N : (Spec (CommRingCat.of S)).Modules) (hN : Scheme.Modules.IsInvertible N) :
    ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧
      (∀ i, Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))).obj N ≅
        SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away (r i)))).ringCatSheaf)) ∧
      Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i)) ∧

      Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i)))))).obj N ≅
        SheafOfModules.unit (Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))).ringCatSheaf) :=
  BenchQED0.main N hN

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_finite_away_cover_trivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_finite_away_cover_trivial (solution)
