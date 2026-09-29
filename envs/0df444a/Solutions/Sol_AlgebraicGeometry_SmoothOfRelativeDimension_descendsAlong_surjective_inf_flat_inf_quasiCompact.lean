-- Prove2me | solution 1 for AlgebraicGeometry.SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/cc370dab-960d-55e6-8112-e71168ebff2c

import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Localization.BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "TensorProduct CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty"

namespace RingHom
p2m_export "RingHom" "Smooth.codescendsAlong_faithfullyFlat locally_of_locally Smooth CodescendsAlong.algebraMap_tensorProduct IsStandardSmoothOfRelativeDimension Etale Flat ext CodescendsAlong smooth_iff_locally_isStandardSmooth isStandardSmoothOfRelativeDimension_algebraMap isStandardSmoothOfRelativeDimension_respectsIso faithfullyFlat_algebraMap_iff locally_of_exists IsStableUnderBaseChange FaithfullyFlat mk CodescendsAlong.mk IsStandardSmoothOfRelativeDimension.isStandardSmooth id smooth_algebraMap locally_stableUnderCompositionWithLocalizationAwayTarget comp locally_respectsIso Locally isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway IsStandardSmooth toAlgebra"
p2m_open "RingHom"

theorem dsrd_exists_mem_not_isNilpotent {A : Type u} [CommRing A] [Nontrivial A] {s : Set A}
    (hs : Ideal.span s = ⊤) : ∃ h ∈ s, ¬ IsNilpotent h := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hle : Ideal.span s ≤ nilradical A := by
    rw [Ideal.span_le]
    intro x hx
    exact mem_nilradical.mpr (hall x hx)
  rw [hs, top_le_iff] at hle
  have h1 : IsNilpotent (1 : A) := mem_nilradical.mp (hle ▸ Submodule.mem_top)
  obtain ⟨k, hk⟩ := h1
  exact one_ne_zero ((one_pow k).symm.trans hk)

theorem dsrd_nontrivial_localizationAway {A : Type u} [CommRing A] {h : A} (hh : ¬ IsNilpotent h) :
    Nontrivial (Localization.Away h) := by
  rw [← not_subsingleton_iff_nontrivial,
    IsLocalization.subsingleton_iff (M := Submonoid.powers h) (S := Localization.Away h)]
  rintro ⟨k, hk⟩
  exact hh ⟨k, hk⟩

theorem dsrd_key (n : ℕ) {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.FaithfullyFlat R S] [Nontrivial T]
    [Algebra.IsStandardSmooth R T]
    (hST : Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap S (S ⊗[R] T))) :
    Algebra.IsStandardSmoothOfRelativeDimension n R T := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth R T›
  haveI hmT : Algebra.IsStandardSmoothOfRelativeDimension P.dimension R T :=
    P.isStandardSmoothOfRelativeDimension rfl

  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential P.dimension]

  haveI : Nontrivial (S ⊗[R] T) := inferInstance
  haveI hmA : Algebra.IsStandardSmoothOfRelativeDimension P.dimension S (S ⊗[R] T) := inferInstance

  obtain ⟨s, hs1, hs⟩ := hST
  obtain ⟨h, hh, hnil⟩ := dsrd_exists_mem_not_isNilpotent hs1
  haveI : Nontrivial (Localization.Away h) := dsrd_nontrivial_localizationAway hnil

  have hn : Algebra.IsStandardSmoothOfRelativeDimension n S (Localization.Away h) := by
    have := hs h hh
    rwa [← IsScalarTower.algebraMap_eq, isStandardSmoothOfRelativeDimension_algebraMap] at this

  have hm : Algebra.IsStandardSmoothOfRelativeDimension (0 + P.dimension) S (Localization.Away h) := by
    haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (S ⊗[R] T) (Localization.Away h) :=
      Algebra.IsStandardSmoothOfRelativeDimension.localization_away h
    exact Algebra.IsStandardSmoothOfRelativeDimension.trans (P.dimension) 0 S (S ⊗[R] T)
      (Localization.Away h)

  haveI : Algebra.IsStandardSmooth S (Localization.Away h) := by
    haveI := hn
    exact Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have h1 := (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mp hn
  have h2 := (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth
    (0 + P.dimension)).mp hm
  have : ((0 + P.dimension : ℕ) : Cardinal) = n := h2.symm.trans h1
  simpa using this

theorem dsrd_locally_baseChange_localizationAway (n : ℕ) {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (g : T)
    (hST : Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap S (S ⊗[R] T))) :
    Locally (IsStandardSmoothOfRelativeDimension n)
      (algebraMap S (S ⊗[R] Localization.Away g)) := by
  letI alg : Algebra (S ⊗[R] T) (S ⊗[R] Localization.Away g) :=
    (Algebra.TensorProduct.map (AlgHom.id S S)
      (IsScalarTower.toAlgHom R T (Localization.Away g))).toRingHom.toAlgebra
  have halg : algebraMap (S ⊗[R] T) (S ⊗[R] Localization.Away g) =
      (Algebra.TensorProduct.map (AlgHom.id S S)
        (IsScalarTower.toAlgHom R T (Localization.Away g))).toRingHom := rfl
  haveI : IsScalarTower S (S ⊗[R] T) (S ⊗[R] Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap S (S ⊗[R] Localization.Away g) x =
        (Algebra.TensorProduct.map (AlgHom.id S S)
          (IsScalarTower.toAlgHom R T (Localization.Away g))) (algebraMap S (S ⊗[R] T) x)
      rw [AlgHom.commutes]
  have H : (algebraMap (S ⊗[R] T) (S ⊗[R] Localization.Away g)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap T (Localization.Away g)) := by
    ext t
    simp [halg, Algebra.TensorProduct.map_tmul]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right R S (Submonoid.powers g)
    (Localization.Away g) H
  rw [Submonoid.map_powers] at hloc
  haveI : IsLocalization.Away ((Algebra.TensorProduct.includeRight (R := R) (A := S)) g)
      (S ⊗[R] Localization.Away g) := hloc
  have key := locally_stableUnderCompositionWithLocalizationAwayTarget
    (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway (n := n)).2
    (S ⊗[R] Localization.Away g) ((Algebra.TensorProduct.includeRight (R := R) (A := S)) g)
    (algebraMap S (S ⊗[R] T)) hST
  rwa [← IsScalarTower.algebraMap_eq] at key

theorem dsrd_locally_isStandardSmoothOfRelativeDimension_codescendsAlong (n : ℕ) :
    CodescendsAlong (Locally (IsStandardSmoothOfRelativeDimension n)) FaithfullyFlat := by
  refine CodescendsAlong.mk _ (locally_respectsIso isStandardSmoothOfRelativeDimension_respectsIso)
    fun R S T _ _ _ _ _ hS hST => ?_
  haveI : Module.FaithfullyFlat R S := (faithfullyFlat_algebraMap_iff).mp hS

  have hsmST : (algebraMap S (S ⊗[R] T)).Smooth :=
    smooth_iff_locally_isStandardSmooth.mpr
      (locally_of_locally
        (fun {_ _} _ _ {f} hf => IsStandardSmoothOfRelativeDimension.isStandardSmooth n f hf) hST)
  haveI : Algebra.Smooth R T :=
    smooth_algebraMap.mp
      (CodescendsAlong.algebraMap_tensorProduct (hPQ := Smooth.codescendsAlong_faithfullyFlat)
        (h := hS) (H := hsmST))

  choose g hg hgsm using fun q : PrimeSpectrum T =>
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R q.asIdeal
  refine locally_of_exists isStandardSmoothOfRelativeDimension_respectsIso (algebraMap R T) g ?_
    (fun q => Localization.Away (g q)) fun q => ?_
  ·
    by_contra htop
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ htop
    exact hg ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨⟨m, hm.isPrime⟩, rfl⟩))
  ·
    rw [← IsScalarTower.algebraMap_eq, isStandardSmoothOfRelativeDimension_algebraMap]
    haveI := hgsm q
    haveI : Nontrivial (Localization.Away (g q)) := by
      refine dsrd_nontrivial_localizationAway fun ⟨k, hk⟩ => hg q ?_
      exact q.isPrime.mem_of_pow_mem k (hk ▸ q.asIdeal.zero_mem)
    exact dsrd_key n (dsrd_locally_baseChange_localizationAway n (g q) hST)

end RingHom

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective SmoothOfRelativeDimension HasRingHomProperty.descendsAlong IsLocalIso QuasiCompact IsLocalIso.le_of_isZariskiLocalAtSource Scheme Smooth Flat smoothOfRelativeDimension_isStableUnderBaseChange Etale flat_and_surjective_SpecMap_iff HasRingHomProperty"
p2m_open "AlgebraicGeometry"

theorem dsrd_smoothOfRelativeDimension_descendsAlong (n : ℕ) :
    DescendsAlong (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  refine HasRingHomProperty.descendsAlong (P := @SmoothOfRelativeDimension n)
    (P' := @Surjective ⊓ @Flat)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
    (Q' := fun f => f.FaithfullyFlat)
    (H₁ := ?_) (H₂ := ?_) (RingHom.dsrd_locally_isStandardSmoothOfRelativeDimension_codescendsAlong n)
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  · intro R S f hf
    exact (flat_and_surjective_SpecMap_iff f).mp ⟨hf.2, hf.1⟩

end AlgebraicGeometry

open CategoryTheory _root_.CategoryTheory.MorphismProperty _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry in
theorem solution (n : ℕ) :
    DescendsAlong (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  AlgebraicGeometry.dsrd_smoothOfRelativeDimension_descendsAlong n

end S_AlgebraicGeometry_SmoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact (solution)
