-- Prove2me | solution 1 for AlgebraicGeometry.exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/599b5f1a-83be-599f-9684-f000278e4580

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isOpenImmersion_isClosed_cover_isEmpty_pullback_of_locallyQuasiFinite_of_henselianLocalRing
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "HasAffineProperty LocallyQuasiFinite IsFinite isAffine_of_isAffineHom QuasiCompact IsAffine Scheme.homeoOfIso LocallyOfFiniteType Spec IsIntegral Spec.map Scheme HasAffineProperty.iff_of_isAffine Flat IsSeparated Spec.map_id Flat.generalizingMap Scheme.Pullback.exists_preimage_pullback Scheme.ΓSpecIso exists_isFinite_isOpenImmersion_isClosed_cover_isEmpty_pullback_of_locallyQuasiFinite_of_henselianLocalRing Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing"
namespace HenselFlatSection
p2m_open "AlgebraicGeometry"

theorem isClosed_singleton_of_isFinite {K : Type u} [Field K] {F : Scheme.{u}} (f : F ⟶ Spec (.of K)) [IsFinite f]
    (y : F) : IsClosed ({y} : Set F) := by
  haveI : IsAffine F := isAffine_of_isAffineHom f
  have hfin : RingHom.Finite (f.appTop).hom :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp inferInstance).2

  letI alg : Algebra K Γ(F, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  haveI : Module.Finite K Γ(F, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    show RingHom.Finite ((f.appTop).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    exact hfin.comp (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  haveI : Algebra.IsIntegral K Γ(F, ⊤) := Algebra.IsIntegral.of_finite _ _

  let e := Scheme.homeoOfIso F.isoSpec
  rw [← e.isClosed_image, Set.image_singleton]
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := K)
  have hprime : (Ideal.comap (algebraMap K Γ(F, ⊤)) (e y).asIdeal).IsPrime := Ideal.comap_isPrime _ _
  rcases Ideal.eq_bot_or_top (Ideal.comap (algebraMap K Γ(F, ⊤)) (e y).asIdeal) with h | h
  · rw [h]; exact Ideal.bot_isMaximal
  · exact absurd h hprime.ne_top

end AlgebraicGeometry.HenselFlatSection

open AlgebraicGeometry.HenselFlatSection in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g] [Flat g]
    (x : X) (hx : g.base x = IsLocalRing.closedPoint R) :
    ∃ s : Spec (.of R) ⟶ X, s ≫ g = 𝟙 _ := by

  obtain ⟨Xf, X', i, j, hi, hj, hfin, hcov, -, hcl, -, -⟩ :=
    exists_isFinite_isOpenImmersion_isClosed_cover_isEmpty_pullback_of_locallyQuasiFinite_of_henselianLocalRing g
  haveI := hi
  haveI := hj
  haveI := hfin

  have hxi : x ∈ Set.range i.base := by
    have hx' : x ∈ Set.range i.base ∪ Set.range j.base := by
      have : x ∈ (Set.univ : Set X) := trivial
      rwa [← hcov] at this
    rcases hx' with h | ⟨x', hx'⟩
    · exact h
    · exact absurd ⟨x', by show g.base (j.base x') = _; rw [hx', hx]⟩ hcl
  obtain ⟨xf, hxf⟩ := hxi

  let ιK : Spec (.of K) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let η : Spec (.of R) := ιK.base (IsLocalRing.closedPoint K)
  have hη : η ⤳ (i ≫ g).base xf := by
    show η ⤳ g.base (i.base xf)
    rw [hxf, hx]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (IsLocalRing.le_maximalIdeal_of_isPrime η.asIdeal))
  obtain ⟨ξ, -, hξ⟩ := Flat.generalizingMap (i ≫ g) hη

  obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i ≫ g) (g := ιK) ξ (IsLocalRing.closedPoint K) hξ
  let fK : pullback (i ≫ g) ιK ⟶ Spec (.of K) := pullback.snd (i ≫ g) ιK
  haveI : IsFinite fK := MorphismProperty.pullback_snd (P := @IsFinite) _ _ inferInstance
  obtain ⟨zK, hzK, -⟩ := Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton fK K y
    (isClosed_singleton_of_isFinite fK y)
  have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _
  rw [hid] at hzK

  let xK : Spec (.of K) ⟶ X := (zK ≫ pullback.fst (i ≫ g) ιK) ≫ i
  have hxK : xK ≫ g = ιK := by
    simp only [xK, Category.assoc]
    rw [pullback.condition, ← Category.assoc, hzK, Category.id_comp]

  obtain ⟨s, hs, -⟩ := (exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing R K g i j hcov hcl
    xK hxK).mpr ⟨zK ≫ pullback.fst (i ≫ g) ιK, rfl⟩
  exact ⟨s, hs⟩

end S_AlgebraicGeometry_exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed (solution)
