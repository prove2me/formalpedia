-- Prove2me | solution 1 for AlgebraicGeometry.maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/74babf0b-b0c8-5e71-8724-826e99b79ea1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span.AlgebraicGeometry TopologicalSpace Topology"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.stalkSpecializes_stalkMap_apply Spec Scheme"
p2m_open "AlgebraicGeometry"

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom Γ Hom.stalkSpecializes_stalkMap_apply functionField isoSpec isBasis_affineOpens le_iff_specializes" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

private theorem Scheme.map_comap_stalkSpecializes {X : Scheme.{u}} {x y : X} (h : y ⤳ x)
    (J : Ideal (X.presheaf.stalk y)) :
    (J.comap (X.presheaf.stalkSpecializes h).hom).map (X.presheaf.stalkSpecializes h).hom = J := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  letI iAx : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  letI iAy : Algebra Γ(X, U) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
  haveI hlx := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI hly := hU.isLocalization_stalk ⟨y, hyU⟩
  letI iA : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (X.presheaf.stalk y) := by
    apply IsScalarTower.of_algebraMap_eq'
    simp_rw [RingHom.algebraMap_toAlgebra]
    change (X.presheaf.germ U y hyU).hom = (X.presheaf.germ U x hxU ≫ X.presheaf.stalkSpecializes h).hom
    rw [X.presheaf.germ_stalkSpecializes]
  have hsp : (⟨y, hyU⟩ : U) ⤳ (⟨x, hxU⟩ : U) :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp h
  have hle : hU.primeIdealOf ⟨y, hyU⟩ ≤ hU.primeIdealOf ⟨x, hxU⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hsp.map hU.isoSpec.hom.continuous)
  have hle' : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ≤
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl := by
    intro a ha hay
    exact ha ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hle hay)
  haveI := IsLocalization.isLocalization_of_submonoid_le (X.presheaf.stalk x) (X.presheaf.stalk y)
    _ _ hle'
  exact IsLocalization.map_under (M := ((hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl.map
    (algebraMap Γ(X, U) (X.presheaf.stalk x)))) (S := X.presheaf.stalk y) J

p2m_open_scoped "AlgebraicGeometry.Scheme" in

private theorem Scheme.stalkSpecializes_genericPoint_closedPoint_injective
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] :
    Function.Injective ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes
      (genericPoint_specializes (IsLocalRing.closedPoint A))).hom :=
  IsFractionRing.injective
    ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A))
    (Spec (CommRingCat.of A)).functionField

end AlgebraicGeometry

theorem solution
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ c = 𝟙 _)
    (t : X.presheaf.stalk (σ.base (IsLocalRing.closedPoint A)))
    (ht : RingHom.ker (σ.stalkMap (IsLocalRing.closedPoint A)).hom = Ideal.span {t}) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk (σ.base (genericPoint ↥(Spec (CommRingCat.of A))))) =
      Ideal.span {(X.presheaf.stalkSpecializes
        (((genericPoint_specializes (IsLocalRing.closedPoint A)).map σ.continuous) :
          σ.base (genericPoint ↥(Spec (CommRingCat.of A))) ⤳ σ.base (IsLocalRing.closedPoint A))).hom t} := by

  clear hσ
  set hs := genericPoint_specializes (α := ↥(Spec (CommRingCat.of A))) (IsLocalRing.closedPoint A)
    with hs_def
  set h : σ.base (genericPoint ↥(Spec (CommRingCat.of A))) ⤳ σ.base (IsLocalRing.closedPoint A) :=
    hs.map σ.continuous with h_def

  rw [← Scheme.map_comap_stalkSpecializes h (IsLocalRing.maximalIdeal _)]
  suffices hc : (IsLocalRing.maximalIdeal _).comap (X.presheaf.stalkSpecializes h).hom =
      Ideal.span {t} by
    rw [hc, Ideal.map_span, Set.image_singleton]
    rfl

  rw [← ht]
  ext a
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [← IsLocalRing.maximalIdeal_comap
    (σ.stalkMap (genericPoint ↥(Spec (CommRingCat.of A)))).hom, Ideal.mem_comap]
  have hnat := Scheme.Hom.stalkSpecializes_stalkMap_apply σ
    (genericPoint ↥(Spec (CommRingCat.of A))) (IsLocalRing.closedPoint A) hs a
  erw [hnat]
  have hF : IsLocalRing.maximalIdeal
      ((Spec (CommRingCat.of A)).presheaf.stalk (genericPoint ↥(Spec (CommRingCat.of A)))) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField _)
  rw [hF, Ideal.mem_bot]
  exact map_eq_zero_iff _ (Scheme.stalkSpecializes_genericPoint_closedPoint_injective A)

end S_AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span
end P2MW
export P2MW.S_AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span (solution)
