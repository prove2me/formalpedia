-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.germ_app_appIso_inv_mem_maximalIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1c9385e9-8be4-5593-9aec-0139c1ad1ec8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_germ_app_appIso_inv_mem_maximalIdeal_iff

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_germ_app_appIso_inv_mem_maximalIdeal_iff.AlgebraicGeometry IsLocalRing TopologicalSpace"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom StructureSheaf.stalkAlgebra_map Scheme.Hom.germ_stalkMap_apply Spec StructureSheaf.toStalk Scheme IsOpenImmersion Scheme.Hom.appIso_inv_app_assoc Scheme.ΓSpecIso"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom Γ Hom.germ_stalkMap_apply Opens Hom.appIso_inv_app_assoc ΓSpecIso"
namespace StalkRead
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem germ_app_mem_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (x : X) (hx : f.base x ∈ V) (s : Γ(Y, V)) :
    (X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom ((f.app V).hom s) ∈ maximalIdeal (X.presheaf.stalk x) ↔
      (Y.presheaf.germ V (f.base x) hx).hom s ∈ maximalIdeal (Y.presheaf.stalk (f.base x)) := by
  rw [← Scheme.Hom.germ_stalkMap_apply f V x hx s, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

theorem germ_ΓSpecIso_inv_mem_iff (R : CommRingCat.{u}) (q : PrimeSpectrum R) (t : R) :
    ((Spec R).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso R).inv t) ∈ maximalIdeal ((Spec R).presheaf.stalk q) ↔
      t ∈ q.asIdeal := by
  have h1 : ((Spec R).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso R).inv t) =
      (StructureSheaf.toStalk R q).hom t := rfl
  have h2 : IsUnit ((StructureSheaf.toStalk R q).hom t) ↔ t ∈ q.asIdeal.primeCompl := by
    rw [← StructureSheaf.stalkAlgebra_map]
    exact IsLocalization.AtPrime.isUnit_to_map_iff _ q.asIdeal t
  have h3 : t ∈ q.asIdeal.primeCompl ↔ t ∉ q.asIdeal := Iff.rfl
  rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact (not_congr h2).trans ((not_congr h3).trans not_not)

theorem germ_appIso_inv_mem_iff {Y : Scheme.{u}} (R : CommRingCat.{u}) (ι : Spec R ⟶ Y) [IsOpenImmersion ι]
    (q : PrimeSpectrum R) (hq : ι.base q ∈ ι ''ᵁ ⊤) (t : R) :
    (Y.presheaf.germ (ι ''ᵁ ⊤) (ι.base q) hq).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv t)) ∈
        maximalIdeal (Y.presheaf.stalk (ι.base q)) ↔ t ∈ q.asIdeal := by
  rw [← germ_app_mem_iff ι (ι ''ᵁ ⊤) q hq]
  have hmor : (ι.appIso ⊤).inv ≫ ι.app (ι ''ᵁ ⊤) ≫ (Spec R).presheaf.germ (ι ⁻¹ᵁ ι ''ᵁ ⊤) q hq =
      (Spec R).presheaf.germ ⊤ q trivial := by
    rw [Scheme.Hom.appIso_inv_app_assoc]
    exact TopCat.Presheaf.germ_res _ _ _ _
  have : ((Spec R).presheaf.germ (ι ⁻¹ᵁ ι ''ᵁ ⊤) q hq).hom
        ((ι.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv t))) =
      ((Spec R).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso R).inv t) :=
    congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso R).inv t)) hmor
  rw [this, germ_ΓSpecIso_inv_mem_iff]

end AlgebraicGeometry.Scheme.StalkRead

theorem solution
    {X Y : Scheme.{u}} (f : Y ⟶ X) (R : CommRingCat.{u}) (ι : Spec R ⟶ X) [IsOpenImmersion ι]
    (y : ↥Y) (q : PrimeSpectrum ↑R) (hy : f.base y ∈ ι ''ᵁ ⊤) (hq : ι.base q = f.base y) (t : ↑R) :
    (Y.presheaf.germ (f ⁻¹ᵁ (ι ''ᵁ ⊤)) y hy).hom
        ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv t))) ∈
      IsLocalRing.maximalIdeal ↑(Y.presheaf.stalk y) ↔ t ∈ q.asIdeal := by
  rw [AlgebraicGeometry.Scheme.StalkRead.germ_app_mem_iff]
  have key : ∀ (z : ↥X) (hz : z ∈ ι ''ᵁ ⊤), ι.base q = z →
      ((X.presheaf.germ (ι ''ᵁ ⊤) z hz).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv t)) ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk z) ↔ t ∈ q.asIdeal) := by
    rintro z hz rfl
    exact AlgebraicGeometry.Scheme.StalkRead.germ_appIso_inv_mem_iff R ι q hz t
  exact key _ hy hq

end S_AlgebraicGeometry_Scheme_germ_app_appIso_inv_mem_maximalIdeal_iff
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_germ_app_appIso_inv_mem_maximalIdeal_iff (solution)
