-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/dde9277f-556a-5b48-957b-2ecf36e3cc06

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace G3s

theorem stalkSpecializes_injective {X : Scheme.{u}} [IsIntegral X] {x y : X} (h : x ⤳ y) :
    Function.Injective (X.presheaf.stalkSpecializes h) := by

  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hcomp : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes hgx
      = X.presheaf.stalkSpecializes (hgx.trans h) := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  have hinj : Function.Injective (X.presheaf.stalkSpecializes (hgx.trans h)) := by
    have : (X.presheaf.stalkSpecializes (hgx.trans h)).hom
        = algebraMap (X.presheaf.stalk y) X.functionField := rfl
    rw [show (X.presheaf.stalkSpecializes (hgx.trans h) : _ → _) = algebraMap (X.presheaf.stalk y) X.functionField
      from rfl]
    exact IsFractionRing.injective _ _
  have hinj' : Function.Injective ((X.presheaf.stalkSpecializes hgx) ∘ (X.presheaf.stalkSpecializes h)) := by
    intro a b hab
    apply hinj
    show (X.presheaf.stalkSpecializes (hgx.trans h)) a = (X.presheaf.stalkSpecializes (hgx.trans h)) b
    rw [← hcomp]
    exact hab
  exact hinj'.of_comp

theorem exists_frac {G : Scheme.{u}} [IsIntegral G] (y z : G) (hy : y = genericPoint G) (h : y ⤳ z)
    (k : G.presheaf.stalk y) :
    ∃ r s : G.presheaf.stalk z, s ≠ 0 ∧ k * G.presheaf.stalkSpecializes h s = G.presheaf.stalkSpecializes h r := by
  subst hy
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (G.presheaf.stalk z)) (S := G.functionField) k
  refine ⟨r, s.1, nonZeroDivisors.ne_zero s.2, ?_⟩
  exact hrs

theorem main {Γ G : Scheme.{u}} [IsIntegral Γ] [IsIntegral G] (π : Γ ⟶ G)
    (hgen : π.base (genericPoint Γ) = genericPoint G)
    (hbir : IsIso (π.stalkMap (genericPoint Γ)))
    (γ : Γ) [IsDiscreteValuationRing (G.presheaf.stalk (π.base γ))] :
    IsIso (π.stalkMap γ) := by

  set R := G.presheaf.stalk (π.base γ) with hR
  set A := Γ.presheaf.stalk γ with hA
  let φ : R →+* A := (π.stalkMap γ).hom
  have hξγ : genericPoint Γ ⤳ γ := (genericPoint_spec Γ).specializes trivial

  let ι : A →+* Γ.functionField := (Γ.presheaf.stalkSpecializes hξγ).hom
  have hι : Function.Injective ι := stalkSpecializes_injective hξγ
  let sp : R →+* G.presheaf.stalk (π.base (genericPoint Γ)) :=
    (G.presheaf.stalkSpecializes (π.base.hom.map_specializes hξγ)).hom
  let ψ : G.presheaf.stalk (π.base (genericPoint Γ)) →+* Γ.functionField := (π.stalkMap (genericPoint Γ)).hom
  have hsq : ∀ r : R, ψ (sp r) = ι (φ r) := fun r =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply π (genericPoint Γ) γ hξγ r
  have hψ : Function.Bijective ψ := ConcreteCategory.bijective_of_isIso (π.stalkMap (genericPoint Γ))
  have hsp : Function.Injective sp := stalkSpecializes_injective _

  have hinj : Function.Injective φ := by
    intro a b hab
    apply hsp; apply hψ.1
    rw [hsq, hsq, hab]

  have hfrac : ∀ a : A, ∃ r s : R, s ≠ 0 ∧ a * φ s = φ r := by
    intro a
    obtain ⟨k, hk⟩ := hψ.2 (ι a)
    obtain ⟨r, s, hs, hrs⟩ := exists_frac (π.base (genericPoint Γ)) (π.base γ) hgen
      (π.base.hom.map_specializes hξγ) k
    refine ⟨r, s, hs, hι ?_⟩
    rw [map_mul, ← hsq, ← hsq, ← hk]
    show ψ k * ψ (sp s) = ψ (sp r)
    rw [← map_mul]
    exact congrArg ψ hrs

  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨r, s, hs, hrs⟩ := hfrac a
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
    by_cases hr : r = 0
    · subst hr
      rw [map_zero] at hrs
      have hφs : φ ((u : R) * ϖ ^ n) ≠ 0 := fun h0 => hs (hinj (h0.trans (map_zero φ).symm))
      exact ⟨0, by rw [map_zero]; exact (mul_eq_zero.mp hrs).resolve_right hφs |>.symm⟩
    obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    have hϖA : φ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinj (h0.trans (map_zero φ).symm))
    rcases Nat.lt_or_ge m n with hmn | hnm
    ·
      exfalso
      have h1 : (a * φ u * φ ϖ ^ (n - m - 1)) * φ ϖ * φ ϖ ^ m = φ v * φ ϖ ^ m := by
        have : n = (n - m - 1) + 1 + m := by omega
        rw [this] at hrs
        simp only [map_mul, map_pow, pow_add, pow_one] at hrs
        simpa only [mul_assoc] using hrs
      have h2 : (a * φ u * φ ϖ ^ (n - m - 1)) * φ ϖ = φ v := mul_right_cancel₀ (pow_ne_zero m hϖA) h1
      have hunit : IsUnit (φ ϖ) := by
        have hv : IsUnit (φ v) := (Units.isUnit v).map φ
        rw [← h2] at hv
        exact isUnit_of_mul_isUnit_right hv
      exact hϖ.not_isUnit ((isUnit_map_iff φ ϖ).mp hunit)
    ·
      refine ⟨((u⁻¹ : Rˣ) : R) * v * ϖ ^ (m - n), ?_⟩
      have h1 : a * φ u * φ ϖ ^ n = φ v * φ ϖ ^ (m - n) * φ ϖ ^ n := by
        rw [mul_assoc (φ v), ← pow_add, Nat.sub_add_cancel hnm]
        simpa only [map_mul, map_pow, mul_assoc] using hrs
      have h2 : a * φ u = φ v * φ ϖ ^ (m - n) :=
        mul_right_cancel₀ (pow_ne_zero n hϖA) h1
      have hu : φ ((u⁻¹ : Rˣ) : R) * φ u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      calc φ (((u⁻¹ : Rˣ) : R) * v * ϖ ^ (m - n))
          = φ ((u⁻¹ : Rˣ) : R) * (φ v * φ ϖ ^ (m - n)) := by rw [map_mul, map_mul, map_pow, mul_assoc]
        _ = φ ((u⁻¹ : Rˣ) : R) * (a * φ u) := by rw [h2]
        _ = a * (φ ((u⁻¹ : Rˣ) : R) * φ u) := by ring
        _ = a := by rw [hu, mul_one]
  exact (ConcreteCategory.isIso_iff_bijective (π.stalkMap γ)).mpr ⟨hinj, hsurj⟩

end G3s

theorem solution
    {Γ G : Scheme.{u}} [IsIntegral Γ] [IsIntegral G] (π : Γ ⟶ G)
    (hgen : π.base (genericPoint Γ) = genericPoint G)
    (hbir : IsIso (π.stalkMap (genericPoint Γ)))
    (γ : Γ) (hγ : γ ≠ genericPoint Γ)
    [IsDiscreteValuationRing (G.presheaf.stalk (π.base γ))] :
    IsIso (π.stalkMap γ) :=
  G3s.main π hgen hbir γ

end S_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint (solution)
