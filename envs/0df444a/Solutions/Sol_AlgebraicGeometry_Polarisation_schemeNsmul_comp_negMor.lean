-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.schemeNsmul_comp_negMor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9c274116-8757-5cf1-a6ad-1fddea61c2fa

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_schemeNsmul_comp_negMor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace K79HK

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : schemeHomOverComp ψ hψ (L.inv t x) * schemeHomOverComp ψ hψ x = 1 := by
    change L.mul t' _ _ = L.one t'
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural t t' ψ hψ]
  exact eq_inv_of_mul_eq_one_left h

theorem schemeHomOverComp_idPoint {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P :=
  Subtype.ext (Category.comp_id _)

theorem mapPt_schemeNsmul (m : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) P = L.nsmul t m P := by
  have h := L.nsmul_natural f t P.1 P.2 m (RelativeGroupLaw.idPoint (f := f))
  rw [schemeHomOverComp_idPoint] at h
  rw [← h]
  rfl

theorem mapPt_negMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L) P = L.inv t P := by
  have h := inv_natural L f t P.1 P.2 (Polarisation.idPt f)
  have h2 : schemeHomOverComp P.1 P.2 (Polarisation.idPt f) = P := Subtype.ext (Category.comp_id _)
  rw [h2] at h
  rw [← h]
  rfl

theorem nsmul_mul (hc : L.IsCommutative) (m : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    L.nsmul t m (L.mul t P Q) = L.mul t (L.nsmul t m P) (L.nsmul t m Q) := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun x y => hc t x y }
  have hpow : ∀ (x : SchemeHomOver t f) (n : ℕ), L.nsmul t n x = x ^ n := by
    intro x n
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]; rfl
  rw [hpow, hpow, hpow]
  exact mul_pow P Q m

end K79HK

open K79HK in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (m : ℕ) :
    L.schemeNsmul m ≫ Polarisation.negMor f L = Polarisation.negMor f L ≫ L.schemeNsmul m := by
  have key := (GoodReductionJacobian.RelativeGroupLaw.schemeNsmul_comp_eq_comp_schemeNsmul_of_hom L L ⟨Polarisation.negMor f L, Polarisation.negMor_over f L⟩ ?_).2.2 m
  · exact key
  · intro T t x y
    apply Subtype.ext
    have h1 := congrArg Subtype.val (mapPt_negMor L t (L.mul t x y))
    have h2 := congrArg Subtype.val (mapPt_negMor L t x)
    have h3 := congrArg Subtype.val (mapPt_negMor L t y)
    change (L.mul t x y).1 ≫ Polarisation.negMor f L = (L.mul t ⟨x.1 ≫ Polarisation.negMor f L, _⟩ ⟨y.1 ≫ Polarisation.negMor f L, _⟩).1
    change (L.mul t x y).1 ≫ Polarisation.negMor f L = _ at h1
    rw [h1]
    letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun a b => hc t a b }
    have : L.inv t (L.mul t x y) = L.mul t (L.inv t x) (L.inv t y) := by
      change (x * y)⁻¹ = x⁻¹ * y⁻¹; exact mul_inv x y
    rw [this]
    congr 1
    congr 1
    · exact Subtype.ext h2.symm
    · exact Subtype.ext h3.symm

end S_AlgebraicGeometry_Polarisation_schemeNsmul_comp_negMor
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_schemeNsmul_comp_negMor (solution)
