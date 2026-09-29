-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3a1d4457-fd1f-5c7e-8b58-56ce4baf875f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace KcR4S220
namespace ChartExtension

open HomogeneousLocalization TopologicalSpace Opposite

section Geometry

variable (A : Type) [CommRing A] (n : ℕ)

theorem proj_basicOpen_awayToSection_ratio (j i : Fin (n + 1)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).basicOpen
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j)).hom
          (ProjSpace.ratio A n j i))
      = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
          ((MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) * MvPolynomial.X i) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A with h𝒜
  set z : Away 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) := ProjSpace.ratio A n j i with hz
  have hkey : ∀ (x : Proj 𝒜) (hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A)),
      IsUnit ((Proj 𝒜).presheaf.germ _ x hxj ((Proj.awayToSection 𝒜 (MvPolynomial.X j)).hom z))
        ↔ (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A) ∉ x.asHomogeneousIdeal := by
    intro x hxj
    have hxj' : (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A)
        ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hxj
    have hgerm := congrArg (fun ψ => CommRingCat.Hom.hom ψ z)
      (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X j) x hxj)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hgerm
    erw [hgerm]
    haveI : IsLocalHom (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom := isLocalHom_of_isIso _
    refine (isUnit_map_iff (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom _).trans ?_
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
    have hval : (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxj') z).val
        = Localization.mk (MvPolynomial.X i)
            ⟨(MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ 1, pow_mem hxj' 1⟩ := by
      simp only [hz, ProjSpace.ratio, HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
        HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
      rfl
    rw [show Submonoid.powers_le.mpr hxj = Submonoid.powers_le.mpr hxj' from rfl, hval,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact Iff.rfl
  ext x
  simp only [SetLike.mem_coe, Proj.basicOpen_mul, Proj.mem_basicOpen, Opens.mem_inf]
  refine ⟨fun hx => ?_, fun ⟨hxj, hxi⟩ => ?_⟩
  · have hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) :=
      Scheme.basicOpen_le _ _ hx
    exact ⟨hxj, (hkey x hxj).mp ((Scheme.mem_basicOpen _ _ x hxj).mp hx)⟩
  · exact (Scheme.mem_basicOpen _ _ x hxj).mpr ((hkey x hxj).mpr hxi)

end Geometry

section Fractions

variable {A : Type} [CommRing A] (n : ℕ)

def frac (j : Fin (n + 1)) (k : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous k) :
    Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j : MvPolynomial (Fin (n + 1)) A) :=
  HomogeneousLocalization.mk
    { deg := k
      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule k F).mpr hF⟩
      den := ⟨X j ^ k, (MvPolynomial.mem_homogeneousSubmodule k _).mpr (MvPolynomial.isHomogeneous_X_pow j k)⟩
      den_mem := ⟨k, rfl⟩ }

theorem frac_pow_mul (j i : Fin (n + 1)) (k K : ℕ) (F : MvPolynomial (Fin (n + 1)) A)
    (hF : F.IsHomogeneous k) (hG : (X i ^ K * F).IsHomogeneous (k + K)) :
    frac n j (k + K) (X i ^ K * F) hG = ProjSpace.ratio A n j i ^ K * frac n j k F hF := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, ProjSpace.ratio, HomogeneousLocalization.Away.mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_pow, HomogeneousLocalization.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

def corr (j i : Fin (n + 1)) (k : ℕ) :
    Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) ((X j : MvPolynomial (Fin (n + 1)) A) * X i) :=
  HomogeneousLocalization.mk
    { deg := (1 + 1) * k
      num := ⟨X i ^ ((1 + 1) * k),
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X_pow i _)⟩
      den := ⟨(X j * X i) ^ k,
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (((MvPolynomial.isHomogeneous_X A j).mul (MvPolynomial.isHomogeneous_X A i)).pow k)⟩
      den_mem := ⟨k, rfl⟩ }

theorem awayMap_frac_eq (j i : Fin (n + 1)) (k : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous k) :
    HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
        (ProjSpace.X_mem_one A n i) (rfl : (X j : MvPolynomial (Fin (n + 1)) A) * X i = X j * X i) (frac n j k F hF) =
      HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
        (ProjSpace.X_mem_one A n j) (mul_comm (X j) (X i) : (X j : MvPolynomial (Fin (n + 1)) A) * X i = X i * X j)
        (frac n i k F hF) * corr n j i k := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, frac, frac, HomogeneousLocalization.val_awayMap_mk,
    HomogeneousLocalization.val_awayMap_mk, corr, HomogeneousLocalization.val_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

end Fractions

section Main

variable {A : Type} [CommRing A] (n : ℕ) {Z : Scheme.{0}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

theorem res_app (U' V' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).Opens) (hVU : V' ≤ U')
    (hle : ι ⁻¹ᵁ V' ≤ ι ⁻¹ᵁ U') (a : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A), U')) :
    (Z.presheaf.map (homOfLE hle).op).hom ((ι.app U').hom a) =
      (ι.app V').hom (((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).presheaf.map (homOfLE hVU).op).hom a) := by
  have e := ι.map_appLE (le_rfl : ι ⁻¹ᵁ V' ≤ ι ⁻¹ᵁ V') (homOfLE hVU).op
  rw [Scheme.Hom.appLE_eq_app] at e
  have e' := congrArg (fun φ => φ.hom a) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e'
  rw [e']
  rfl

theorem exists_pow_mul_eq_zero [IsClosedImmersion ι] (i : Fin (n + 1)) (k : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous k)
    (h : (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))).hom
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)).hom (frac n i k F hF)) = 0)
    (j : Fin (n + 1)) :
    ∃ K : ℕ,
      (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))).hom
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j)).hom (ProjSpace.ratio A n j i)) ^ K *
        (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))).hom
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j)).hom (frac n j k F hF)) = 0 := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A with h𝒜
  set U : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (X j) with hU
  set U' : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (X i) with hU'
  set V : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 ((X j : MvPolynomial (Fin (n + 1)) A) * X i) with hV
  have hVU : V ≤ U := Proj.basicOpen_mono _ _ _ ⟨X i, rfl⟩
  have hVU' : V ≤ U' := Proj.basicOpen_mono _ _ _ ⟨X j, mul_comm _ _⟩
  have hle : ι ⁻¹ᵁ V ≤ ι ⁻¹ᵁ U := fun x hx => hVU hx
  have hle' : ι ⁻¹ᵁ V ≤ ι ⁻¹ᵁ U' := fun x hx => hVU' hx
  set σ : Γ(Z, ι ⁻¹ᵁ U) := (ι.app U).hom ((Proj.awayToSection 𝒜 (X j)).hom (ProjSpace.ratio A n j i)) with hσ
  set T : Γ(Z, ι ⁻¹ᵁ U) := (ι.app U).hom ((Proj.awayToSection 𝒜 (X j)).hom (frac n j k F hF)) with hT

  have h1 : (Z.presheaf.map (homOfLE hle).op).hom T = 0 := by
    rw [hT, res_app n ι U V hVU hle]
    have r1 := congrArg (fun φ => φ.hom (frac n j k F hF))
      (Proj.awayMap_awayToSection 𝒜 (ProjSpace.X_mem_one A n i)
        (x := (X j : MvPolynomial (Fin (n + 1)) A) * X i) rfl)
    have r2 := congrArg (fun φ => φ.hom (frac n i k F hF))
      (Proj.awayMap_awayToSection 𝒜 (ProjSpace.X_mem_one A n j)
        (x := (X j : MvPolynomial (Fin (n + 1)) A) * X i) (mul_comm (X j) (X i)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at r1 r2
    have h3 : (ι.app V).hom (((Proj 𝒜).presheaf.map (homOfLE hVU').op).hom
        ((Proj.awayToSection 𝒜 (X i)).hom (frac n i k F hF))) = 0 := by
      rw [← res_app n ι U' V hVU' hle', h, map_zero]
    have e1 : ((Proj 𝒜).presheaf.map (homOfLE hVU).op).hom ((Proj.awayToSection 𝒜 (X j)).hom (frac n j k F hF)) =
        (Proj.awayToSection 𝒜 ((X j : MvPolynomial (Fin (n + 1)) A) * X i)).hom
          (HomogeneousLocalization.awayMap 𝒜 (ProjSpace.X_mem_one A n i)
            (rfl : (X j : MvPolynomial (Fin (n + 1)) A) * X i = X j * X i) (frac n j k F hF)) := r1.symm
    have e2 : ((Proj 𝒜).presheaf.map (homOfLE hVU').op).hom ((Proj.awayToSection 𝒜 (X i)).hom (frac n i k F hF)) =
        (Proj.awayToSection 𝒜 ((X j : MvPolynomial (Fin (n + 1)) A) * X i)).hom
          (HomogeneousLocalization.awayMap 𝒜 (ProjSpace.X_mem_one A n j)
            (mul_comm (X j) (X i) : (X j : MvPolynomial (Fin (n + 1)) A) * X i = X i * X j) (frac n i k F hF)) := r2.symm
    rw [e1, awayMap_frac_eq, map_mul, map_mul, ← e2, h3, zero_mul]

  have hbo : Z.basicOpen σ = ι ⁻¹ᵁ V := by
    have eb : ι ⁻¹ᵁ ((Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (X j)).hom (ProjSpace.ratio A n j i))) =
        Z.basicOpen σ := Scheme.preimage_basicOpen ι _
    rw [← eb, proj_basicOpen_awayToSection_ratio]

  have hUaff : IsAffineOpen (ι ⁻¹ᵁ U) :=
    (Proj.isAffineOpen_basicOpen 𝒜 (X j) (ProjSpace.X_mem_one A n j) one_pos).preimage ι
  haveI := hUaff.isLocalization_basicOpen σ
  have hz : algebraMap Γ(Z, ι ⁻¹ᵁ U) Γ(Z, Z.basicOpen σ) T = 0 := by
    have key : ∀ (W : Z.Opens) (hW : W ≤ ι ⁻¹ᵁ U), W = ι ⁻¹ᵁ V →
        (Z.presheaf.map (homOfLE hW).op).hom T = 0 := by
      rintro W hW rfl
      exact h1
    exact key _ (Z.basicOpen_le σ) hbo
  obtain ⟨⟨_, K, rfl⟩, hK⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers σ) Γ(Z, Z.basicOpen σ) T).mp hz
  exact ⟨K, hK⟩

theorem main [IsClosedImmersion ι] (i : Fin (n + 1)) (k : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous k)
    (h : (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))).hom
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)).hom (frac n i k F hF)) = 0)
    (m : ℕ) :
    ∃ K : ℕ, m ≤ k + K ∧
      ∀ (hG : (X i ^ K * F).IsHomogeneous (k + K)) (j : Fin (n + 1)),
        (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))).hom
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j)).hom
            (frac n j (k + K) (X i ^ K * F) hG)) = 0 := by
  choose Kf hKf using exists_pow_mul_eq_zero n ι i k F hF h
  refine ⟨m + ∑ j, Kf j, by omega, fun hG j => ?_⟩
  have hjle : Kf j ≤ m + ∑ j, Kf j :=
    le_add_left (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjle
  rw [frac_pow_mul n j i k _ F hF hG, map_mul, map_pow, map_mul, map_pow, hd, pow_add, mul_right_comm, hKf j,
    zero_mul]

end Main

end KcR4S220.ChartExtension

end

open KcR4S220.ChartExtension in
theorem solution
    {A : Type} [CommRing A] (n : ℕ) {Z : Scheme.{0}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (i : Fin (n + 1)) (k : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous k)
    (h : ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
          (HomogeneousLocalization.mk
            { deg := k
              num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule k F).mpr hF⟩
              den := ⟨X i ^ k, (MvPolynomial.mem_homogeneousSubmodule k _).mpr (MvPolynomial.isHomogeneous_X_pow i k)⟩
              den_mem := ⟨k, rfl⟩ })) = 0)
    (m : ℕ) :
    ∃ K : ℕ, m ≤ k + K ∧
      ∀ (hG : (X i ^ K * F).IsHomogeneous (k + K)) (j : Fin (n + 1)),
        ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))
            (HomogeneousLocalization.mk
              { deg := k + K
                num := ⟨X i ^ K * F, (MvPolynomial.mem_homogeneousSubmodule (k + K) _).mpr hG⟩
                den := ⟨X j ^ (k + K), (MvPolynomial.mem_homogeneousSubmodule (k + K) _).mpr (MvPolynomial.isHomogeneous_X_pow j (k + K))⟩
                den_mem := ⟨k + K, rfl⟩ })) = 0 :=
  main n ι i k F hF h m

end S_AlgebraicGeometry_ProjSpace_exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero (solution)
