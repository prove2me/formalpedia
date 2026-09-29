-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0ebe2eba-396c-5ed0-84bc-08ac3b1ab2ca

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace SatVanishAux

open HomogeneousLocalization

variable {n : ℕ} {A : Type} [CommRing A]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "S" => MvPolynomial (Fin (n + 1)) A

noncomputable def elt (i j : Fin (n + 1)) (a : ℕ) (H : S) (hH : H.IsHomogeneous a) (N : ℕ) : Away 𝒜 (X j : S) :=
  HomogeneousLocalization.mk
    { deg := N + a
      num := ⟨X i ^ N * H, (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr ((MvPolynomial.isHomogeneous_X_pow i N).mul hH)⟩
      den := ⟨X j ^ (N + a), (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr (MvPolynomial.isHomogeneous_X_pow j (N + a))⟩
      den_mem := ⟨N + a, rfl⟩ }

noncomputable def ratio (i j : Fin (n + 1)) : Away 𝒜 (X j : S) :=
  HomogeneousLocalization.mk
    { deg := 1
      num := ⟨X i, ProjSpace.X_mem_one A n i⟩
      den := ⟨X j ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow j 1)⟩
      den_mem := ⟨1, rfl⟩ }

theorem val_elt (i j : Fin (n + 1)) (a : ℕ) (H : S) (hH : H.IsHomogeneous a) (N : ℕ) :
    (elt i j a H hH N).val = Localization.mk (X i ^ N * H) (⟨X j ^ (N + a), ⟨N + a, rfl⟩⟩ : ↥(Submonoid.powers (X j : S))) := rfl

theorem val_ratio_pow (i j : Fin (n + 1)) (L : ℕ) :
    (ratio (A := A) i j ^ L).val = Localization.mk (X i ^ L) (⟨X j ^ L, ⟨L, rfl⟩⟩ : ↥(Submonoid.powers (X j : S))) := by
  rw [HomogeneousLocalization.val_pow]
  show (Localization.mk (X i : S) (⟨X j ^ 1, ⟨1, rfl⟩⟩ : ↥(Submonoid.powers (X j : S)))) ^ L = _
  rw [Localization.mk_pow]
  congr 1
  exact Subtype.ext (by simp [← pow_mul])

theorem ratio_pow_mul_elt (i j : Fin (n + 1)) (a : ℕ) (H : S) (hH : H.IsHomogeneous a) (N L : ℕ) :
    ratio i j ^ L * elt i j a H hH N = elt i j a H hH (L + N) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_ratio_pow, val_elt, val_elt, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

theorem isLocalizationElem_eq_ratio (i j : Fin (n + 1)) :
    Away.isLocalizationElem (ProjSpace.X_mem_one A n j) (ProjSpace.X_mem_one A n i) = ratio i j := by
  apply HomogeneousLocalization.val_injective
  show Localization.mk ((X i : S) ^ 1) (⟨X j ^ 1, ⟨1, rfl⟩⟩ : ↥(Submonoid.powers (X j : S))) =
    Localization.mk (X i : S) (⟨X j ^ 1, ⟨1, rfl⟩⟩ : ↥(Submonoid.powers (X j : S)))
  rw [pow_one]

set_option maxHeartbeats 1600000 in

theorem claim (𝓘 : (Proj 𝒜).IdealSheafData) (i j : Fin (n + 1)) (a : ℕ) (H : S) (hH : H.IsHomogeneous a)
    (hmem : (Proj.awayToSection 𝒜 (X i : S))
      (HomogeneousLocalization.mk
        { deg := a
          num := ⟨H, (MvPolynomial.mem_homogeneousSubmodule a H).mpr hH⟩
          den := ⟨X i ^ a, (MvPolynomial.mem_homogeneousSubmodule a _).mpr (MvPolynomial.isHomogeneous_X_pow i a)⟩
          den_mem := ⟨a, rfl⟩ } : Away 𝒜 (X i : S)) ∈
      𝓘.ideal ⟨Proj.basicOpen 𝒜 (X i : S), Proj.isAffineOpen_basicOpen 𝒜 (X i : S) (ProjSpace.X_mem_one A n i) one_pos⟩) :
    ∃ M : ℕ, (Proj.awayToSection 𝒜 (X j : S)) (elt i j a H hH M) ∈
      𝓘.ideal ⟨Proj.basicOpen 𝒜 (X j : S), Proj.isAffineOpen_basicOpen 𝒜 (X j : S) (ProjSpace.X_mem_one A n j) one_pos⟩ := by
  classical
  have hXi : (X i : S) ∈ 𝒜 1 := ProjSpace.X_mem_one A n i
  have hXj : (X j : S) ∈ 𝒜 1 := ProjSpace.X_mem_one A n j
  set tI : Away 𝒜 (X i : S) := HomogeneousLocalization.mk
        { deg := a
          num := ⟨H, (MvPolynomial.mem_homogeneousSubmodule a H).mpr hH⟩
          den := ⟨X i ^ a, (MvPolynomial.mem_homogeneousSubmodule a _).mpr (MvPolynomial.isHomogeneous_X_pow i a)⟩
          den_mem := ⟨a, rfl⟩ } with htI

  set x : S := X j * X i with hxdef
  have hx : x = X j * X i := rfl
  have hx' : x = X i * X j := mul_comm _ _
  have hxdeg : x ∈ 𝒜 (1 + 1) := SetLike.mul_mem_graded hXj hXi
  let Ui : (Proj 𝒜).affineOpens := ⟨Proj.basicOpen 𝒜 (X i : S), Proj.isAffineOpen_basicOpen 𝒜 (X i : S) hXi one_pos⟩
  let Uj : (Proj 𝒜).affineOpens := ⟨Proj.basicOpen 𝒜 (X j : S), Proj.isAffineOpen_basicOpen 𝒜 (X j : S) hXj one_pos⟩
  let Ux : (Proj 𝒜).affineOpens := ⟨Proj.basicOpen 𝒜 x, Proj.isAffineOpen_basicOpen 𝒜 x hxdeg (by norm_num)⟩
  have hxi : Ux ≤ Ui := Proj.basicOpen_mono 𝒜 _ _ ⟨X j, hx'⟩
  have hxj : Ux ≤ Uj := Proj.basicOpen_mono 𝒜 _ _ ⟨X i, hx⟩

  let φi := (Proj.awayToSection 𝒜 (X i : S)).hom
  let φj := (Proj.awayToSection 𝒜 (X j : S)).hom
  let φx := (Proj.awayToSection 𝒜 x).hom
  let ψi : Away 𝒜 (X i : S) →+* Away 𝒜 x := HomogeneousLocalization.awayMap 𝒜 hXj hx'
  let ψj : Away 𝒜 (X j : S) →+* Away 𝒜 x := HomogeneousLocalization.awayMap 𝒜 hXi hx
  let resI := ((Proj 𝒜).presheaf.map (homOfLE hxi).op).hom
  let resJ := ((Proj 𝒜).presheaf.map (homOfLE hxj).op).hom
  have ci : ∀ t, φx (ψi t) = resI (φi t) := fun t => by
    have := Proj.awayMap_awayToSection 𝒜 (f := (X i : S)) hXj hx'
    exact congrArg (fun h => h.hom t) this
  have cj : φx.comp ψj = resJ.comp φj := by
    have := Proj.awayMap_awayToSection 𝒜 (f := (X j : S)) hXi hx
    ext t
    exact congrArg (fun h => h.hom t) this

  have hbijx : Function.Bijective φx := by
    have : IsIso (Proj.awayToSection 𝒜 x) := by
      rw [← Proj.basicOpenIsoAway_hom 𝒜 x hxdeg (by norm_num)]; infer_instance
    exact ConcreteCategory.bijective_of_isIso _
  have hsurjj : Function.Surjective φj := by
    have : IsIso (Proj.awayToSection 𝒜 (X j : S)) := by
      rw [← Proj.basicOpenIsoAway_hom 𝒜 (X j : S) hXj one_pos]; infer_instance
    exact (ConcreteCategory.bijective_of_isIso _).2

  have h1 : resI (φi tI) ∈ 𝓘.ideal Ux := by
    rw [← 𝓘.map_ideal hxi]; exact Ideal.mem_map_of_mem _ hmem

  set K : Ideal (Away 𝒜 (X j : S)) := (𝓘.ideal Uj).comap φj with hK
  have hKj : K.map φj = 𝓘.ideal Uj := Ideal.map_comap_of_surjective φj hsurjj _
  have h2 : 𝓘.ideal Ux = (K.map ψj).map φx := by
    rw [← 𝓘.map_ideal hxj, ← hKj, Ideal.map_map, Ideal.map_map, cj]
  have h3 : ψi tI ∈ K.map ψj := by
    have : φx (ψi tI) ∈ (K.map ψj).map φx := by rw [← h2, ci]; exact h1
    obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_iff_of_surjective φx hbijx.2).mp this
    rwa [← hbijx.1 hwe]

  letI : Algebra (Away 𝒜 (X j : S)) (Away 𝒜 x) := ψj.toAlgebra
  haveI := HomogeneousLocalization.Away.isLocalization_mul hXj hXi hx one_ne_zero
  have h3' : ψi tI ∈ K.map (algebraMap (Away 𝒜 (X j : S)) (Away 𝒜 x)) := h3
  obtain ⟨⟨⟨y, hyK⟩, ⟨c, hc⟩⟩, heq⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (Away.isLocalizationElem hXj hXi)) (Away 𝒜 x)).mp h3'
  obtain ⟨M, rfl⟩ := hc

  have heq' : ψi tI * ψj (ratio i j ^ M) = ψj y := by
    rw [← isLocalizationElem_eq_ratio]; exact heq

  have h4 : ψi tI * ψj (ratio i j ^ a) = ψj (elt i j a H hH 0) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, map_pow, HomogeneousLocalization.val_pow]
    have e1 : (ψi tI).val = Localization.mk (H * X j ^ a) (⟨x ^ a, ⟨a, rfl⟩⟩ : ↥(Submonoid.powers x)) := by
      rw [htI]; exact HomogeneousLocalization.val_awayMap_mk 𝒜 hXj hx' a _ a _
    have e2 : (ψj (ratio i j)).val = Localization.mk ((X i : S) * X i ^ 1) (⟨x ^ 1, ⟨1, rfl⟩⟩ : ↥(Submonoid.powers x)) :=
      HomogeneousLocalization.val_awayMap_mk 𝒜 hXi hx 1 _ 1 _
    have e3 : (ψj (elt i j a H hH 0)).val = Localization.mk ((X i ^ 0 * H) * X i ^ (0 + a)) (⟨x ^ (0 + a), ⟨0 + a, rfl⟩⟩ : ↥(Submonoid.powers x)) :=
      HomogeneousLocalization.val_awayMap_mk 𝒜 hXi hx (0 + a) _ (0 + a) _
    rw [e1, e2, e3, Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow, hx]
    ring

  have h5 : algebraMap (Away 𝒜 (X j : S)) (Away 𝒜 x) (elt i j a H hH 0 * ratio i j ^ M) =
      algebraMap (Away 𝒜 (X j : S)) (Away 𝒜 x) (y * ratio i j ^ a) := by
    show ψj _ = ψj _
    rw [map_mul, map_mul, ← h4, ← heq']; ring
  obtain ⟨⟨c', hc'⟩, hc'eq⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (Away.isLocalizationElem hXj hXi)) (Away 𝒜 x)).mp h5
  obtain ⟨M', rfl⟩ := hc'

  have hmemK : ratio i j ^ M' * (elt i j a H hH 0 * ratio i j ^ M) ∈ K := by
    have : ratio i j ^ M' * (elt i j a H hH 0 * ratio i j ^ M) = ratio i j ^ M' * (y * ratio i j ^ a) := by
      have h := hc'eq
      change Away.isLocalizationElem hXj hXi ^ M' * (elt i j a H hH 0 * ratio i j ^ M) =
        Away.isLocalizationElem hXj hXi ^ M' * (y * ratio i j ^ a) at h
      rw [isLocalizationElem_eq_ratio] at h
      exact h
    rw [this, ← mul_assoc, mul_comm (_ ^ M'), mul_assoc]
    exact K.mul_mem_right _ hyK
  refine ⟨(M' + M) + 0, ?_⟩
  have : ratio i j ^ M' * (elt i j a H hH 0 * ratio i j ^ M) = elt i j a H hH ((M' + M) + 0) := by
    rw [mul_comm (elt i j a H hH 0), ← mul_assoc, ← pow_add, ratio_pow_mul_elt]
  rw [← this]
  exact hmemK

end SatVanishAux

open SatVanishAux in
theorem solution
    (n : ℕ) (A : Type) [CommRing A] (𝓘 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IdealSheafData)
    (i : Fin (n + 1)) (a : ℕ) (H : MvPolynomial (Fin (n + 1)) A) (hH : H.IsHomogeneous a)
    (hmem : (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
      (HomogeneousLocalization.mk
        { deg := a
          num := ⟨H, (MvPolynomial.mem_homogeneousSubmodule a H).mpr hH⟩
          den := ⟨X i ^ a, (MvPolynomial.mem_homogeneousSubmodule a _).mpr (MvPolynomial.isHomogeneous_X_pow i a)⟩
          den_mem := ⟨a, rfl⟩ }) ∈
      𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩)
    (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∀ j : Fin (n + 1),
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))
        (HomogeneousLocalization.mk
          { deg := N + a
            num := ⟨X i ^ N * H, (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr ((MvPolynomial.isHomogeneous_X_pow i N).mul hH)⟩
            den := ⟨X j ^ (N + a), (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr (MvPolynomial.isHomogeneous_X_pow j (N + a))⟩
            den_mem := ⟨N + a, rfl⟩ }) ∈
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j) (ProjSpace.X_mem_one A n j) one_pos⟩ := by
  classical

  have hXi : (X i : MvPolynomial (Fin (n + 1)) A) ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A 1 := ProjSpace.X_mem_one A n i

  have claim : ∀ j : Fin (n + 1), ∃ M : ℕ,
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j)) (elt i j a H hH M) ∈
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j) (ProjSpace.X_mem_one A n j) one_pos⟩ := by
    intro j
    exact SatVanishAux.claim 𝓘 i j a H hH hmem

  have raise : ∀ (j : Fin (n + 1)) (M L : ℕ),
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j)) (elt i j a H hH M) ∈
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j) (ProjSpace.X_mem_one A n j) one_pos⟩ →
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j)) (elt i j a H hH (L + M)) ∈
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j) (ProjSpace.X_mem_one A n j) one_pos⟩ := by
    intro j M L h
    rw [← ratio_pow_mul_elt, map_mul]
    exact Ideal.mul_mem_left _ _ h
  choose Mf hMf using claim
  refine ⟨N₀ + ∑ j, Mf j, Nat.le_add_right _ _, fun j => ?_⟩
  have hle : Mf j ≤ N₀ + ∑ j, Mf j :=
    (Finset.single_le_sum (fun k _ => Nat.zero_le (Mf k)) (Finset.mem_univ j)).trans (Nat.le_add_left _ _)
  obtain ⟨L, hL⟩ := Nat.exists_eq_add_of_le hle
  have := raise j (Mf j) L (hMf j)
  rw [show N₀ + ∑ j, Mf j = L + Mf j by omega]
  exact this

end S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal (solution)
