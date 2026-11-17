-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.kPointOfVec_mem_iff_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:26.963248+00:00
-- url     : https://prove2.me/submissions/1fe3d481-2972-4f00-8573-a057c518a1a1

import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_eq_of_chart
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_mem_basicOpen_iff

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.ProjSpace

/-- Homogeneous polynomials vanish at the point of a vector exactly when their
ordinary evaluation on the vector is zero. -/
theorem _root_.solution {K : Type} [Field K] {N : ℕ}
    (z : Fin (N + 1) → K) (hz : z ≠ 0)
    (p : MvPolynomial (Fin (N + 1)) K) (d : ℕ) (hp : p.IsHomogeneous d) :
    p ∈ ((kPointOfVec K N z hz).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
      eval z p = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    apply hz
    funext i
    exact not_ne_iff.mp (fun hi => h ⟨i, hi⟩)
  let lift0 : Localization.Away (X i : MvPolynomial (Fin (N + 1)) K) →+* K :=
    IsLocalization.Away.lift (X i : MvPolynomial (Fin (N + 1)) K)
      (g := eval z) (by simpa using isUnit_iff_ne_zero.mpr hi)
  let φ : Away (homogeneousSubmodule (Fin (N + 1)) K) (X i) →ₐ[K] K :=
    { toRingHom := lift0.comp (algebraMap _ _)
      commutes' := by
        intro r
        change lift0 ((algebraMap K
          (Away (homogeneousSubmodule (Fin (N + 1)) K) (X i)) r).val) = r
        rw [val_algebraMap, IsLocalization.Away.lift_eq]
        simp }
  have hφ (j : Fin (N + 1)) : φ (ratio K N i j) = z j / z i := by
    change lift0 (ratio K N i j).val = z j / z i
    rw [ratio, Away.val_mk, Localization.mk_eq_mk']
    dsimp only [lift0]
    rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
    simp only [eval_X, pow_one]
    field_simp [hi]
  let x : Scheme.KPoint (π K N) :=
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Proj.awayι (homogeneousSubmodule (Fin (N + 1)) K) (X i)
        (X_mem_one K N i) one_pos, by
      rw [Category.assoc, awayι_comp_π, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext r : 2
      exact φ.commutes r⟩
  have hx : kPointOfVec K N z hz = x :=
    kPointOfVec_eq_of_chart x z hz i hi φ.toRingHom hφ rfl
  have hpoint : (kPointOfVec K N z hz).1 =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Proj.awayι (homogeneousSubmodule (Fin (N + 1)) K) (X i)
          (X_mem_one K N i) one_pos := congrArg Subtype.val hx
  have hpositive (q : MvPolynomial (Fin (N + 1)) K) (e : ℕ)
      (hq : q.IsHomogeneous e) (he : 0 < e) :
      q ∈ ((kPointOfVec K N z hz).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
        eval z q = 0 := by
    have heval : φ (Away.isLocalizationElem (X_mem_one K N i) hq) =
        eval z q / z i ^ e := by
      change lift0 (Localization.mk (q ^ 1)
        ⟨(X i : MvPolynomial (Fin (N + 1)) K) ^ e, ⟨e, rfl⟩⟩) = _
      rw [Localization.mk_eq_mk']
      dsimp only [lift0]
      rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
      simp only [eval_X, map_pow, pow_one]
      field_simp [hi]
    have hpre := Proj.awayι_preimage_basicOpen
      (homogeneousSubmodule (Fin (N + 1)) K)
      (X_mem_one K N i) one_pos hq he
    have hnon : q ∉ ((kPointOfVec K N z hz).1
        (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔ eval z q ≠ 0 := by
      change IsLocalRing.closedPoint K ∈ (kPointOfVec K N z hz).1 ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) K) q ↔ _
      rw [hpoint, Scheme.Hom.comp_preimage, hpre]
      change φ (Away.isLocalizationElem (X_mem_one K N i) hq) ∉
        IsLocalRing.maximalIdeal K ↔ _
      simp [heval, IsLocalRing.mem_maximalIdeal, hi]
    exact not_iff_not.mp hnon
  have hprod := hpositive (p * X i) (d + 1) (hp.mul (isHomogeneous_X K i)) (by omega)
  have hxi : (X i : MvPolynomial (Fin (N + 1)) K) ∉
      ((kPointOfVec K N z hz).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal :=
    (kPointOfVec_mem_basicOpen_iff K N z hz i).mpr hi
  constructor
  · intro h
    have hmul := ((kPointOfVec K N z hz).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal.toIdeal.mul_mem_right (X i) h
    have hzero := hprod.mp hmul
    simpa [hi] using hzero
  · intro h
    have hmul : p * X i ∈ ((kPointOfVec K N z hz).1
        (IsLocalRing.closedPoint K)).asHomogeneousIdeal := hprod.mpr (by simp [h])
    exact (((kPointOfVec K N z hz).1 (IsLocalRing.closedPoint K)).isPrime.mem_or_mem hmul).resolve_right hxi

end AlgebraicGeometry.ProjSpace
