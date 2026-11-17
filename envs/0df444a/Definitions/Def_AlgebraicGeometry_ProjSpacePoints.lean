-- Prove2me | Definitions.Def_AlgebraicGeometry_ProjSpacePoints
-- name    : AlgebraicGeometry_ProjSpacePoints
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:25.142558+00:00
-- url     : https://prove2.me/theorems/49818c60-cef9-4b9f-b8bd-260eae687b45
-- title:
--   Projective scheme points from homogeneous coordinate vectors
-- statement:
--   The file defines evaluation maps from the degree-zero localizations of the standard projective charts and their common overlap maps. From a nonzero vector $v=(v_0,…,v_N)$ it constructs a scheme point of $P^N_K$ whose coordinates on the chart $v_i≠0$ satisfy $$X_j/X_i=v_j/v_i.$$ This is the coordinate-level constructor later used to compare projective presentations and their heights.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
set_option autoImplicit false

universe u
noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.ProjSpace

/-! ### Chart points

The two facts behind `kPointOfVec`: a coordinate tuple normalized at `i` defines an
`R`-algebra map out of the `i`-th standard chart, and two such chart maps that agree on all
ratios define the same morphism to projective space. They are proved here because the
definition of `kPointOfVec` depends on them. -/

namespace ChartLift

variable (R : Type*) [CommRing R] (n : ℕ) (i : Fin (n + 1))
  {B : Type*} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1)

/-- Evaluation at `b`, extended to the localization away from `X i`. -/
private noncomputable def lift0 :
    Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →+* B :=
  IsLocalization.Away.lift (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)
    (g := (MvPolynomial.aeval b : MvPolynomial (Fin (n + 1)) R →ₐ[R] B).toRingHom)
    (by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, hb]
        exact isUnit_one)

private theorem lift0_algebraMap (p : MvPolynomial (Fin (n + 1)) R) :
    lift0 R n i b hb (algebraMap _ _ p) = MvPolynomial.aeval b p :=
  IsLocalization.Away.lift_eq _ _ _

/-- The chart map: evaluation at `b` on the degree-zero part away from `X i`. -/
private noncomputable def liftAway :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B where
  toRingHom := (lift0 R n i b hb).comp
    (algebraMap (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)))
  commutes' r := by
    show lift0 R n i b hb ((algebraMap R (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) r).val) = algebraMap R B r
    rw [ProjSpace.val_algebraMap, lift0_algebraMap, MvPolynomial.aeval_C]

private theorem liftAway_ratio (k : Fin (n + 1)) :
    liftAway R n i b hb (ProjSpace.ratio R n i k) = b k := by
  show lift0 R n i b hb (ProjSpace.ratio R n i k).val = b k
  rw [ProjSpace.ratio, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', lift0,
    IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  show MvPolynomial.aeval b (MvPolynomial.X k) =
    MvPolynomial.aeval b (MvPolynomial.X i ^ 1) * b k
  simp [hb]

end ChartLift

/-- A tuple normalized at `i` is the image of the ratios under an `R`-algebra map out of
the `i`-th standard chart. -/
private theorem exists_algHom_away_apply_ratio_eq
    (R : Type*) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    {B : Type*} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B,
      ∀ k, φ (ProjSpace.ratio R n i k) = b k :=
  ⟨ChartLift.liftAway R n i b hb, ChartLift.liftAway_ratio R n i b hb⟩

namespace ChartGlue

open HomogeneousLocalization

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The chart away from `X i` maps to the chart away from `X i * X j`. -/
private noncomputable abbrev mapI (i j : Fin (n + 1)) :
    Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →+*
      Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * MvPolynomial.X j) :=
  awayMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (ProjSpace.X_mem_one R n j) rfl

/-- The chart away from `X j` maps to the chart away from `X i * X j`. -/
private noncomputable abbrev mapJ (i j : Fin (n + 1)) :
    Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →+*
      Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * MvPolynomial.X j) :=
  awayMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (ProjSpace.X_mem_one R n i)
    (mul_comm _ _)

private theorem mapJ_ratio_mul_mapI_ratio (i j l : Fin (n + 1)) :
    mapJ R n i j (ProjSpace.ratio R n j l) * mapI R n i j (ProjSpace.ratio R n i j) =
      mapI R n i j (ProjSpace.ratio R n i l) := by
  apply HomogeneousLocalization.val_injective
  simp only [ProjSpace.ratio, val_mul, awayMap_mk, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

private theorem isLocalizationElem_eq (i j : Fin (n + 1)) :
    Away.isLocalizationElem (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j) =
      ProjSpace.ratio R n i j := by
  apply HomogeneousLocalization.val_injective
  simp [ProjSpace.ratio, Away.val_mk]

private theorem mapI_algebraMap (i j : Fin (n + 1)) (r : R) :
    mapI R n i j (algebraMap R (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) r) =
      mapJ R n i j (algebraMap R (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) r) := by
  change awayMap _ _ _ (fromZeroRingHom _ _ (ProjSpace.grad0Equiv R n r)) =
    awayMap _ _ _ (fromZeroRingHom _ _ (ProjSpace.grad0Equiv R n r))
  rw [awayMap_fromZeroRingHom, awayMap_fromZeroRingHom]

section lift

variable {B : Type u} [CommRing B] [Algebra R B] (a : Fin (n + 1) → B) (i j : Fin (n + 1))
  (hj : IsUnit (a j))
  (ψi : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
  (hψi : ∀ l, ψi (ProjSpace.ratio R n i l) * a i = a l)

include hj hψi in
private theorem isUnit_ψi_elem :
    IsUnit (ψi.toRingHom
      (Away.isLocalizationElem (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j))) := by
  rw [isLocalizationElem_eq]
  have h : IsUnit (ψi (ProjSpace.ratio R n i j) * a i) := by rw [hψi j]; exact hj
  exact (IsUnit.mul_iff.mp h).1

/-- The common extension of the `i`-th chart map to the overlap chart. -/
private noncomputable def liftij :
    Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * MvPolynomial.X j) →+* B :=
  letI := (mapI R n i j).toAlgebra
  letI := Away.isLocalization_mul (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j)
    rfl one_ne_zero
  IsLocalization.Away.lift
    (Away.isLocalizationElem (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j))
    (g := ψi.toRingHom) (isUnit_ψi_elem R n a i j hj ψi hψi)

private theorem liftij_mapI (z : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) :
    liftij R n a i j hj ψi hψi (mapI R n i j z) = ψi z := by
  let := (mapI R n i j).toAlgebra
  let := Away.isLocalization_mul (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j)
    rfl one_ne_zero
  exact IsLocalization.Away.lift_eq
    (Away.isLocalizationElem (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j))
    (isUnit_ψi_elem R n a i j hj ψi hψi) z

private theorem liftij_mapJ
    (ψj : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (hψj : ∀ l, ψj (ProjSpace.ratio R n j l) * a j = a l)
    (z : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) :
    liftij R n a i j hj ψi hψi (mapJ R n i j z) = ψj z := by
  have hz : z ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R n j)) := by
    rw [ProjSpace.adjoin_range_ratio]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨l, rfl⟩ := hz
    rw [← hj.mul_left_inj, hψj l]
    have key : liftij R n a i j hj ψi hψi (mapJ R n i j (ProjSpace.ratio R n j l)) *
        (ψi (ProjSpace.ratio R n i j) * a i) = a l := by
      rw [← mul_assoc, ← liftij_mapI R n a i j hj ψi hψi (ProjSpace.ratio R n i j), ← map_mul,
        mapJ_ratio_mul_mapI_ratio, liftij_mapI, hψi]
    rwa [hψi j] at key
  | algebraMap r =>
    rw [← mapI_algebraMap, liftij_mapI, AlgHom.commutes, AlgHom.commutes]
  | add z w _ _ hz hw => rw [map_add, map_add, hz, hw, map_add]
  | mul z w _ _ hz hw => rw [map_mul, map_mul, hz, hw, map_mul]

end lift

end ChartGlue

open HomogeneousLocalization in
/-- Two chart maps that send the ratios to the same normalized coordinates define the same
morphism from `Spec B` to projective space. -/
private theorem specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
    (R : Type u) [CommRing R] (n : ℕ) (B : Type u) [CommRing B] [Algebra R B]
    (a : Fin (n + 1) → B) (i j : Fin (n + 1)) (hj : IsUnit (a j))
    (ψi : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (ψj : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (hψi : ∀ l, ψi (ProjSpace.ratio R n i l) * a i = a l)
    (hψj : ∀ l, ψj (ProjSpace.ratio R n j l) * a j = a l) :
    Spec.map (CommRingCat.ofHom ψi.toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
          (ProjSpace.X_mem_one R n i) one_pos =
      Spec.map (CommRingCat.ofHom ψj.toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
          (ProjSpace.X_mem_one R n j) one_pos := by
  have hψi' : ψi.toRingHom =
      (ChartGlue.liftij R n a i j hj ψi hψi).comp (ChartGlue.mapI R n i j) :=
    RingHom.ext fun z => (ChartGlue.liftij_mapI R n a i j hj ψi hψi z).symm
  have hψj' : ψj.toRingHom =
      (ChartGlue.liftij R n a i j hj ψi hψi).comp (ChartGlue.mapJ R n i j) :=
    RingHom.ext fun z => (ChartGlue.liftij_mapJ R n a i j hj ψi hψi ψj hψj z).symm
  rw [hψi', hψj', CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (awayMap _ _ _)) ≫ Proj.awayι _ _ _ _ =
    Spec.map _ ≫ Spec.map (CommRingCat.ofHom (awayMap _ _ _)) ≫ Proj.awayι _ _ _ _
  rw [Proj.SpecMap_awayMap_awayι _ (ProjSpace.X_mem_one R n i) one_pos (ProjSpace.X_mem_one R n j)
      rfl,
    Proj.SpecMap_awayMap_awayι _ (ProjSpace.X_mem_one R n j) one_pos (ProjSpace.X_mem_one R n i)
      (mul_comm _ _)]


private theorem exists_point_with_charts (K : Type) [Field K] (N : ℕ)
    (v : Fin (N + 1) → K) (hv : v ≠ 0) :
    ∃ x : Scheme.KPoint (π K N), ∀ (i : Fin (N + 1)), v i ≠ 0 →
      ∃ φ : HomogeneousLocalization.Away
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) →+* K,
        (∀ j, φ (ratio K N i j) = v j / v i) ∧
        x.1 = Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
            (MvPolynomial.X i) (X_mem_one K N i) one_pos := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    exact not_ne_iff.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨ψ, hψ⟩ := exists_algHom_away_apply_ratio_eq K N i
    (fun j => v j / v i) (div_self hi)
  let x : Scheme.KPoint (π K N) :=
    ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
          (MvPolynomial.X i) (X_mem_one K N i) one_pos, by
      rw [Category.assoc, awayι_comp_π, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext r : 2
      exact ψ.commutes r⟩
  refine ⟨x, ?_⟩
  intro j hj
  obtain ⟨φ, hφ⟩ := exists_algHom_away_apply_ratio_eq K N j
    (fun k => v k / v j) (div_self hj)
  refine ⟨φ.toRingHom, hφ, ?_⟩
  exact specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq K N K v i j
    (isUnit_iff_ne_zero.mpr hj) ψ φ
    (fun k => by rw [hψ k]; exact div_mul_cancel₀ _ hi)
    (fun k => by rw [hφ k]; exact div_mul_cancel₀ _ hj)

/-- A nonzero coordinate tuple defines a scheme point with its prescribed ratios
on every standard chart on which the corresponding coordinate is nonzero. -/
noncomputable def kPointOfVec (K : Type) [Field K] (N : ℕ)
    (v : Fin (N + 1) → K) (hv : v ≠ 0) : Scheme.KPoint (π K N) :=
  Classical.choose (exists_point_with_charts K N v hv)

/-- The coordinate point has its prescribed ratios on every standard chart. -/
theorem kPointOfVec_has_charts (K : Type) [Field K] (N : ℕ)
    (v : Fin (N + 1) → K) (hv : v ≠ 0) :
    ∀ (i : Fin (N + 1)), v i ≠ 0 →
      ∃ φ : HomogeneousLocalization.Away
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) →+* K,
        (∀ j, φ (ratio K N i j) = v j / v i) ∧
        (kPointOfVec K N v hv).1 = Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
            (MvPolynomial.X i) (X_mem_one K N i) one_pos :=
  Classical.choose_spec (exists_point_with_charts K N v hv)

end AlgebraicGeometry.ProjSpace


