-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalFiniteHyperellipticMapAndProperCurveDataDistinctProjectiveLineNamespaceV320261019
-- name    : MazurTransfer_Order13MixedQuadraticOriginalFiniteHyperellipticMapAndProperCurveDataDistinctProjectiveLineNamespaceV320261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T04:26:20.091397+00:00
-- url     : https://prove2.me/theorems/895c879a-cf54-461c-824e-f68ec65d51d2
-- title:
--   Original finite mixed quadratic hyperelliptic map and proper curve
-- statement:
--   The original mixed quadratic finite chart algebras, chart maps to the projective line, finite glued hyperelliptic morphism, and comparison of its composite with the glued curve structure morphism. All original public and private constructor values and types are compared with the source and the renamed original projective-line context. Properness follows over every commutative coefficient ring. Named downstream consumer: the actual proper smooth dyadic curve and integral Picard family.
-- source:
--   MazurTheorem integral mixed quadratic hyperelliptic map, by Vasily Ilin and contributors; original projective-line adaptation retains attribution to the Tau Ceti contributors. Apache-2.0; campaign pin only.

import Definitions.Def_MazurTransfer_Order13MixedQuadraticProjectiveLineOriginalProperAndAffineChartsDataDistinctPublicNamespaceV220261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalGluedCurveData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both actual mixed quadratic equations are monic in the
ordinate and their chart algebras are finite over the abscissa polynomial
ring. Named downstream consumer: finiteness of the actual map to P1.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticChartFiniteAlgebras
open Polynomial MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13DyadicMixedQuadraticCharts
universe u
variable (R : Type u) [CommRing R]

abbrev ordinaryEquation := equation R (ordinaryH R) (ordinaryF R)
abbrev reciprocalEquation := equation R (reciprocalH R) (reciprocalF R)

theorem mixed_equation_monic (h f : Polynomial R) : (equation R h f).Monic := by
  have he : equation R h f = X ^ 2 + (C h * X - C f) := by unfold equation; ring
  rw [he]
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_sub_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_mul_le _ _) (by
      calc
        degree (C h) + degree (X : Polynomial (Polynomial R)) ≤ 0 + 1 :=
          add_le_add degree_C_le degree_X_le
        _ < (2 : WithBot ℕ) := by norm_num)
  · exact lt_of_le_of_lt degree_C_le (by norm_num)

theorem ordinaryEquation_monic : (ordinaryEquation R).Monic := mixed_equation_monic R _ _
theorem reciprocalEquation_monic : (reciprocalEquation R).Monic := mixed_equation_monic R _ _

theorem ordinary_finite : Module.Finite (Polynomial R) (ordinaryCoordinateRing R) :=
  (ordinaryEquation_monic R).finite_adjoinRoot
theorem reciprocal_finite : Module.Finite (Polynomial R) (reciprocalCoordinateRing R) :=
  (reciprocalEquation_monic R).finite_adjoinRoot

end MazurTransfer.Order13MixedQuadraticChartFiniteAlgebras
#print axioms MazurTransfer.Order13MixedQuadraticChartFiniteAlgebras.ordinary_finite
#print axioms MazurTransfer.Order13MixedQuadraticChartFiniteAlgebras.reciprocal_finite

end
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Vas and contributors.
Released under Apache-2.0. Authors: Vasily Ilin.
Complete gluing, preimage, finite-morphism and properness proofs adapted
from the pinned WIP-compatible XOneThirteenHyperellipticMap.lean.
The coefficient ring is an arbitrary commutative ring, with no field or
characteristic restriction. No Noetherianity conclusion is asserted for
an arbitrary base ring. The independent adaptation uses the campaign
Mathlib pin and does not alter the core or separate Tau Ceti package pins.
Design boundary: the actual whole integral hyperelliptic map is finite,
and the actual glued mixed quadratic curve is proper over its base ring.
Named downstream consumer: the actual smooth proper integral curve family
and its compatible Picard family at two.
This file changes the affine equations and gluing object explicitly; it
does not assert a whole rational-fibre comparison with the old curve.
-/
noncomputable section

namespace MazurTransfer.Order13MixedQuadraticHyperellipticMap

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped DirectSum
open MazurTransfer MazurTorsion

universe u

private lemma zero_lt_one : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

section ChartRingMaps

variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]

/-- Evaluation of the homogeneous coordinates at `[x:1]`. -/
private def standardCoordinatePolynomialHom (x : A) :
    MvPolynomial (Fin 2) K →+* A :=
  MvPolynomial.eval₂Hom (algebraMap K A)
    fun i ↦ if i = 0 then x else 1

private lemma standardCoordinatePolynomialHom_X_one (x : A) :
    standardCoordinatePolynomialHom K A x
        (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [standardCoordinatePolynomialHom]

/-- The standard projective-line chart ring map sending `X₀/X₁` to
`x`. -/
noncomputable def standardChartRingHom (x : A) :
    HomogeneousLocalization.Away (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) →+* A :=
  (Localization.awayLift (standardCoordinatePolynomialHom K A x)
      (MvPolynomial.X (1 : Fin 2)) (by
        rw [standardCoordinatePolynomialHom_X_one]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

@[simp]
theorem standardChartRingHom_affineCoordinateAway (x : A) :
    standardChartRingHom K A x (Order13MixedQuadraticProjectiveLineOriginal20261019.affineCoordinateAway K) = x := by
  simp only [standardChartRingHom, RingHom.comp_apply,
    Order13MixedQuadraticProjectiveLineOriginal20261019.affineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K A x)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    (by rw [standardCoordinatePolynomialHom_X_one]; simp) 1
  simpa [standardCoordinatePolynomialHom] using h

/-- Evaluation of the homogeneous coordinates at `[1:z]`. -/
private def inverseCoordinatePolynomialHom (z : A) :
    MvPolynomial (Fin 2) K →+* A :=
  MvPolynomial.eval₂Hom (algebraMap K A)
    fun i ↦ if i = 1 then z else 1

private lemma inverseCoordinatePolynomialHom_X_zero (z : A) :
    inverseCoordinatePolynomialHom K A z
        (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [inverseCoordinatePolynomialHom]

/-- The infinity projective-line chart ring map sending `X₁/X₀` to
`z`. -/
noncomputable def infinityChartRingHom (z : A) :
    HomogeneousLocalization.Away (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) →+* A :=
  (Localization.awayLift (inverseCoordinatePolynomialHom K A z)
      (MvPolynomial.X (0 : Fin 2)) (by
        rw [inverseCoordinatePolynomialHom_X_zero]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)))
      (Localization.Away (MvPolynomial.X (0 : Fin 2))))

@[simp]
theorem infinityChartRingHom_inverseAffineCoordinateAway (z : A) :
    infinityChartRingHom K A z
        (Order13MixedQuadraticProjectiveLineOriginal20261019.inverseAffineCoordinateAway K) = z := by
  simp only [infinityChartRingHom, RingHom.comp_apply,
    Order13MixedQuadraticProjectiveLineOriginal20261019.inverseAffineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom K A z)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) 1
  simpa [inverseCoordinatePolynomialHom] using h

private theorem standardCoordinatePolynomialHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (x : A) :
    f.toRingHom.comp (standardCoordinatePolynomialHom K A x) =
      standardCoordinatePolynomialHom K B (f x) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp [standardCoordinatePolynomialHom]
  · intro i
    fin_cases i <;> simp [standardCoordinatePolynomialHom]

private theorem infinityCoordinatePolynomialHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (z : A) :
    f.toRingHom.comp (inverseCoordinatePolynomialHom K A z) =
      inverseCoordinatePolynomialHom K B (f z) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp [inverseCoordinatePolynomialHom]
  · intro i
    fin_cases i <;> simp [inverseCoordinatePolynomialHom]

/-- Homogeneous evaluation is invariant under the projective rescaling
`[x:1] = [1:z]` when `xz=1`. -/
private theorem eval_standard_eq_pow_mul_eval_inverse
    (p : MvPolynomial (Fin 2) K) (n : ℕ)
    (hp : p.IsHomogeneous n) (x z : A) (hxz : x * z = 1) :
    standardCoordinatePolynomialHom K A x p =
      x ^ n * inverseCoordinatePolynomialHom K A z p := by
  simp only [standardCoordinatePolynomialHom,
    inverseCoordinatePolynomialHom, MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d 0 + d 1 = n := by
    have h := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_two] using h
  simp only [Fin.prod_univ_two,
    if_neg (by decide : (1 : Fin 2) ≠ 0),
    if_neg (by decide : (0 : Fin 2) ≠ 1), if_true, one_pow,
    one_mul, mul_one]
  rw [← hdeg, pow_add]
  calc
    (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 =
        (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 * 1 := by
          rw [mul_one]
    _ = (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 *
        ((x * z) ^ d 1) := by rw [hxz, one_pow]
    _ = (x ^ d 0 * x ^ d 1) *
        ((algebraMap K A) (MvPolynomial.coeff d p) * z ^ d 1) := by
          rw [mul_pow]
          ring

private theorem overlapDenominator_mem_degree_two :
    MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2) ∈
      Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 2 := by
  simpa using
    (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K).mul
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K)

/-- Evaluation on the common projective-line chart `D₊(X₁X₀)`,
normalized as `[x:1]` with chosen inverse `z`. -/
private noncomputable def overlapChartRingHom
    (x z : A) (hxz : x * z = 1) :
    HomogeneousLocalization.Away (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2)) →+* A :=
  (Localization.awayLift (standardCoordinatePolynomialHom K A x)
      (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))
      (isUnit_iff_exists_inv.mpr ⟨z, by
        simpa [standardCoordinatePolynomialHom] using hxz⟩)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2)))
      (Localization.Away
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))))

private theorem standardChartRingHom_awayMk
    (x : A) (n : ℕ) (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K n) :
    standardChartRingHom K A x
        (HomogeneousLocalization.Away.mk
          (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) n p
          (by simpa using hp)) =
      standardCoordinatePolynomialHom K A x p := by
  simp only [standardChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K A x)
    (MvPolynomial.X (1 : Fin 2)) p 1
    (by rw [standardCoordinatePolynomialHom_X_one]; simp) n
  simpa using h

private theorem infinityChartRingHom_awayMk
    (z : A) (n : ℕ) (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K n) :
    infinityChartRingHom K A z
        (HomogeneousLocalization.Away.mk
          (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) n p
          (by simpa using hp)) =
      inverseCoordinatePolynomialHom K A z p := by
  simp only [infinityChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom K A z)
    (MvPolynomial.X (0 : Fin 2)) p 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) n
  simpa using h

private theorem standardChartRingHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (x : A) :
    f.toRingHom.comp (standardChartRingHom K A x) =
      standardChartRingHom K B (f x) := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) q
  have hp' : p ∈ Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K n := by
    simpa using hp
  rw [RingHom.comp_apply,
    standardChartRingHom_awayMk K A x n p hp',
    standardChartRingHom_awayMk K B (f x) n p hp']
  exact DFunLike.congr_fun
    (standardCoordinatePolynomialHom_naturality K A B f x) p

private theorem infinityChartRingHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (z : A) :
    f.toRingHom.comp (infinityChartRingHom K A z) =
      infinityChartRingHom K B (f z) := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) q
  have hp' : p ∈ Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K n := by
    simpa using hp
  rw [RingHom.comp_apply,
    infinityChartRingHom_awayMk K A z n p hp',
    infinityChartRingHom_awayMk K B (f z) n p hp']
  exact DFunLike.congr_fun
    (infinityCoordinatePolynomialHom_naturality K A B f z) p

private theorem overlapChartRingHom_awayMk
    (x z : A) (hxz : x * z = 1) (n : ℕ)
    (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K (n • 2)) :
    overlapChartRingHom K A x z hxz
        (HomogeneousLocalization.Away.mk
          (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (overlapDenominator_mem_degree_two K) n p
          (by simpa using hp)) =
      standardCoordinatePolynomialHom K A x p * z ^ n := by
  simp only [overlapChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K A x)
    (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))
    p z (by simpa [standardCoordinatePolynomialHom] using hxz) n
  simpa using h

private theorem overlapChartRingHom_comp_standardAwayMap
    (x z : A) (hxz : x * z = 1) :
    (overlapChartRingHom K A x z hxz).comp
        (HomogeneousLocalization.awayMap
          (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) rfl) =
      standardChartRingHom K A x := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) q
  have hp' : p ∈ Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K n := by
    simpa using hp
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.awayMap_mk]
  rw [overlapChartRingHom_awayMk K A x z hxz n
      (p * MvPolynomial.X (0 : Fin 2) ^ n),
    standardChartRingHom_awayMk K A x n p hp']
  · simp only [map_mul, map_pow, standardCoordinatePolynomialHom,
      MvPolynomial.eval₂Hom_X']
    simp only [if_pos]
    rw [mul_assoc, ← mul_pow, hxz, one_pow, mul_one]
  · simpa [nsmul_eq_mul, Nat.mul_two] using
      hp'.mul (SetLike.pow_mem_graded n
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K))

private theorem overlapChartRingHom_comp_infinityAwayMap
    (x z : A) (hxz : x * z = 1) :
    (overlapChartRingHom K A x z hxz).comp
        (HomogeneousLocalization.awayMap
          (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K)
          (mul_comm _ _)) =
      infinityChartRingHom K A z := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) q
  have hp' : p ∈ Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K n := by
    simpa using hp
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.awayMap_mk]
  rw [overlapChartRingHom_awayMk K A x z hxz n
      (p * MvPolynomial.X (1 : Fin 2) ^ n),
    infinityChartRingHom_awayMk K A z n p hp']
  · simp only [map_mul, map_pow, standardCoordinatePolynomialHom,
      MvPolynomial.eval₂Hom_X']
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0), one_pow,
      mul_one]
    change standardCoordinatePolynomialHom K A x p * z ^ n =
      inverseCoordinatePolynomialHom K A z p
    rw [eval_standard_eq_pow_mul_eval_inverse K A p n hp' x z hxz]
    calc
      (x ^ n * inverseCoordinatePolynomialHom K A z p) * z ^ n =
          inverseCoordinatePolynomialHom K A z p * (x * z) ^ n := by
            rw [mul_pow]
            ring
      _ = inverseCoordinatePolynomialHom K A z p := by
        rw [hxz, one_pow, mul_one]
  · simpa [nsmul_eq_mul, Nat.mul_two] using
      hp'.mul (SetLike.pow_mem_graded n
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K))

end ChartRingMaps

section ChartFiniteness

variable (K : Type u) [CommRing K]

private noncomputable def standardPolynomialToAway :
    Polynomial K →+*
      HomogeneousLocalization.Away (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) :=
  Polynomial.eval₂RingHom
    ((algebraMap (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0)
        (HomogeneousLocalization.Away
          (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2)))).comp
      (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K).toRingHom)
    (Order13MixedQuadraticProjectiveLineOriginal20261019.affineCoordinateAway K)

private theorem standardChartRingHom_comp_standardPolynomialToAway :
    (standardChartRingHom K
      (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)).comp
        (standardPolynomialToAway K) =
      (AdjoinRoot.of
        (Order13MixedQuadraticChartFiniteAlgebras.ordinaryEquation K)) := by
  apply Polynomial.ringHom_ext
  · intro k
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show standardPolynomialToAway K (Polynomial.C k) =
        (algebraMap (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))))
          (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K k) by
      change Polynomial.eval₂ _ _ (Polynomial.C k) = _
      exact Polynomial.eval₂_C _ _]
    have hp : MvPolynomial.C k ∈
        Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0 := by
      simp
    have hcoeff :
        (algebraMap (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))))
          (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K k) =
        HomogeneousLocalization.Away.mk
          (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) 0
          (MvPolynomial.C k) (by simp) := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk
          (((Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K k :
            Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0) :
              MvPolynomial (Fin 2) K)) ⟨1, by simp⟩ =
        Localization.mk (MvPolynomial.C k) ⟨1, by simp⟩
      rw [Order13MixedQuadraticProjectiveLineOriginal20261019.coe_degreeZeroRingEquiv_apply]
    rw [hcoeff,
      standardChartRingHom_awayMk K
        (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
        (Order13MixedQuadraticOverlapCoordinates.xCoordinate K) 0
        (MvPolynomial.C k) hp]
    rw [show standardCoordinatePolynomialHom K
        (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
        (Order13MixedQuadraticOverlapCoordinates.xCoordinate K) (MvPolynomial.C k) =
      algebraMap K (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K) k by
        simp [standardCoordinatePolynomialHom]]
    simpa [AdjoinRoot.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply K (Polynomial K)
        (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K) k)
  · simp [standardPolynomialToAway,
      Order13MixedQuadraticOverlapCoordinates.xCoordinate]

private theorem affineEquation_monic :
    (Order13MixedQuadraticChartFiniteAlgebras.ordinaryEquation K).Monic := by
  exact Order13MixedQuadraticChartFiniteAlgebras.ordinaryEquation_monic K

/-- The standard chart of the hyperelliptic map is finite. -/
theorem standardChartRingHom_finite :
    (standardChartRingHom K
      (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)).Finite := by
  apply RingHom.Finite.of_comp_finite (f := standardPolynomialToAway K)
  rw [standardChartRingHom_comp_standardPolynomialToAway K]
  change (algebraMap (Polynomial K)
    (AdjoinRoot (Order13MixedQuadraticChartFiniteAlgebras.ordinaryEquation K))).Finite
  exact RingHom.finite_algebraMap.mpr
    (affineEquation_monic K |>.finite_adjoinRoot)

private noncomputable def infinityPolynomialToAway :
    Polynomial K →+*
      HomogeneousLocalization.Away (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) :=
  Polynomial.eval₂RingHom
    ((algebraMap (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0)
        (HomogeneousLocalization.Away
          (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2)))).comp
      (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K).toRingHom)
    (Order13MixedQuadraticProjectiveLineOriginal20261019.inverseAffineCoordinateAway K)

private theorem infinityChartRingHom_comp_infinityPolynomialToAway :
    (infinityChartRingHom K
      (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)).comp
        (infinityPolynomialToAway K) =
      (AdjoinRoot.of
        (Order13MixedQuadraticChartFiniteAlgebras.reciprocalEquation K)) := by
  apply Polynomial.ringHom_ext
  · intro k
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show infinityPolynomialToAway K (Polynomial.C k) =
        (algebraMap (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))))
          (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K k) by
      change Polynomial.eval₂ _ _ (Polynomial.C k) = _
      exact Polynomial.eval₂_C _ _]
    have hp : MvPolynomial.C k ∈
        Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0 := by
      simp
    have hcoeff :
        (algebraMap (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))))
          (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K k) =
        HomogeneousLocalization.Away.mk
          (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) 0
          (MvPolynomial.C k) (by simp) := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk
          (((Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K k :
            Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0) :
              MvPolynomial (Fin 2) K)) ⟨1, by simp⟩ =
        Localization.mk (MvPolynomial.C k) ⟨1, by simp⟩
      rw [Order13MixedQuadraticProjectiveLineOriginal20261019.coe_degreeZeroRingEquiv_apply]
    rw [hcoeff,
      infinityChartRingHom_awayMk K
        (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
        (Order13MixedQuadraticOverlapCoordinates.zCoordinate K) 0
        (MvPolynomial.C k) hp]
    rw [show inverseCoordinatePolynomialHom K
        (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
        (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)
        (MvPolynomial.C k) =
      algebraMap K (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K) k by
        simp [inverseCoordinatePolynomialHom]]
    simpa [AdjoinRoot.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply K (Polynomial K)
        (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K) k)
  · simp [infinityPolynomialToAway,
      Order13MixedQuadraticOverlapCoordinates.zCoordinate]

private theorem reciprocalEquation_monic :
    (Order13MixedQuadraticChartFiniteAlgebras.reciprocalEquation K).Monic := by
  exact Order13MixedQuadraticChartFiniteAlgebras.reciprocalEquation_monic K

/-- The infinity chart of the hyperelliptic map is finite. -/
theorem infinityChartRingHom_finite :
    (infinityChartRingHom K
      (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)).Finite := by
  apply RingHom.Finite.of_comp_finite (f := infinityPolynomialToAway K)
  rw [infinityChartRingHom_comp_infinityPolynomialToAway K]
  change (algebraMap (Polynomial K)
    (AdjoinRoot
      (Order13MixedQuadraticChartFiniteAlgebras.reciprocalEquation K))).Finite
  exact RingHom.finite_algebraMap.mpr
    (reciprocalEquation_monic K |>.finite_adjoinRoot)

end ChartFiniteness

section ChartMorphisms

variable (K : Type u) [CommRing K]

private theorem projectiveLine_chart_maps_eq
    (A : Type u) [CommRing A] [Algebra K A]
    (x z : A) (hxz : x * z = 1) :
    Spec.map (CommRingCat.ofHom (standardChartRingHom K A x)) ≫
        Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2))
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one =
      Spec.map (CommRingCat.ofHom (infinityChartRingHom K A z)) ≫
        Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2))
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one := by
  let H := Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K
  let X₀ : MvPolynomial (Fin 2) K := MvPolynomial.X 0
  let X₁ : MvPolynomial (Fin 2) K := MvPolynomial.X 1
  let q : MvPolynomial (Fin 2) K := X₁ * X₀
  let hq : q ∈ H 2 := overlapDenominator_mem_degree_two K
  have hstd := overlapChartRingHom_comp_standardAwayMap K A x z hxz
  have hinf := overlapChartRingHom_comp_infinityAwayMap K A x z hxz
  calc
    Spec.map (CommRingCat.ofHom (standardChartRingHom K A x)) ≫
          Proj.awayι H X₁ (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K)
            zero_lt_one =
        (Spec.map (CommRingCat.ofHom (overlapChartRingHom K A x z hxz)) ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.awayMap H
              (f := X₁) (x := q)
              (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) rfl))) ≫
          Proj.awayι H X₁ (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K)
            zero_lt_one := by
              rw [← Spec.map_comp]
              congr 2
              apply CommRingCat.hom_ext
              exact hstd.symm
    _ = Spec.map (CommRingCat.ofHom
          (overlapChartRingHom K A x z hxz)) ≫
        Proj.awayι H q hq (by omega) := by
          rw [Category.assoc,
            Proj.SpecMap_awayMap_awayι
              (f := X₁) (g := X₀) (x := q) H
              (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one
              (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) rfl]
    _ = (Spec.map (CommRingCat.ofHom
          (overlapChartRingHom K A x z hxz)) ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.awayMap H
              (f := X₀) (x := q)
              (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K)
              (mul_comm X₁ X₀)))) ≫
        Proj.awayι H X₀ (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K)
          zero_lt_one := by
            rw [Category.assoc,
              Proj.SpecMap_awayMap_awayι
                (f := X₀) (g := X₁) (x := q) H
                (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one
                (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) (mul_comm X₁ X₀)]
    _ = Spec.map (CommRingCat.ofHom (infinityChartRingHom K A z)) ≫
        Proj.awayι H X₀ (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K)
          zero_lt_one := by
            rw [← Spec.map_comp]
            congr 2
            apply CommRingCat.hom_ext
            exact hinf

/-- The ordinary hyperelliptic chart map, with projective coordinate
`[x:1]`. -/
noncomputable def ordinaryChartToProjectiveLine :
    Order13DyadicMixedQuadraticCharts.ordinaryScheme K ⟶ Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K :=
  Spec.map (CommRingCat.ofHom
      (standardChartRingHom K
        (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
        (Order13MixedQuadraticOverlapCoordinates.xCoordinate K))) ≫
    Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one

/-- The reciprocal hyperelliptic chart map, with projective coordinate
`[1:z]`. -/
noncomputable def reciprocalChartToProjectiveLine :
    Order13DyadicMixedQuadraticCharts.reciprocalScheme K ⟶
      Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K :=
  Spec.map (CommRingCat.ofHom
      (infinityChartRingHom K
        (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
        (Order13MixedQuadraticOverlapCoordinates.zCoordinate K))) ≫
    Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2))
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one

private theorem ordinaryChartToProjectiveLine_toSpecZero :
    ordinaryChartToProjectiveLine K ≫
        Proj.toSpecZero (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap K (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)).comp
          (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K).symm.toRingHom)) := by
  unfold ordinaryChartToProjectiveLine Order13DyadicMixedQuadraticCharts.ordinaryScheme
  rw [Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply]
  change standardChartRingHom K
      (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)
      (HomogeneousLocalization.fromZeroRingHom
        (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (1 : Fin 2)))
        (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K r)) =
    algebraMap K (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K) r
  simp only [standardChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K
      (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.xCoordinate K))
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [standardCoordinatePolynomialHom_X_one]; simp) 0
  convert h using 1
  · congr 1
  · simp [standardCoordinatePolynomialHom]

private theorem reciprocalChartToProjectiveLine_toSpecZero :
    reciprocalChartToProjectiveLine K ≫
        Proj.toSpecZero (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap K
            (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)).comp
          (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K).symm.toRingHom)) := by
  unfold reciprocalChartToProjectiveLine Order13DyadicMixedQuadraticCharts.reciprocalScheme
  rw [Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply]
  change infinityChartRingHom K
      (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)
      (HomogeneousLocalization.fromZeroRingHom
        (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (0 : Fin 2)))
        (Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K r)) =
    algebraMap K (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K) r
  simp only [infinityChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom K
      (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.zCoordinate K))
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) 0
  convert h using 1
  · congr 1
  · simp [inverseCoordinatePolynomialHom]

private theorem scalar_spec_comp (A D : Type u) [CommRing A] [Algebra K A] [CommRing D]
    (e : K ≃+* D) :
    Spec.map (CommRingCat.ofHom ((algebraMap K A).comp e.symm.toRingHom)) ≫
      Spec.map e.toCommRingCatIso.hom = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  rw [← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp

@[simp, reassoc]
theorem ordinaryChartToProjectiveLine_structureMap :
    ordinaryChartToProjectiveLine K ≫ Order13MixedQuadraticProjectiveLineOriginal20261019.structureMap K =
      Order13DyadicMixedQuadraticCharts.ordinaryToBase K := by
  let D := Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0
  let e := Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K
  have ht : (ordinaryChartToProjectiveLine K ≫ Proj.toSpecZero (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)) ≫
      Spec.map e.toCommRingCatIso.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap K (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)).comp e.symm.toRingHom)) ≫
        Spec.map e.toCommRingCatIso.hom :=
    congrArg (fun t : Order13DyadicMixedQuadraticCharts.ordinaryScheme K ⟶ Spec (.of D) => t ≫ Spec.map e.toCommRingCatIso.hom)
      (ordinaryChartToProjectiveLine_toSpecZero K)
  change ordinaryChartToProjectiveLine K ≫
      (Proj.toSpecZero (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K) ≫ Spec.map e.toCommRingCatIso.hom) = _
  have hlast : Spec.map (CommRingCat.ofHom ((algebraMap K (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)).comp e.symm.toRingHom)) ≫
      Spec.map e.toCommRingCatIso.hom = Order13DyadicMixedQuadraticCharts.ordinaryToBase K := scalar_spec_comp K (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K) D e
  exact (Category.assoc (ordinaryChartToProjectiveLine K)
    (Proj.toSpecZero (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)) (Spec.map e.toCommRingCatIso.hom)).symm.trans
      (ht.trans hlast)



@[simp, reassoc]
theorem reciprocalChartToProjectiveLine_structureMap :
    reciprocalChartToProjectiveLine K ≫ Order13MixedQuadraticProjectiveLineOriginal20261019.structureMap K =
      Order13DyadicMixedQuadraticCharts.reciprocalToBase K := by
  let D := Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K 0
  let e := Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv K
  have ht : (reciprocalChartToProjectiveLine K ≫ Proj.toSpecZero (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)) ≫
      Spec.map e.toCommRingCatIso.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap K (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)).comp e.symm.toRingHom)) ≫
        Spec.map e.toCommRingCatIso.hom :=
    congrArg (fun t : Order13DyadicMixedQuadraticCharts.reciprocalScheme K ⟶ Spec (.of D) => t ≫ Spec.map e.toCommRingCatIso.hom)
      (reciprocalChartToProjectiveLine_toSpecZero K)
  change reciprocalChartToProjectiveLine K ≫
      (Proj.toSpecZero (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K) ≫ Spec.map e.toCommRingCatIso.hom) = _
  have hlast : Spec.map (CommRingCat.ofHom ((algebraMap K (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)).comp e.symm.toRingHom)) ≫
      Spec.map e.toCommRingCatIso.hom = Order13DyadicMixedQuadraticCharts.reciprocalToBase K := scalar_spec_comp K (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K) D e
  exact (Category.assoc (reciprocalChartToProjectiveLine K)
    (Proj.toSpecZero (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)) (Spec.map e.toCommRingCatIso.hom)).symm.trans
      (ht.trans hlast)



theorem ordinaryChartToProjectiveLine_preimage_standardAffineOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K = ⊤ := by
  rw [show Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K =
      (Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one).opensRange by
    exact (Proj.opensRange_awayι _ _
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one).symm]
  unfold ordinaryChartToProjectiveLine Order13DyadicMixedQuadraticCharts.ordinaryScheme
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange]
  simp

private theorem inverseAffineCoordinateAway_eq_isLocalizationElem :
    Order13MixedQuadraticProjectiveLineOriginal20261019.inverseAffineCoordinateAway K =
      HomogeneousLocalization.Away.isLocalizationElem
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K)
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) := by
  simp [Order13MixedQuadraticProjectiveLineOriginal20261019.inverseAffineCoordinateAway,
    HomogeneousLocalization.Away.isLocalizationElem]

theorem reciprocalChartToProjectiveLine_preimage_standardAffineOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K =
      PrimeSpectrum.basicOpen
        (Order13MixedQuadraticOverlapCoordinates.zCoordinate K) := by
  unfold reciprocalChartToProjectiveLine
    Order13DyadicMixedQuadraticCharts.reciprocalScheme
  change (Spec.map (CommRingCat.ofHom
      (infinityChartRingHom K
        (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
        (Order13MixedQuadraticOverlapCoordinates.zCoordinate K))) ≫
      Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one) ⁻¹ᵁ
      Proj.basicOpen (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) = _
  rw [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen
    (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
    (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one
    (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  rw [← inverseAffineCoordinateAway_eq_isLocalizationElem K]
  exact infinityChartRingHom_inverseAffineCoordinateAway K
    (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
    (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)

theorem reciprocalChartToProjectiveLine_preimage_infinityAffineOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K = ⊤ := by
  rw [show Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K =
      (Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one).opensRange by
    exact (Proj.opensRange_awayι _ _
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one).symm]
  unfold reciprocalChartToProjectiveLine
    Order13DyadicMixedQuadraticCharts.reciprocalScheme
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange]
  simp

private theorem affineCoordinateAway_eq_isLocalizationElem :
    Order13MixedQuadraticProjectiveLineOriginal20261019.affineCoordinateAway K =
      HomogeneousLocalization.Away.isLocalizationElem
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K)
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) := by
  simp [Order13MixedQuadraticProjectiveLineOriginal20261019.affineCoordinateAway,
    HomogeneousLocalization.Away.isLocalizationElem]

theorem ordinaryChartToProjectiveLine_preimage_infinityAffineOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K =
      PrimeSpectrum.basicOpen
        (Order13MixedQuadraticOverlapCoordinates.xCoordinate K) := by
  unfold ordinaryChartToProjectiveLine
  change (Spec.map (CommRingCat.ofHom
      (standardChartRingHom K
        (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
        (Order13MixedQuadraticOverlapCoordinates.xCoordinate K))) ≫
      Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one) ⁻¹ᵁ
      Proj.basicOpen (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) = _
  rw [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen
    (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
    (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one
    (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  rw [← affineCoordinateAway_eq_isLocalizationElem K]
  exact standardChartRingHom_affineCoordinateAway K
    (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
    (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)

private theorem ordinary_ne_reciprocal :
    (Order13MixedQuadraticGluedCurve.Chart.ordinary :
      Order13MixedQuadraticGluedCurve.Chart.{u}) ≠
      Order13MixedQuadraticGluedCurve.Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary :
    (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
      Order13MixedQuadraticGluedCurve.Chart.{u}) ≠
      Order13MixedQuadraticGluedCurve.Chart.ordinary := by
  intro h
  cases h

private theorem ordinaryReciprocalOverlapInclusion_eq :
    Order13MixedQuadraticGluedCurve.overlapInclusion K
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u}) ordinary_ne_reciprocal =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
          (Order13MixedQuadraticOverlapCoordinates.OrdinaryOverlapRing K))) := by
  rfl

private theorem reciprocalOrdinaryOverlapInclusion_eq :
    Order13MixedQuadraticGluedCurve.overlapInclusion K
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u}) reciprocal_ne_ordinary =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
          (Order13MixedQuadraticOverlapCoordinates.ReciprocalOverlapRing K))) := by
  rfl

private theorem ordinaryReciprocalOverlapTransition_eq :
    Order13MixedQuadraticGluedCurve.overlapTransition K
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u}) ordinary_ne_reciprocal =
      (Order13MixedQuadraticGluedCurve.overlapSchemeIso K).hom := by
  rfl

private theorem reciprocalOrdinaryOverlapTransition_eq :
    Order13MixedQuadraticGluedCurve.overlapTransition K
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u}) reciprocal_ne_ordinary =
      (Order13MixedQuadraticGluedCurve.overlapSchemeIso K).inv := by
  rfl

private instance reciprocalOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (Order13MixedQuadraticGluedCurve.overlapInclusion K
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        reciprocal_ne_ordinary) := by
  rw [reciprocalOrdinaryOverlapInclusion_eq]
  exact IsOpenImmersion.of_isLocalization
    (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)

private noncomputable abbrev reciprocalOverlapOpen :
    (Order13MixedQuadraticGluedCurve.chartScheme K
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})).Opens :=
  PrimeSpectrum.basicOpen (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)

private theorem reciprocalOverlapInclusion_opensRange :
    (Order13MixedQuadraticGluedCurve.overlapInclusion K
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})
      reciprocal_ne_ordinary).opensRange =
        reciprocalOverlapOpen K := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (Order13MixedQuadraticOverlapCoordinates.ReciprocalOverlapRing K)
    (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)

private instance reciprocalGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((Order13MixedQuadraticGluedCurve.glueData K).f
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})) :=
  (Order13MixedQuadraticGluedCurve.glueData K).f_open _ _

private theorem reciprocalChartToProjectiveLine_preimage_standardAffineOpen_eq_overlapOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K =
      reciprocalOverlapOpen K := by
  exact reciprocalChartToProjectiveLine_preimage_standardAffineOpen K

private theorem reciprocalGlueOverlap_opensRange :
    ((Order13MixedQuadraticGluedCurve.glueData K).f
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})).opensRange =
      reciprocalOverlapOpen K := by
  dsimp [Order13MixedQuadraticGluedCurve.glueData,
    Order13MixedQuadraticGluedCurve.categoricalGlueData,
    CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f',
    ordinary_ne_reciprocal, reciprocal_ne_ordinary]
  simp only [dif_neg reciprocal_ne_ordinary]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact reciprocalOverlapInclusion_opensRange K

private theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange :
    Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
        (Order13MixedQuadraticGluedCurve.ordinaryChartMap K).opensRange =
      ((Order13MixedQuadraticGluedCurve.glueData K).f
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (Order13MixedQuadraticGluedCurve.reciprocalChartMap K q ∈
      (Order13MixedQuadraticGluedCurve.ordinaryChartMap K).opensRange) ↔
    q ∈ ((Order13MixedQuadraticGluedCurve.glueData K).f
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((Order13MixedQuadraticGluedCurve.glueData K).ι_eq_iff
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((Order13MixedQuadraticGluedCurve.glueData K).t
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u}) ≫
        (Order13MixedQuadraticGluedCurve.glueData K).f
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((Order13MixedQuadraticGluedCurve.glueData K).glue_condition
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u}))

private theorem reciprocalOverlapOpen_eq_chartMap_preimage :
    reciprocalOverlapOpen K =
      Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
        (Order13MixedQuadraticGluedCurve.ordinaryChartMap K).opensRange :=
  (reciprocalGlueOverlap_opensRange K).symm.trans
    (reciprocalChartMap_preimage_ordinaryChartMap_opensRange K).symm

/-- On the reciprocal chart, the overlap with the ordinary chart is exactly
the principal open where the reciprocal coordinate `z` is nonzero. -/
@[simp]
theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen :
    Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
        (Order13MixedQuadraticGluedCurve.ordinaryChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (Order13MixedQuadraticOverlapCoordinates.zCoordinate K) := by
  exact (reciprocalOverlapOpen_eq_chartMap_preimage K).symm

private instance ordinaryOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (Order13MixedQuadraticGluedCurve.overlapInclusion K
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        ordinary_ne_reciprocal) := by
  rw [ordinaryReciprocalOverlapInclusion_eq]
  exact IsOpenImmersion.of_isLocalization
    (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)

private noncomputable abbrev ordinaryOverlapOpen :
    (Order13MixedQuadraticGluedCurve.chartScheme K
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})).Opens :=
  PrimeSpectrum.basicOpen (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)

private theorem ordinaryOverlapInclusion_opensRange :
    (Order13MixedQuadraticGluedCurve.overlapInclusion K
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})
      ordinary_ne_reciprocal).opensRange =
        ordinaryOverlapOpen K := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (Order13MixedQuadraticOverlapCoordinates.OrdinaryOverlapRing K)
    (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)

private instance ordinaryGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((Order13MixedQuadraticGluedCurve.glueData K).f
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})) :=
  (Order13MixedQuadraticGluedCurve.glueData K).f_open _ _

private theorem ordinaryChartToProjectiveLine_preimage_infinityAffineOpen_eq_overlapOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K =
      ordinaryOverlapOpen K := by
  exact ordinaryChartToProjectiveLine_preimage_infinityAffineOpen K

private theorem ordinaryGlueOverlap_opensRange :
    ((Order13MixedQuadraticGluedCurve.glueData K).f
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})).opensRange =
      ordinaryOverlapOpen K := by
  dsimp [Order13MixedQuadraticGluedCurve.glueData,
    Order13MixedQuadraticGluedCurve.categoricalGlueData,
    CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f',
    ordinary_ne_reciprocal, reciprocal_ne_ordinary]
  simp only [dif_neg ordinary_ne_reciprocal]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact ordinaryOverlapInclusion_opensRange K

private theorem ordinaryChartMap_preimage_reciprocalChartMap_opensRange :
    Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
        (Order13MixedQuadraticGluedCurve.reciprocalChartMap K).opensRange =
      ((Order13MixedQuadraticGluedCurve.glueData K).f
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (Order13MixedQuadraticGluedCurve.ordinaryChartMap K q ∈
      (Order13MixedQuadraticGluedCurve.reciprocalChartMap K).opensRange) ↔
    q ∈ ((Order13MixedQuadraticGluedCurve.glueData K).f
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((Order13MixedQuadraticGluedCurve.glueData K).ι_eq_iff
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((Order13MixedQuadraticGluedCurve.glueData K).t
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u}) ≫
        (Order13MixedQuadraticGluedCurve.glueData K).f
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((Order13MixedQuadraticGluedCurve.glueData K).glue_condition
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u}))

private theorem ordinaryOverlapOpen_eq_chartMap_preimage :
    ordinaryOverlapOpen K =
      Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
        (Order13MixedQuadraticGluedCurve.reciprocalChartMap K).opensRange :=
  (ordinaryGlueOverlap_opensRange K).symm.trans
    (ordinaryChartMap_preimage_reciprocalChartMap_opensRange K).symm

/-- On the ordinary chart, the overlap with the reciprocal chart is exactly
the principal open where `x` is nonzero. -/
@[simp]
theorem ordinaryChartMap_preimage_reciprocalChartMap_opensRange_eq_basicOpen :
    Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
        (Order13MixedQuadraticGluedCurve.reciprocalChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (Order13MixedQuadraticOverlapCoordinates.xCoordinate K) := by
  exact (ordinaryOverlapOpen_eq_chartMap_preimage K).symm

private theorem ordinary_reciprocal_hyperelliptic_compatible :
    Order13MixedQuadraticGluedCurve.overlapInclusion K
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K =
      Order13MixedQuadraticGluedCurve.overlapTransition K
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        Order13MixedQuadraticGluedCurve.overlapInclusion K
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        reciprocalChartToProjectiveLine K := by
  let A := Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K
  let B := Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K
  let LA := Order13MixedQuadraticOverlapCoordinates.OrdinaryOverlapRing K
  let LB := Order13MixedQuadraticOverlapCoordinates.ReciprocalOverlapRing K
  let x : LA := algebraMap A LA (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)
  let z : LA := IsLocalization.Away.invSelf
    (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)
  let ordinaryLocalization : A →ₐ[K] LA :=
    IsScalarTower.toAlgHom K A LA
  let reciprocalToOrdinary : B →ₐ[K] LA :=
    (Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinary K).comp
      (IsScalarTower.toAlgHom K B LB)
  have hxz : x * z = 1 := by
    exact IsLocalization.Away.mul_invSelf
      (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)
  have hz : reciprocalToOrdinary
      (Order13MixedQuadraticOverlapCoordinates.zCoordinate K) = z := by
    change Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinary K
      (algebraMap B LB (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)) = z
    rw [Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinary_algebraMap,
      Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinaryBase_z]
    rfl
  have hordinary := standardChartRingHom_naturality K A LA
    ordinaryLocalization (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)
  have hreciprocal := infinityChartRingHom_naturality K B LA
    reciprocalToOrdinary (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)
  rw [hz] at hreciprocal
  calc
    Order13MixedQuadraticGluedCurve.overlapInclusion K
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K =
      Spec.map (CommRingCat.ofHom (standardChartRingHom K LA x)) ≫
        Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2))
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one := by
      rw [ordinaryReciprocalOverlapInclusion_eq]
      unfold ordinaryChartToProjectiveLine Order13DyadicMixedQuadraticCharts.ordinaryScheme
      change Spec.map (CommRingCat.ofHom (algebraMap A LA)) ≫
          (Spec.map (CommRingCat.ofHom
            (standardChartRingHom K A
              (Order13MixedQuadraticOverlapCoordinates.xCoordinate K))) ≫
            Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
              (MvPolynomial.X (1 : Fin 2))
              (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one) =
        Spec.map (CommRingCat.ofHom (standardChartRingHom K LA x)) ≫
          Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))
            (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      exact hordinary
    _ = Spec.map (CommRingCat.ofHom (infinityChartRingHom K LA z)) ≫
        Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2))
          (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one :=
      projectiveLine_chart_maps_eq K LA x z hxz
    _ = Order13MixedQuadraticGluedCurve.overlapTransition K
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        Order13MixedQuadraticGluedCurve.overlapInclusion K
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        reciprocalChartToProjectiveLine K := by
      rw [ordinaryReciprocalOverlapTransition_eq,
        Order13MixedQuadraticGluedCurve.overlapSchemeIso_hom,
        reciprocalOrdinaryOverlapInclusion_eq]
      unfold reciprocalChartToProjectiveLine
        Order13DyadicMixedQuadraticCharts.reciprocalScheme
      change Spec.map (CommRingCat.ofHom (infinityChartRingHom K LA z)) ≫
          Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))
            (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one =
        Spec.map (CommRingCat.ofHom
          (Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinary K).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B LB)) ≫
          (Spec.map (CommRingCat.ofHom
            (infinityChartRingHom K B
              (Order13MixedQuadraticOverlapCoordinates.zCoordinate K))) ≫
            Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
              (MvPolynomial.X (0 : Fin 2))
              (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one)
      symm
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      exact hreciprocal

private theorem reciprocal_ordinary_hyperelliptic_compatible :
    Order13MixedQuadraticGluedCurve.overlapInclusion K
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        reciprocalChartToProjectiveLine K =
      Order13MixedQuadraticGluedCurve.overlapTransition K
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        Order13MixedQuadraticGluedCurve.overlapInclusion K
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K := by
  let l := Order13MixedQuadraticGluedCurve.overlapInclusion K
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u}) reciprocal_ne_ordinary ≫
    reciprocalChartToProjectiveLine K
  calc
    l = (Order13MixedQuadraticGluedCurve.overlapSchemeIso K).inv ≫
        (Order13MixedQuadraticGluedCurve.overlapSchemeIso K).hom ≫ l := by
      rw [(Order13MixedQuadraticGluedCurve.overlapSchemeIso K).inv_hom_id_assoc]
    _ = (Order13MixedQuadraticGluedCurve.overlapSchemeIso K).inv ≫
        Order13MixedQuadraticGluedCurve.overlapInclusion K
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K := by
      rw [ordinary_reciprocal_hyperelliptic_compatible K]
      rfl
    _ = Order13MixedQuadraticGluedCurve.overlapTransition K
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        Order13MixedQuadraticGluedCurve.overlapInclusion K
          (Order13MixedQuadraticGluedCurve.Chart.ordinary :
            Order13MixedQuadraticGluedCurve.Chart.{u})
          (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
            Order13MixedQuadraticGluedCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K := by
      rw [reciprocalOrdinaryOverlapTransition_eq]

/-- The chartwise hyperelliptic maps before descent through the gluing. -/
noncomputable def chartToProjectiveLine :
    ∀ i : Order13MixedQuadraticGluedCurve.Chart.{u},
      Order13MixedQuadraticGluedCurve.chartScheme K i ⟶
        Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K
  | .ordinary => ordinaryChartToProjectiveLine K
  | .reciprocal => reciprocalChartToProjectiveLine K

/-- The hyperelliptic map descended from the two checked chart maps. -/
noncomputable def gluedHyperellipticMap :
    Order13MixedQuadraticGluedCurve.curveScheme K ⟶
      Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (Order13MixedQuadraticGluedCurve.glueData K)
  exact Limits.Multicoequalizer.desc
    (Order13MixedQuadraticGluedCurve.glueData K).toGlueData.diagram
    (Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K) (chartToProjectiveLine K) (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [Order13MixedQuadraticGluedCurve.glueData,
          Order13MixedQuadraticGluedCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          Limits.MultispanShape.prod]
        simp
      · dsimp [Order13MixedQuadraticGluedCurve.glueData,
          Order13MixedQuadraticGluedCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact ordinary_reciprocal_hyperelliptic_compatible K
      · dsimp [Order13MixedQuadraticGluedCurve.glueData,
          Order13MixedQuadraticGluedCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact reciprocal_ordinary_hyperelliptic_compatible K
      · dsimp [Order13MixedQuadraticGluedCurve.glueData,
          Order13MixedQuadraticGluedCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          Limits.MultispanShape.prod]
        simp)

@[simp, reassoc]
theorem ordinaryChartMap_gluedHyperellipticMap :
    Order13MixedQuadraticGluedCurve.ordinaryChartMap K ≫
        gluedHyperellipticMap K =
      ordinaryChartToProjectiveLine K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (Order13MixedQuadraticGluedCurve.glueData K)
  unfold Order13MixedQuadraticGluedCurve.ordinaryChartMap
    gluedHyperellipticMap
  apply Limits.Multicoequalizer.π_desc

@[simp, reassoc]
theorem reciprocalChartMap_gluedHyperellipticMap :
    Order13MixedQuadraticGluedCurve.reciprocalChartMap K ≫
        gluedHyperellipticMap K =
      reciprocalChartToProjectiveLine K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (Order13MixedQuadraticGluedCurve.glueData K)
  unfold Order13MixedQuadraticGluedCurve.reciprocalChartMap
    gluedHyperellipticMap
  apply Limits.Multicoequalizer.π_desc

theorem gluedHyperellipticMap_preimage_standardAffineOpen :
    gluedHyperellipticMap K ⁻¹ᵁ
        Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K =
      (Order13MixedQuadraticGluedCurve.ordinaryChartMap K).opensRange := by
  have hordinary :
      Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K =
        Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
          (Order13MixedQuadraticGluedCurve.ordinaryChartMap K).opensRange := by
    calc
      Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K =
          (Order13MixedQuadraticGluedCurve.ordinaryChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K := rfl
      _ = ordinaryChartToProjectiveLine K ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K := by
          rw [ordinaryChartMap_gluedHyperellipticMap]
      _ = ⊤ := ordinaryChartToProjectiveLine_preimage_standardAffineOpen K
      _ = Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
          (Order13MixedQuadraticGluedCurve.ordinaryChartMap K).opensRange := by
        rw [Scheme.Hom.preimage_opensRange]
  have hreciprocal :
      Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K =
        Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
          (Order13MixedQuadraticGluedCurve.ordinaryChartMap K).opensRange := by
    calc
      Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K =
          (Order13MixedQuadraticGluedCurve.reciprocalChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K := rfl
      _ = reciprocalChartToProjectiveLine K ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K := by
          rw [reciprocalChartMap_gluedHyperellipticMap]
      _ = reciprocalOverlapOpen K :=
        reciprocalChartToProjectiveLine_preimage_standardAffineOpen_eq_overlapOpen K
      _ = Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
          (Order13MixedQuadraticGluedCurve.ordinaryChartMap K).opensRange :=
        reciprocalOverlapOpen_eq_chartMap_preimage K
  apply TopologicalSpace.Opens.ext
  ext p
  obtain ⟨i, q, rfl⟩ :=
    (Order13MixedQuadraticGluedCurve.glueData K).ι_jointly_surjective p
  rcases i with (_ | _)
  · exact SetLike.ext_iff.mp hordinary q
  · exact SetLike.ext_iff.mp hreciprocal q

theorem gluedHyperellipticMap_preimage_infinityAffineOpen :
    gluedHyperellipticMap K ⁻¹ᵁ
        Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K =
      (Order13MixedQuadraticGluedCurve.reciprocalChartMap K).opensRange := by
  have hordinary :
      Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K =
        Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
          (Order13MixedQuadraticGluedCurve.reciprocalChartMap K).opensRange := by
    calc
      Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K =
          (Order13MixedQuadraticGluedCurve.ordinaryChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K := rfl
      _ = ordinaryChartToProjectiveLine K ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K := by
          rw [ordinaryChartMap_gluedHyperellipticMap]
      _ = ordinaryOverlapOpen K :=
        ordinaryChartToProjectiveLine_preimage_infinityAffineOpen_eq_overlapOpen K
      _ = Order13MixedQuadraticGluedCurve.ordinaryChartMap K ⁻¹ᵁ
          (Order13MixedQuadraticGluedCurve.reciprocalChartMap K).opensRange :=
        ordinaryOverlapOpen_eq_chartMap_preimage K
  have hreciprocal :
      Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K =
        Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
          (Order13MixedQuadraticGluedCurve.reciprocalChartMap K).opensRange := by
    calc
      Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K =
          (Order13MixedQuadraticGluedCurve.reciprocalChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K := rfl
      _ = reciprocalChartToProjectiveLine K ⁻¹ᵁ
            Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K := by
          rw [reciprocalChartMap_gluedHyperellipticMap]
      _ = ⊤ := reciprocalChartToProjectiveLine_preimage_infinityAffineOpen K
      _ = Order13MixedQuadraticGluedCurve.reciprocalChartMap K ⁻¹ᵁ
          (Order13MixedQuadraticGluedCurve.reciprocalChartMap K).opensRange := by
        rw [Scheme.Hom.preimage_opensRange]
  apply TopologicalSpace.Opens.ext
  ext p
  obtain ⟨i, q, rfl⟩ :=
    (Order13MixedQuadraticGluedCurve.glueData K).ι_jointly_surjective p
  rcases i with (_ | _)
  · exact SetLike.ext_iff.mp hordinary q
  · exact SetLike.ext_iff.mp hreciprocal q

private noncomputable abbrev projectiveLineChartScheme :
    Order13MixedQuadraticGluedCurve.Chart.{u} → Scheme
  | .ordinary => Spec (.of <|
      HomogeneousLocalization.Away (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))
  | .reciprocal => Spec (.of <|
      HomogeneousLocalization.Away (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)))

private noncomputable def projectiveLineChartMap :
    ∀ i : Order13MixedQuadraticGluedCurve.Chart.{u},
      projectiveLineChartScheme K i ⟶ Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K
  | .ordinary => Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one
  | .reciprocal => Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2))
      (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one

private instance projectiveLineChartMap_isOpenImmersion
    (i : Order13MixedQuadraticGluedCurve.Chart.{u}) :
    IsOpenImmersion (projectiveLineChartMap K i) := by
  rcases i with (_ | _)
  · change IsOpenImmersion
      (Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one)
    infer_instance
  · change IsOpenImmersion
      (Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one)
    infer_instance

private theorem projectiveLineChartMap_ordinary_opensRange :
    (projectiveLineChartMap K
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})).opensRange =
      Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K := by
  exact Proj.opensRange_awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
    (MvPolynomial.X (1 : Fin 2))
    (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one

private theorem projectiveLineChartMap_reciprocal_opensRange :
    (projectiveLineChartMap K
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})).opensRange =
      Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K := by
  exact Proj.opensRange_awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
    (MvPolynomial.X (0 : Fin 2))
    (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one

private noncomputable def projectiveLineChartCover :
    (Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K).OpenCover where
  I₀ := Order13MixedQuadraticGluedCurve.Chart.{u}
  X := projectiveLineChartScheme K
  f := projectiveLineChartMap K
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      have hp : p ∈ Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K ⊔
          Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K := by
        rw [Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen_sup_infinityAffineOpen_eq_top]
        trivial
      change p ∈ (Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K :
          Set (Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K)) ∪
        (Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K :
          Set (Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K)) at hp
      rcases hp with hp | hp
      · refine ⟨Order13MixedQuadraticGluedCurve.Chart.ordinary, ?_⟩
        change p ∈ (Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))
            (Order13MixedQuadraticProjectiveLineOriginal20261019.X_one_mem_degree_one K) zero_lt_one).opensRange
        rw [Proj.opensRange_awayι]
        exact hp
      · refine ⟨Order13MixedQuadraticGluedCurve.Chart.reciprocal, ?_⟩
        change p ∈ (Proj.awayι (Order13MixedQuadraticProjectiveLineOriginal20261019.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))
            (Order13MixedQuadraticProjectiveLineOriginal20261019.X_zero_mem_degree_one K) zero_lt_one).opensRange
        rw [Proj.opensRange_awayι]
        exact hp
    · intro i
      exact projectiveLineChartMap_isOpenImmersion K i

private noncomputable def ordinaryChartFiniteMap :
    Order13DyadicMixedQuadraticCharts.ordinaryScheme K ⟶
      projectiveLineChartScheme K
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u}) :=
  Spec.map (CommRingCat.ofHom
    (standardChartRingHom K
      (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.xCoordinate K)))

private noncomputable def reciprocalChartFiniteMap :
    Order13DyadicMixedQuadraticCharts.reciprocalScheme K ⟶
      projectiveLineChartScheme K
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u}) :=
  Spec.map (CommRingCat.ofHom
    (infinityChartRingHom K
      (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.zCoordinate K)))

private theorem ordinaryChartSquare_isPullback :
    IsPullback (ordinaryChartFiniteMap K)
      (Order13MixedQuadraticGluedCurve.ordinaryChartMap K)
      (projectiveLineChartMap K
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u}))
      (gluedHyperellipticMap K) := by
  letI : IsOpenImmersion
      (projectiveLineChartMap K
        (Order13MixedQuadraticGluedCurve.Chart.ordinary :
          Order13MixedQuadraticGluedCurve.Chart.{u})) :=
    projectiveLineChartMap_isOpenImmersion K _
  apply IsOpenImmersion.isPullback
  · rw [ordinaryChartMap_gluedHyperellipticMap]
    rfl
  · rw [projectiveLineChartMap_ordinary_opensRange]
    exact gluedHyperellipticMap_preimage_standardAffineOpen K

private theorem reciprocalChartSquare_isPullback :
    IsPullback (reciprocalChartFiniteMap K)
      (Order13MixedQuadraticGluedCurve.reciprocalChartMap K)
      (projectiveLineChartMap K
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u}))
      (gluedHyperellipticMap K) := by
  letI : IsOpenImmersion
      (projectiveLineChartMap K
        (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
          Order13MixedQuadraticGluedCurve.Chart.{u})) :=
    projectiveLineChartMap_isOpenImmersion K _
  apply IsOpenImmersion.isPullback
  · rw [reciprocalChartMap_gluedHyperellipticMap]
    rfl
  · rw [projectiveLineChartMap_reciprocal_opensRange]
    exact gluedHyperellipticMap_preimage_infinityAffineOpen K

/-- The morphism property underlying `IsFinite`, named explicitly so that
Mathlib's affine-local framework can elaborate it at the default transparency
setting. -/
private abbrev finiteMorphismProperty : MorphismProperty Scheme :=
  fun {_ _} f => IsFinite f

private instance finiteMorphismProperty_hasAffineProperty :
    HasAffineProperty finiteMorphismProperty (affineAnd RingHom.Finite) := by
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away
    RingHom.finite_ofLocalizationSpan]
  simp [finiteMorphismProperty, isFinite_iff]

private theorem ordinaryCoverPullbackHom_isFinite :
    IsFinite ((projectiveLineChartCover K).pullbackHom
      (gluedHyperellipticMap K)
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})) := by
  let h := ordinaryChartSquare_isPullback K
  change finiteMorphismProperty (Limits.pullback.snd (gluedHyperellipticMap K)
    (projectiveLineChartMap K
      (Order13MixedQuadraticGluedCurve.Chart.ordinary :
        Order13MixedQuadraticGluedCurve.Chart.{u})))
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := finiteMorphismProperty) h.flip.isoPullback.hom,
    h.flip.isoPullback_hom_snd]
  change IsFinite (Spec.map (CommRingCat.ofHom
    (standardChartRingHom K
      (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.xCoordinate K))))
  rw [IsFinite.SpecMap_iff]
  exact standardChartRingHom_finite K

private theorem reciprocalCoverPullbackHom_isFinite :
    IsFinite ((projectiveLineChartCover K).pullbackHom
      (gluedHyperellipticMap K)
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})) := by
  let h := reciprocalChartSquare_isPullback K
  change finiteMorphismProperty (Limits.pullback.snd (gluedHyperellipticMap K)
    (projectiveLineChartMap K
      (Order13MixedQuadraticGluedCurve.Chart.reciprocal :
        Order13MixedQuadraticGluedCurve.Chart.{u})))
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := finiteMorphismProperty) h.flip.isoPullback.hom,
    h.flip.isoPullback_hom_snd]
  change IsFinite (Spec.map (CommRingCat.ofHom
    (infinityChartRingHom K
      (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)
      (Order13MixedQuadraticOverlapCoordinates.zCoordinate K))))
  rw [IsFinite.SpecMap_iff]
  exact infinityChartRingHom_finite K

noncomputable instance gluedHyperellipticMap_isFinite :
    IsFinite (gluedHyperellipticMap K) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (P := finiteMorphismProperty) (projectiveLineChartCover K)
  intro i
  rcases i with (_ | _)
  · exact ordinaryCoverPullbackHom_isFinite K
  · exact reciprocalCoverPullbackHom_isFinite K

end ChartMorphisms

end MazurTransfer.Order13MixedQuadraticHyperellipticMap

namespace MazurTransfer.Order13MixedQuadraticProperCurve
open Order13MixedQuadraticGluedCurve

open CategoryTheory
open _root_.AlgebraicGeometry
open MazurTransfer MazurTorsion

universe u

variable (K : Type u) [CommRing K]

/-- The degree-two coordinate map from the glued order-thirteen curve to
Tau Ceti's concrete projective line. -/
noncomputable def hyperellipticMap :
    curveScheme K ⟶ Order13MixedQuadraticProjectiveLineOriginal20261019.scheme K :=
  MazurTransfer.Order13MixedQuadraticHyperellipticMap.gluedHyperellipticMap K

@[simp, reassoc]
theorem ordinaryChartMap_hyperellipticMap :
    ordinaryChartMap K ≫ hyperellipticMap K =
      MazurTransfer.Order13MixedQuadraticHyperellipticMap.ordinaryChartToProjectiveLine K := by
  exact MazurTransfer.Order13MixedQuadraticHyperellipticMap.ordinaryChartMap_gluedHyperellipticMap K

@[simp, reassoc]
theorem reciprocalChartMap_hyperellipticMap :
    reciprocalChartMap K ≫ hyperellipticMap K =
      MazurTransfer.Order13MixedQuadraticHyperellipticMap.reciprocalChartToProjectiveLine K := by
  exact MazurTransfer.Order13MixedQuadraticHyperellipticMap.reciprocalChartMap_gluedHyperellipticMap K

@[simp]
theorem hyperellipticMap_preimage_standardAffineOpen :
    hyperellipticMap K ⁻¹ᵁ Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen K =
      (ordinaryChartMap K).opensRange :=
  MazurTransfer.Order13MixedQuadraticHyperellipticMap.gluedHyperellipticMap_preimage_standardAffineOpen K

@[simp]
theorem hyperellipticMap_preimage_infinityAffineOpen :
    hyperellipticMap K ⁻¹ᵁ Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffineOpen K =
      (reciprocalChartMap K).opensRange :=
  MazurTransfer.Order13MixedQuadraticHyperellipticMap.gluedHyperellipticMap_preimage_infinityAffineOpen K

noncomputable instance hyperellipticMap_isFinite :
    IsFinite (hyperellipticMap K) :=
  MazurTransfer.Order13MixedQuadraticHyperellipticMap.gluedHyperellipticMap_isFinite K

/-- The structure morphism obtained by gluing the affine algebra maps is the
finite hyperelliptic map followed by the structure morphism of projective
line. -/
theorem curveToBase_eq_hyperellipticMap_comp_structureMap :
    curveToBase K =
      hyperellipticMap K ≫ Order13MixedQuadraticProjectiveLineOriginal20261019.structureMap K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  apply Limits.Multicoequalizer.hom_ext
  intro i
  rcases i with (_ | _)
  · change ordinaryChartMap K ≫ curveToBase K =
      ordinaryChartMap K ≫ hyperellipticMap K ≫
        Order13MixedQuadraticProjectiveLineOriginal20261019.structureMap K
    rw [ordinaryChartMap_curveToBase,
      ordinaryChartMap_hyperellipticMap_assoc,
      MazurTransfer.Order13MixedQuadraticHyperellipticMap.ordinaryChartToProjectiveLine_structureMap]
  · change reciprocalChartMap K ≫ curveToBase K =
      reciprocalChartMap K ≫ hyperellipticMap K ≫
        Order13MixedQuadraticProjectiveLineOriginal20261019.structureMap K
    rw [reciprocalChartMap_curveToBase,
      reciprocalChartMap_hyperellipticMap_assoc,
      MazurTransfer.Order13MixedQuadraticHyperellipticMap.reciprocalChartToProjectiveLine_structureMap]

/-- The actual glued order-thirteen curve is proper over its coefficient
ring.  This is the first downstream consumer of the structural-morphism
comparison above. -/
theorem curveToBase_isProper : IsProper (curveToBase K) := by
  letI : IsProper (Order13MixedQuadraticProjectiveLineOriginal20261019.structureMap K) :=
    Order13MixedQuadraticProjectiveLineOriginal20261019.structureMap_isProper K
  rw [curveToBase_eq_hyperellipticMap_comp_structureMap]
  infer_instance


end MazurTransfer.Order13MixedQuadraticProperCurve
#print axioms MazurTransfer.Order13MixedQuadraticHyperellipticMap.gluedHyperellipticMap_isFinite
#print axioms MazurTransfer.Order13MixedQuadraticProperCurve.curveToBase_eq_hyperellipticMap_comp_structureMap
#print axioms MazurTransfer.Order13MixedQuadraticProperCurve.curveToBase_isProper

end


