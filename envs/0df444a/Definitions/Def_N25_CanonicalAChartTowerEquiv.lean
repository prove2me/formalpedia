-- Prove2me | Definitions.Def_N25_CanonicalAChartTowerEquiv
-- name    : N25_CanonicalAChartTowerEquiv
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:50.11053+00:00
-- url     : https://prove2.me/theorems/61f055c1-cb1d-44e1-92f6-3e72beddfc29
-- title:
--   The $A=1$ chart as a quadratic–cubic tower
-- statement:
--   Defines the quotient projection for the affine chart $A=1$, an iterated presentation obtained by adjoining a root of a monic quadratic and then imposing the remaining cubic relation, its coefficient and coordinate maps, and mutually inverse homomorphisms. The resulting ring and $K$-algebra equivalences identify the literal affine chart with this quadratic–cubic tower for structural calculations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalAChartTower
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_CanonicalUnitPlane
/-! The affine A-chart ring is the monic quadratic and cubic tower over its coefficient ring. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

def canonicalAChartProjection25 : MvPolynomial (Fin 4) K →ₐ[K] CanonicalAChartRing25 K :=
  Ideal.Quotient.mkₐ K (canonicalAChartIdeal25 K)

@[simp] theorem canonicalAChartQuotientScalar25 (a : K) :
    algebraMap K (CanonicalAChartRing25 K) a = Ideal.Quotient.mk (canonicalAChartIdeal25 K) (MvPolynomial.C a) := by
  simpa only [MvPolynomial.algebraMap_eq, Ideal.Quotient.mkₐ_eq_mk] using
    ((Ideal.Quotient.mkₐ K (canonicalAChartIdeal25 K)).commutes a).symm

/-- The literal A=1 relation recovers the fourth coordinate. -/
theorem canonicalAChartW25_eq :
    canonicalAChartCoordinate25 K 3 = canonicalAChartCoordinate25 K 1 + canonicalAChartCoordinate25 K 2 - 1 := by
  have h : canonicalAChartCoordinate25 K 1 + canonicalAChartCoordinate25 K 2 -
      canonicalAChartCoordinate25 K 3 - 1 = 0 := by
    change Ideal.Quotient.mk (canonicalAChartIdeal25 K)
      (canonicalDenominator (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3) - 1) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  linear_combination -h

def canonicalAChartTowerProjection25 :
    Polynomial (CanonicalAChartBase25 K) →+* CanonicalAChartTowerRing25 K :=
  (Ideal.Quotient.mk _).comp (AdjoinRoot.mk (canonicalAChartQuadratic25 K))

def canonicalAChartTowerCoefficient25 : K →+* CanonicalAChartTowerRing25 K :=
  ((canonicalAChartTowerProjection25 K).comp C).comp C |>.comp C

def canonicalAChartTowerCoordinate25 (i : Fin 4) : CanonicalAChartTowerRing25 K :=
  ![canonicalAChartTowerProjection25 K (C (canonicalAChartBaseX25 K)),
    canonicalAChartTowerProjection25 K X,
    canonicalAChartTowerProjection25 K (C (canonicalAChartBaseZ25 K)),
    canonicalAChartTowerProjection25 K X + canonicalAChartTowerProjection25 K (C (canonicalAChartBaseZ25 K)) - 1] i

@[simp] theorem canonicalAChartTowerProjection25_quadric :
    canonicalAChartTowerProjection25 K (canonicalAChartQuadratic25 K) = 0 := by
  simp [canonicalAChartTowerProjection25]

@[simp] theorem canonicalAChartTowerProjection25_cubic :
    canonicalAChartTowerProjection25 K (canonicalAChartLinearRemainder25 K) = 0 :=
  Ideal.Quotient.mk_singleton_self _

theorem canonicalAChartTower25_tower_quadric :
    canonicalQuadric (canonicalAChartTowerCoordinate25 K 0) (canonicalAChartTowerCoordinate25 K 1)
      (canonicalAChartTowerCoordinate25 K 2) (canonicalAChartTowerCoordinate25 K 3) = 0 := by
  calc
    _ = canonicalAChartTowerProjection25 K (canonicalAChartQuadratic25 K) := by
      simp only [canonicalAChartTowerCoordinate25, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Fin.reduceFinMk, canonicalQuadric,
        canonicalAChartQuadratic25, _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat, _root_.map_one]
      ring
    _ = 0 := canonicalAChartTowerProjection25_quadric K

theorem canonicalAChartTower25_tower_cubic :
    canonicalCubic (canonicalAChartTowerCoordinate25 K 0) (canonicalAChartTowerCoordinate25 K 1)
      (canonicalAChartTowerCoordinate25 K 2) (canonicalAChartTowerCoordinate25 K 3) = 0 := by
  have hi : canonicalCubic (canonicalAChartTowerCoordinate25 K 0) (canonicalAChartTowerCoordinate25 K 1)
      (canonicalAChartTowerCoordinate25 K 2) (canonicalAChartTowerCoordinate25 K 3) +
      canonicalAChartTowerCoordinate25 K 0 * canonicalQuadric
        (canonicalAChartTowerCoordinate25 K 0) (canonicalAChartTowerCoordinate25 K 1)
        (canonicalAChartTowerCoordinate25 K 2) (canonicalAChartTowerCoordinate25 K 3) =
      canonicalAChartTowerProjection25 K (canonicalAChartLinearRemainder25 K) := by
    simp only [canonicalAChartTowerCoordinate25, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.reduceFinMk, canonicalQuadric, canonicalCubic,
      canonicalAChartLinearRemainder25, canonicalAChartBaseMultiplier25, _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat, _root_.map_one]
    ring
  simpa only [canonicalAChartTower25_tower_quadric, mul_zero, add_zero, canonicalAChartTowerProjection25_cubic] using hi

def canonicalAChartToTower25 : CanonicalAChartRing25 K →+* CanonicalAChartTowerRing25 K :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (canonicalAChartTowerCoefficient25 K) (canonicalAChartTowerCoordinate25 K)) (by
      change canonicalAChartIdeal25 K ≤ RingHom.ker
        (MvPolynomial.eval₂Hom (canonicalAChartTowerCoefficient25 K) (canonicalAChartTowerCoordinate25 K))
      apply Ideal.span_le.mpr
      intro p hp
      rcases hp with rfl | hp
      · simpa [RingHom.mem_ker, canonicalQuadric] using canonicalAChartTower25_tower_quadric K
      · rcases hp with rfl | hp
        · simpa [RingHom.mem_ker, canonicalCubic] using canonicalAChartTower25_tower_cubic K
        · rcases hp with rfl | hp
          · simp [RingHom.mem_ker, canonicalDenominator, canonicalAChartTowerCoordinate25])

def canonicalAChartBaseToChart25 : CanonicalAChartBase25 K →+* CanonicalAChartRing25 K :=
  eval₂RingHom (eval₂RingHom
    ((canonicalAChartProjection25 K).toRingHom.comp MvPolynomial.C)
      (canonicalAChartCoordinate25 K 2)) (canonicalAChartCoordinate25 K 0)

@[simp] theorem canonicalAChartBaseToChart25_X :
    canonicalAChartBaseToChart25 K (canonicalAChartBaseX25 K) = canonicalAChartCoordinate25 K 0 := by
  simp [canonicalAChartBaseToChart25, canonicalAChartBaseX25]

@[simp] theorem canonicalAChartBaseToChart25_Z :
    canonicalAChartBaseToChart25 K (canonicalAChartBaseZ25 K) = canonicalAChartCoordinate25 K 2 := by
  simp [canonicalAChartBaseToChart25, canonicalAChartBaseZ25]

theorem canonicalAChartTower25_cone_quadric :
    canonicalQuadric (canonicalAChartCoordinate25 K 0) (canonicalAChartCoordinate25 K 1)
      (canonicalAChartCoordinate25 K 2) (canonicalAChartCoordinate25 K 3) = 0 := by
  have h : canonicalQuadric (canonicalAChartCoordinate25 K 0) (canonicalAChartCoordinate25 K 1)
    (canonicalAChartCoordinate25 K 2) (canonicalAChartCoordinate25 K 3) =
    canonicalAChartProjection25 K (canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 2) (MvPolynomial.X 3)) := by
    simp only [canonicalQuadric, canonicalAChartCoordinate25, canonicalAChartProjection25, Ideal.Quotient.mkₐ_eq_mk, _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_neg]
  rw [h]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem canonicalAChartTower25_cone_cubic :
    canonicalCubic (canonicalAChartCoordinate25 K 0) (canonicalAChartCoordinate25 K 1)
      (canonicalAChartCoordinate25 K 2) (canonicalAChartCoordinate25 K 3) = 0 := by
  have h : canonicalCubic (canonicalAChartCoordinate25 K 0) (canonicalAChartCoordinate25 K 1)
    (canonicalAChartCoordinate25 K 2) (canonicalAChartCoordinate25 K 3) =
    canonicalAChartProjection25 K (canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 2) (MvPolynomial.X 3)) := by
    simp [canonicalCubic, canonicalAChartCoordinate25, canonicalAChartProjection25, Ideal.Quotient.mkₐ_eq_mk]
  rw [h]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem canonicalAChartTower25_quadric_root_equation :
    eval₂ (canonicalAChartBaseToChart25 K) (canonicalAChartCoordinate25 K 1)
      (canonicalAChartQuadratic25 K) = 0 := by
  have he : eval₂ (canonicalAChartBaseToChart25 K) (canonicalAChartCoordinate25 K 1)
      (canonicalAChartQuadratic25 K) =
      canonicalQuadric (canonicalAChartCoordinate25 K 0) (canonicalAChartCoordinate25 K 1)
        (canonicalAChartCoordinate25 K 2) (canonicalAChartCoordinate25 K 3) := by
    simp [canonicalAChartQuadratic25, eval₂_add, eval₂_sub, eval₂_neg, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
      _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat, _root_.map_one,
      canonicalAChartBaseToChart25_X, canonicalAChartBaseToChart25_Z, canonicalAChartW25_eq, canonicalQuadric]
    ring
  rw [he, canonicalAChartTower25_cone_quadric]

def canonicalAChartQuadricToChart25 : CanonicalAChartQuadricRoot25 K →+* CanonicalAChartRing25 K :=
  AdjoinRoot.lift (canonicalAChartBaseToChart25 K) (canonicalAChartCoordinate25 K 1) (canonicalAChartTower25_quadric_root_equation K)

theorem canonicalAChartTower25_cubic_root_equation :
    canonicalAChartQuadricToChart25 K
      (AdjoinRoot.mk (canonicalAChartQuadratic25 K) (canonicalAChartLinearRemainder25 K)) = 0 := by
  rw [canonicalAChartQuadricToChart25, AdjoinRoot.lift_mk]
  have he : eval₂ (canonicalAChartBaseToChart25 K) (canonicalAChartCoordinate25 K 1)
      (canonicalAChartLinearRemainder25 K) =
      canonicalCubic (canonicalAChartCoordinate25 K 0) (canonicalAChartCoordinate25 K 1)
        (canonicalAChartCoordinate25 K 2) (canonicalAChartCoordinate25 K 3) +
      canonicalAChartCoordinate25 K 0 * canonicalQuadric (canonicalAChartCoordinate25 K 0)
        (canonicalAChartCoordinate25 K 1) (canonicalAChartCoordinate25 K 2) (canonicalAChartCoordinate25 K 3) := by
    simp [canonicalAChartLinearRemainder25, canonicalAChartBaseMultiplier25, eval₂_add, eval₂_sub, eval₂_neg, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
      _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat, _root_.map_one,
      canonicalAChartBaseToChart25_X, canonicalAChartBaseToChart25_Z, canonicalAChartW25_eq, canonicalQuadric, canonicalCubic]
    ring
  rw [he, canonicalAChartTower25_cone_cubic, canonicalAChartTower25_cone_quadric, mul_zero, add_zero]

def canonicalAChartTowerToChart25 : CanonicalAChartTowerRing25 K →+* CanonicalAChartRing25 K :=
  Ideal.Quotient.lift _ (canonicalAChartQuadricToChart25 K) (by
    change Ideal.span _ ≤ RingHom.ker (canonicalAChartQuadricToChart25 K)
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | hp
    exact canonicalAChartTower25_cubic_root_equation K)

@[simp] theorem canonicalAChartTowerToChart25_projection (p : Polynomial (CanonicalAChartBase25 K)) :
    canonicalAChartTowerToChart25 K (canonicalAChartTowerProjection25 K p) =
      eval₂ (canonicalAChartBaseToChart25 K) (canonicalAChartCoordinate25 K 1) p := by
  simp [canonicalAChartTowerToChart25, canonicalAChartTowerProjection25, canonicalAChartQuadricToChart25,
    AdjoinRoot.lift_mk]

theorem canonicalAChartTower25_cone_roundtrip :
    (canonicalAChartTowerToChart25 K).comp (canonicalAChartToTower25 K) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [canonicalAChartToTower25, canonicalAChartTowerCoefficient25, canonicalAChartBaseToChart25]
  · intro i
    fin_cases i <;> simp [canonicalAChartToTower25, canonicalAChartTowerCoordinate25, canonicalAChartBaseToChart25,
      canonicalAChartBaseX25, canonicalAChartBaseZ25,  canonicalAChartW25_eq,
      canonicalAChartCoordinate25, canonicalAChartProjection25]
    exact (canonicalAChartW25_eq K).symm

theorem canonicalAChartTower25_tower_roundtrip :
    (canonicalAChartToTower25 K).comp (canonicalAChartTowerToChart25 K) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply AdjoinRoot.ringHom_ext
  · ext a <;> simp [canonicalAChartTowerToChart25, canonicalAChartQuadricToChart25, canonicalAChartBaseToChart25,
      canonicalAChartToTower25, canonicalAChartTowerCoefficient25, canonicalAChartTowerCoordinate25,
       canonicalAChartBaseX25, canonicalAChartBaseZ25, canonicalAChartW25_eq,
      canonicalAChartCoordinate25, canonicalAChartProjection25, canonicalAChartTowerProjection25]
  · simp [canonicalAChartTowerToChart25, canonicalAChartQuadricToChart25, canonicalAChartToTower25,
      canonicalAChartTowerCoordinate25, canonicalAChartCoordinate25, canonicalAChartProjection25,
      canonicalAChartTowerProjection25]

/-- The monic quadratic/cubic tower is the literal homogeneous cone quotient. -/
def canonicalAChartTowerRingEquiv25 : CanonicalAChartTowerRing25 K ≃+* CanonicalAChartRing25 K where
  toFun := canonicalAChartTowerToChart25 K
  invFun := canonicalAChartToTower25 K
  left_inv := RingHom.congr_fun (canonicalAChartTower25_tower_roundtrip K)
  right_inv := RingHom.congr_fun (canonicalAChartTower25_cone_roundtrip K)
  map_mul' := (canonicalAChartTowerToChart25 K).map_mul
  map_add' := (canonicalAChartTowerToChart25 K).map_add

/-- The quotient equivalence also preserves the coefficient field. -/
def canonicalAChartTowerAlgEquiv25 : CanonicalAChartTowerRing25 K ≃ₐ[K] CanonicalAChartRing25 K where
  __ := canonicalAChartTowerRingEquiv25 K
  commutes' a := by
    change canonicalAChartTowerToChart25 K
      (canonicalAChartTowerProjection25 K (C (C (C a)))) = algebraMap K (CanonicalAChartRing25 K) a
    rw [canonicalAChartTowerToChart25_projection]
    simp [canonicalAChartBaseToChart25, canonicalAChartProjection25]

end N25


