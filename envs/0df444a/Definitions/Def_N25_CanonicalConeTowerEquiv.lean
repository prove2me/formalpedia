-- Prove2me | Definitions.Def_N25_CanonicalConeTowerEquiv
-- name    : N25_CanonicalConeTowerEquiv
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:01.403798+00:00
-- url     : https://prove2.me/theorems/8d1d7f37-51ce-431e-8ae6-20e7b47283d7
-- title:
--   The canonical cone as a quadratic–cubic tower
-- statement:
--   Defines the coefficient and coordinate maps for an iterated monic quadratic–cubic presentation of the homogeneous canonical cone, together with maps in both directions between the tower and the literal quadric–cubic quotient. Their ring equivalence supplies a concrete algebraic presentation of the cone used to establish integrality and control its projective spectrum.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalProjectiveCone
/-! The homogeneous canonical cone ring is the monic quadratic and cubic tower over its coefficient ring. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

@[simp] theorem canonicalConeQuotientScalar25 (a : K) :
    algebraMap K (CanonicalConeRing25 K) a = Ideal.Quotient.mk (canonicalConeIdeal25 K) (MvPolynomial.C a) := by
  simpa only [MvPolynomial.algebraMap_eq, Ideal.Quotient.mkₐ_eq_mk] using
    ((Ideal.Quotient.mkₐ K (canonicalConeIdeal25 K)).commutes a).symm

def canonicalConeTowerProjection25 :
    Polynomial (CanonicalConeBase25 K) →+* CanonicalConeTowerRing25 K :=
  (Ideal.Quotient.mk _).comp (AdjoinRoot.mk (canonicalConeQuadricPolynomial25 K))

def canonicalConeTowerCoefficient25 : K →+* CanonicalConeTowerRing25 K :=
  (((canonicalConeTowerProjection25 K).comp C).comp C).comp C |>.comp C

def canonicalConeTowerCoordinate25 (i : Fin 4) : CanonicalConeTowerRing25 K :=
  ![canonicalConeTowerProjection25 K (C (canonicalConeBaseX25 K)),
    canonicalConeTowerProjection25 K X,
    canonicalConeTowerProjection25 K (C (canonicalConeBaseZ25 K)),
    canonicalConeTowerProjection25 K X + canonicalConeTowerProjection25 K (C (canonicalConeBaseZ25 K)) -
      canonicalConeTowerProjection25 K (C (canonicalConeBaseA25 K))] i

@[simp] theorem canonicalConeTowerProjection25_quadric :
    canonicalConeTowerProjection25 K (canonicalConeQuadricPolynomial25 K) = 0 := by
  simp [canonicalConeTowerProjection25]

@[simp] theorem canonicalConeTowerProjection25_cubic :
    canonicalConeTowerProjection25 K (canonicalConeCubicRemainder25 K) = 0 :=
  Ideal.Quotient.mk_singleton_self _

theorem canonicalConeTower25_tower_quadric :
    canonicalQuadric (canonicalConeTowerCoordinate25 K 0) (canonicalConeTowerCoordinate25 K 1)
      (canonicalConeTowerCoordinate25 K 2) (canonicalConeTowerCoordinate25 K 3) = 0 := by
  calc
    _ = canonicalConeTowerProjection25 K (canonicalConeQuadricPolynomial25 K) := by
      simp only [canonicalConeTowerCoordinate25, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Fin.reduceFinMk, canonicalQuadric,
        canonicalConeQuadricPolynomial25, _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat, _root_.map_one]
      simp only [_root_.map_sub (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
        _root_.map_mul (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
        _root_.map_pow (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
        _root_.map_add (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
        _root_.map_ofNat (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
        _root_.map_one (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
        _root_.map_sub (canonicalConeTowerProjection25 K), _root_.map_mul (canonicalConeTowerProjection25 K),
        _root_.map_pow (canonicalConeTowerProjection25 K), _root_.map_add (canonicalConeTowerProjection25 K),
        _root_.map_ofNat (canonicalConeTowerProjection25 K), _root_.map_one (canonicalConeTowerProjection25 K)]
      ring
    _ = 0 := canonicalConeTowerProjection25_quadric K

theorem canonicalConeTower25_tower_cubic :
    canonicalCubic (canonicalConeTowerCoordinate25 K 0) (canonicalConeTowerCoordinate25 K 1)
      (canonicalConeTowerCoordinate25 K 2) (canonicalConeTowerCoordinate25 K 3) = 0 := by
  have hi : canonicalCubic (canonicalConeTowerCoordinate25 K 0) (canonicalConeTowerCoordinate25 K 1)
      (canonicalConeTowerCoordinate25 K 2) (canonicalConeTowerCoordinate25 K 3) +
      canonicalConeTowerCoordinate25 K 0 * canonicalQuadric
        (canonicalConeTowerCoordinate25 K 0) (canonicalConeTowerCoordinate25 K 1)
        (canonicalConeTowerCoordinate25 K 2) (canonicalConeTowerCoordinate25 K 3) =
      canonicalConeTowerProjection25 K (canonicalConeCubicRemainder25 K) := by
    simp only [canonicalConeTowerCoordinate25, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.reduceFinMk, canonicalQuadric, canonicalCubic,
      canonicalConeCubicRemainder25, _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat, _root_.map_one]
    simp only [_root_.map_sub (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
      _root_.map_mul (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
      _root_.map_pow (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
      _root_.map_add (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
        _root_.map_ofNat (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
        _root_.map_one (C : CanonicalConeBase25 K →+* Polynomial (CanonicalConeBase25 K)),
      _root_.map_sub (canonicalConeTowerProjection25 K), _root_.map_mul (canonicalConeTowerProjection25 K),
      _root_.map_pow (canonicalConeTowerProjection25 K), _root_.map_add (canonicalConeTowerProjection25 K),
      _root_.map_ofNat (canonicalConeTowerProjection25 K), _root_.map_one (canonicalConeTowerProjection25 K)]
    ring
  simpa only [canonicalConeTower25_tower_quadric, mul_zero, add_zero, canonicalConeTowerProjection25_cubic] using hi

def canonicalConeToTower25 : CanonicalConeRing25 K →+* CanonicalConeTowerRing25 K :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (canonicalConeTowerCoefficient25 K) (canonicalConeTowerCoordinate25 K)) (by
      change canonicalConeIdeal25 K ≤ RingHom.ker
        (MvPolynomial.eval₂Hom (canonicalConeTowerCoefficient25 K) (canonicalConeTowerCoordinate25 K))
      apply Ideal.span_le.mpr
      intro p hp
      rcases hp with rfl | hp
      · simpa [RingHom.mem_ker, canonicalQuadric] using canonicalConeTower25_tower_quadric K
      · rcases hp with rfl | hp
        · simpa [RingHom.mem_ker, canonicalCubic] using canonicalConeTower25_tower_cubic K)

def canonicalConeBaseToCone25 : CanonicalConeBase25 K →+* CanonicalConeRing25 K :=
  eval₂RingHom (eval₂RingHom (eval₂RingHom
    ((canonicalConeProjection25 K).toRingHom.comp MvPolynomial.C)
      (canonicalConeCoordinate25 K 2)) (canonicalConeCoordinate25 K 0)) (canonicalConeA25 K)

@[simp] theorem canonicalConeBaseToCone25_A :
    canonicalConeBaseToCone25 K (canonicalConeBaseA25 K) = canonicalConeA25 K := by
  simp [canonicalConeBaseToCone25, canonicalConeBaseA25]

@[simp] theorem canonicalConeBaseToCone25_X :
    canonicalConeBaseToCone25 K (canonicalConeBaseX25 K) = canonicalConeCoordinate25 K 0 := by
  simp [canonicalConeBaseToCone25, canonicalConeBaseX25]

@[simp] theorem canonicalConeBaseToCone25_Z :
    canonicalConeBaseToCone25 K (canonicalConeBaseZ25 K) = canonicalConeCoordinate25 K 2 := by
  simp [canonicalConeBaseToCone25, canonicalConeBaseZ25]

theorem canonicalConeTower25_cone_quadric :
    canonicalQuadric (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
      (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) = 0 := by
  have h : canonicalQuadric (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
    (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) =
    canonicalConeProjection25 K (canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 2) (MvPolynomial.X 3)) := by
    simp only [canonicalQuadric, canonicalConeCoordinate25, _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_neg]
  rw [h]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem canonicalConeTower25_cone_cubic :
    canonicalCubic (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
      (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) = 0 := by
  have h : canonicalCubic (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
    (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) =
    canonicalConeProjection25 K (canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 2) (MvPolynomial.X 3)) := by
    simp [canonicalCubic, canonicalConeCoordinate25]
  rw [h]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem canonicalConeTower25_quadric_root_equation :
    eval₂ (canonicalConeBaseToCone25 K) (canonicalConeCoordinate25 K 1)
      (canonicalConeQuadricPolynomial25 K) = 0 := by
  have he : eval₂ (canonicalConeBaseToCone25 K) (canonicalConeCoordinate25 K 1)
      (canonicalConeQuadricPolynomial25 K) =
      canonicalQuadric (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
        (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) := by
    simp only [canonicalConeQuadricPolynomial25, eval₂_add, eval₂_sub, eval₂_neg, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
      _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat, canonicalConeBaseToCone25_A,
      canonicalConeBaseToCone25_X, canonicalConeBaseToCone25_Z, canonicalConeA25, canonicalQuadric]
    simp only [_root_.map_sub (canonicalConeBaseToCone25 K), _root_.map_mul (canonicalConeBaseToCone25 K),
      _root_.map_add (canonicalConeBaseToCone25 K), _root_.map_pow (canonicalConeBaseToCone25 K),
      _root_.map_ofNat (canonicalConeBaseToCone25 K), _root_.map_one (canonicalConeBaseToCone25 K),
      canonicalConeBaseToCone25_A, canonicalConeBaseToCone25_X, canonicalConeBaseToCone25_Z, canonicalConeA25]
    ring
  rw [he, canonicalConeTower25_cone_quadric]

def canonicalConeQuadricToCone25 : CanonicalConeQuadricRoot25 K →+* CanonicalConeRing25 K :=
  AdjoinRoot.lift (canonicalConeBaseToCone25 K) (canonicalConeCoordinate25 K 1) (canonicalConeTower25_quadric_root_equation K)

theorem canonicalConeTower25_cubic_root_equation :
    canonicalConeQuadricToCone25 K
      (AdjoinRoot.mk (canonicalConeQuadricPolynomial25 K) (canonicalConeCubicRemainder25 K)) = 0 := by
  rw [canonicalConeQuadricToCone25, AdjoinRoot.lift_mk]
  have he : eval₂ (canonicalConeBaseToCone25 K) (canonicalConeCoordinate25 K 1)
      (canonicalConeCubicRemainder25 K) =
      canonicalCubic (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
        (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) +
      canonicalConeCoordinate25 K 0 * canonicalQuadric (canonicalConeCoordinate25 K 0)
        (canonicalConeCoordinate25 K 1) (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) := by
    simp only [canonicalConeCubicRemainder25, eval₂_add, eval₂_sub, eval₂_neg, eval₂_mul, eval₂_C, eval₂_X,
      _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat, canonicalConeBaseToCone25_A,
      canonicalConeBaseToCone25_X, canonicalConeBaseToCone25_Z, canonicalConeA25, canonicalQuadric, canonicalCubic]
    simp only [_root_.map_sub (canonicalConeBaseToCone25 K), _root_.map_mul (canonicalConeBaseToCone25 K),
      _root_.map_add (canonicalConeBaseToCone25 K), _root_.map_pow (canonicalConeBaseToCone25 K),
      _root_.map_ofNat (canonicalConeBaseToCone25 K), _root_.map_one (canonicalConeBaseToCone25 K),
      canonicalConeBaseToCone25_A, canonicalConeBaseToCone25_X, canonicalConeBaseToCone25_Z, canonicalConeA25]
    ring
  rw [he, canonicalConeTower25_cone_cubic, canonicalConeTower25_cone_quadric, mul_zero, add_zero]

def canonicalConeTowerToCone25 : CanonicalConeTowerRing25 K →+* CanonicalConeRing25 K :=
  Ideal.Quotient.lift _ (canonicalConeQuadricToCone25 K) (by
    change Ideal.span _ ≤ RingHom.ker (canonicalConeQuadricToCone25 K)
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | hp
    exact canonicalConeTower25_cubic_root_equation K)

@[simp] theorem canonicalConeTowerToCone25_projection (p : Polynomial (CanonicalConeBase25 K)) :
    canonicalConeTowerToCone25 K (canonicalConeTowerProjection25 K p) =
      eval₂ (canonicalConeBaseToCone25 K) (canonicalConeCoordinate25 K 1) p := by
  simp [canonicalConeTowerToCone25, canonicalConeTowerProjection25, canonicalConeQuadricToCone25,
    AdjoinRoot.lift_mk]

theorem canonicalConeTower25_cone_roundtrip :
    (canonicalConeTowerToCone25 K).comp (canonicalConeToTower25 K) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [canonicalConeToTower25, canonicalConeTowerCoefficient25, canonicalConeBaseToCone25]
  · intro i
    fin_cases i <;> simp [canonicalConeToTower25, canonicalConeTowerCoordinate25, canonicalConeBaseToCone25,
      canonicalConeBaseX25, canonicalConeBaseZ25, canonicalConeBaseA25, canonicalConeA25,
      canonicalConeCoordinate25, canonicalConeProjection25]

theorem canonicalConeTower25_tower_roundtrip :
    (canonicalConeToTower25 K).comp (canonicalConeTowerToCone25 K) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply AdjoinRoot.ringHom_ext
  · ext a <;> simp [canonicalConeTowerToCone25, canonicalConeQuadricToCone25, canonicalConeBaseToCone25,
      canonicalConeToTower25, canonicalConeTowerCoefficient25, canonicalConeTowerCoordinate25,
      canonicalConeBaseA25, canonicalConeBaseX25, canonicalConeBaseZ25, canonicalConeA25,
      canonicalConeCoordinate25, canonicalConeProjection25, canonicalConeTowerProjection25]
  · simp [canonicalConeTowerToCone25, canonicalConeQuadricToCone25, canonicalConeToTower25,
      canonicalConeTowerCoordinate25, canonicalConeCoordinate25, canonicalConeProjection25,
      canonicalConeTowerProjection25]

/-- The monic quadratic/cubic tower is the literal homogeneous cone quotient. -/
def canonicalConeTowerRingEquiv25 : CanonicalConeTowerRing25 K ≃+* CanonicalConeRing25 K where
  toFun := canonicalConeTowerToCone25 K
  invFun := canonicalConeToTower25 K
  left_inv := RingHom.congr_fun (canonicalConeTower25_tower_roundtrip K)
  right_inv := RingHom.congr_fun (canonicalConeTower25_cone_roundtrip K)
  map_mul' := (canonicalConeTowerToCone25 K).map_mul
  map_add' := (canonicalConeTowerToCone25 K).map_add

end N25


