-- Prove2me | Definitions.Def_MazurTransfer_MixedQuadraticOriginalScalarExtensionAndCompletingSquareData20261019
-- name    : MazurTransfer_MixedQuadraticOriginalScalarExtensionAndCompletingSquareData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T04:47:00.315773+00:00
-- url     : https://prove2.me/theorems/190978d7-79e5-4a57-aa4a-1ede90ae72eb
-- title:
--   Original mixed quadratic scalar extension and completing-square equivalences
-- statement:
--   The original tensor-product scalar-extension equivalence for mixed quadratic coordinate algebras, the two original completing-square maps, and their original whole algebra equivalence whenever two has a specified inverse. Twenty-seven original types and six whole nonproof constructor values are checked. Named downstream consumer: the actual dyadic rational affine fibres.
-- source:
--   MazurTheorem original mixed quadratic scalar extension, completing square, rational chart comparison and affine base change; Vas and contributors; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_MixedQuadraticOriginalCoordinateEquationAndJacobianData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: canonical scalar extension of a mixed quadratic coordinate
algebra is the coordinate algebra with both polynomials mapped on coefficients.
Named downstream consumer: genuine rational fibres of the dyadic chart schemes.
-/
noncomputable section
namespace MazurTransfer.MixedQuadraticCoordinateBaseChange
open Polynomial Algebra TensorProduct MixedQuadraticCoordinateJacobian
universe u v
variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

def coordinateRingEquiv (h f : Polynomial R) :
    S ⊗[R] CoordinateRing R h f ≃ₐ[S]
      CoordinateRing S (h.map (algebraMap R S)) (f.map (algebraMap R S)) := by
  let p := equation R h f
  let q : Polynomial (S ⊗[R] Polynomial R) :=
    p.map Algebra.TensorProduct.includeRight.toRingHom
  let e : S ⊗[R] Polynomial R ≃ₐ[S] Polynomial S := (polyEquivTensor' R S).symm
  have hq : q.map e = equation S (h.map (algebraMap R S)) (f.map (algebraMap R S)) := by
    simp [q, p, e, equation, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      polyEquivTensor_symm_apply_tmul_eq_smul]
  exact (AdjoinRoot.tensorAlgEquiv p q rfl).trans
    (AdjoinRoot.mapAlgEquiv e q _ (hq ▸ Associated.refl _))

end MazurTransfer.MixedQuadraticCoordinateBaseChange
#print axioms MazurTransfer.MixedQuadraticCoordinateBaseChange.coordinateRingEquiv

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: completing the square gives an actual algebra equivalence
between mixed quadratic and square coordinate algebras when two has an
inverse. Named downstream consumer: comparison of the proposed dyadic
charts with the SAME existing rational order-thirteen curve charts.
-/
noncomputable section
namespace MazurTransfer.MixedQuadraticCompletingSquare
open Polynomial
universe u
variable (A : Type u) [CommRing A]

def mixedPolynomial (h f : A) : Polynomial A := X ^ 2 + C h * X - C f
def squarePolynomial (h f : A) : Polynomial A := X ^ 2 - C (h ^ 2 + 4 * f)

theorem square_relation (h f y : A) (hy : y ^ 2 + h * y - f = 0) :
    (2 * y + h) ^ 2 - (h ^ 2 + 4 * f) = 0 := by
  linear_combination 4 * hy

theorem mixed_relation (h f c z : A) (hc : 2 * c = 1)
    (hz : z ^ 2 - (h ^ 2 + 4 * f) = 0) :
    (c * (z - h)) ^ 2 + h * (c * (z - h)) - f = 0 := by
  have hc2 : 4 * c ^ 2 = 1 := by
    calc
      _ = (2 * c) ^ 2 := by ring
      _ = 1 := by rw [hc]; ring
  calc
    _ = c ^ 2 * (z ^ 2 - (h ^ 2 + 4 * f)) +
        c * (1 - 2 * c) * h * (z - h) + (4 * c ^ 2 - 1) * f := by ring
    _ = 0 := by rw [hz, hc, hc2]; ring

variable (h f c : A) (hc : 2 * c = 1)

def toSquare : AdjoinRoot (mixedPolynomial A h f) →ₐ[A] AdjoinRoot (squarePolynomial A h f) :=
  AdjoinRoot.liftAlgHom (mixedPolynomial A h f)
    (Algebra.ofId A (AdjoinRoot (squarePolynomial A h f)))
    (AdjoinRoot.of (squarePolynomial A h f) c *
      (AdjoinRoot.root (squarePolynomial A h f) - AdjoinRoot.of (squarePolynomial A h f) h)) (by
    simp only [mixedPolynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    change (AdjoinRoot.of (squarePolynomial A h f) c *
      (AdjoinRoot.root (squarePolynomial A h f) - AdjoinRoot.of (squarePolynomial A h f) h)) ^ 2 +
      AdjoinRoot.of (squarePolynomial A h f) h *
      (AdjoinRoot.of (squarePolynomial A h f) c *
      (AdjoinRoot.root (squarePolynomial A h f) - AdjoinRoot.of (squarePolynomial A h f) h)) -
      AdjoinRoot.of (squarePolynomial A h f) f = 0
    apply mixed_relation
    · have ht := congrArg (AdjoinRoot.of (squarePolynomial A h f)) hc
      simpa only [map_mul, map_ofNat, map_one] using ht
    · have ht := AdjoinRoot.eval₂_root (squarePolynomial A h f)
      change eval₂ (AdjoinRoot.of (squarePolynomial A h f))
        (AdjoinRoot.root (squarePolynomial A h f)) (X ^ 2 - C (h ^ 2 + 4 * f)) = 0 at ht
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at ht
      rw [map_add, map_pow, map_mul, map_ofNat] at ht
      exact ht)

def fromSquare : AdjoinRoot (squarePolynomial A h f) →ₐ[A] AdjoinRoot (mixedPolynomial A h f) :=
  AdjoinRoot.liftAlgHom (squarePolynomial A h f)
    (Algebra.ofId A (AdjoinRoot (mixedPolynomial A h f)))
    (2 * AdjoinRoot.root (mixedPolynomial A h f) + AdjoinRoot.of (mixedPolynomial A h f) h) (by
    simp only [squarePolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    change (2 * AdjoinRoot.root (mixedPolynomial A h f) + AdjoinRoot.of (mixedPolynomial A h f) h) ^ 2 -
      AdjoinRoot.of (mixedPolynomial A h f) (h ^ 2 + 4 * f) = 0
    rw [map_add, map_pow, map_mul, map_ofNat]
    change (2 * AdjoinRoot.root (mixedPolynomial A h f) + AdjoinRoot.of (mixedPolynomial A h f) h) ^ 2 -
      (AdjoinRoot.of (mixedPolynomial A h f) h ^ 2 + 4 * AdjoinRoot.of (mixedPolynomial A h f) f) = 0
    apply square_relation
    have ht := AdjoinRoot.eval₂_root (mixedPolynomial A h f)
    change eval₂ (AdjoinRoot.of (mixedPolynomial A h f))
      (AdjoinRoot.root (mixedPolynomial A h f)) (X ^ 2 + C h * X - C f) = 0 at ht
    simpa only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] using ht)

theorem toSquare_root : toSquare A h f c hc (AdjoinRoot.root (mixedPolynomial A h f)) =
    AdjoinRoot.of (squarePolynomial A h f) c *
      (AdjoinRoot.root (squarePolynomial A h f) - AdjoinRoot.of (squarePolynomial A h f) h) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem fromSquare_root : fromSquare A h f (AdjoinRoot.root (squarePolynomial A h f)) =
    2 * AdjoinRoot.root (mixedPolynomial A h f) + AdjoinRoot.of (mixedPolynomial A h f) h :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

def completingSquareEquiv : AdjoinRoot (mixedPolynomial A h f) ≃ₐ[A] AdjoinRoot (squarePolynomial A h f) :=
  AlgEquiv.ofAlgHom (toSquare A h f c hc) (fromSquare A h f) (by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, fromSquare_root, map_add, map_mul,
      map_ofNat, toSquare_root]
    have hh := (toSquare A h f c hc).commutes h
    simp only [AdjoinRoot.algebraMap_eq] at hh
    rw [hh]
    have hca : (2 : AdjoinRoot (squarePolynomial A h f)) * AdjoinRoot.of (squarePolynomial A h f) c = 1 := by
      simpa only [map_mul, map_ofNat, map_one] using congrArg (AdjoinRoot.of (squarePolynomial A h f)) hc
    linear_combination (AdjoinRoot.root (squarePolynomial A h f) - AdjoinRoot.of (squarePolynomial A h f) h) * hca)
    (by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, toSquare_root, map_mul, map_sub, fromSquare_root]
    have hh := (fromSquare A h f).commutes h
    have hcc := (fromSquare A h f).commutes c
    simp only [AdjoinRoot.algebraMap_eq] at hh hcc
    rw [hh, hcc]
    have hca : (2 : AdjoinRoot (mixedPolynomial A h f)) * AdjoinRoot.of (mixedPolynomial A h f) c = 1 := by
      simpa only [map_mul, map_ofNat, map_one] using congrArg (AdjoinRoot.of (mixedPolynomial A h f)) hc
    linear_combination AdjoinRoot.root (mixedPolynomial A h f) * hca)

end MazurTransfer.MixedQuadraticCompletingSquare
#print axioms MazurTransfer.MixedQuadraticCompletingSquare.completingSquareEquiv

end


