-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCubic_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianCubic_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:10:58.841397+00:00
-- url     : https://prove2.me/theorems/bc411d99-269e-4ff6-91a1-910bd7d2cad2
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianCubic source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianCubic

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianCubic
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFactorization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SexticSquareclass_p0

set_option autoImplicit false




/-!
# The Gaussian cubic presentation of the N13 sextic algebra

The sextic algebra becomes cubic after adjoining its intrinsic order-four
unit `i`.  More importantly for the local descent, all long power-basis
generators have short expressions in `i` and the sextic root `θ`.

Every identity below has a constant or linear quotient by the defining
sextic.  Thus this file records the structural change of presentation rather
than a high-degree certificate.
-/

open Polynomial

namespace MazurProof.N13GaussianCubic

noncomputable section

open N13SexticSquareclass

abbrev L : Type := SexticAlgebra

/-- The sextic root. -/
def theta : L :=
  AdjoinRoot.root f

/-- The polynomial representative of the order-four unit. -/
def iPoly : ℚ[X] :=
  C (1 / 2 : ℚ) * Z

/-- The real and imaginary parts of the Gaussian cubic factor. -/
def cubicA : ℚ[X] :=
  X ^ 3 + 2 * X ^ 2 - X - 1

def cubicB : ℚ[X] :=
  2 * X * (X + 1)

private def zetaSqQuotient : ℚ[X] :=
  4 * X ^ 4 + 12 * X ^ 3 + 13 * X ^ 2 - 2 * X + 13

theorem Z_sq_add_four :
    Z ^ 2 + 4 = f * zetaSqQuotient := by
  simp [f, N13Mumford.f, Z, zetaSqQuotient]
  ring

theorem gaussian_cubic_reduction :
    2 * cubicA - Z * cubicB = f * (-4 * X - 2) := by
  simp [cubicA, cubicB, f, N13Mumford.f, Z]
  ring

theorem e1_short_reduction :
    E₁ - (2 * (1 - X ^ 2) + (Z - 2) * X) =
      f * (-2) := by
  simp [f, N13Mumford.f, Z, E₁]
  ring

theorem e2_short_reduction :
    E₂ -
        (2 + Z * X ^ 2 + (2 + 2 * Z) * X) =
      f * (-(2 * X + 3)) := by
  simp [f, N13Mumford.f, Z, E₂]
  ring

theorem primeA_short_reduction :
    A -
        (2 - Z * X ^ 2 - (2 + Z) * X) =
      f * (2 * X + 1) := by
  simp [f, N13Mumford.f, Z, A]
  ring

theorem primeQ_short_polynomial :
    Q = 4 - 3 * Z := by
  simp [Z, Q]
  ring

private theorem ofPoly_eq_of_sub_eq_mul
    (p q r : ℚ[X]) (h : p - q = f * r) :
    ofPoly p = ofPoly q := by
  have hm := congrArg (AdjoinRoot.mk f) h
  rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul] at hm
  exact sub_eq_zero.mp hm

@[simp] theorem ofPoly_X :
    ofPoly X = theta := rfl

theorem zeta_eq_iPoly :
    zeta = ofPoly iPoly := rfl

theorem halfOfPoly_eq (p : ℚ[X]) :
    halfOfPoly p =
      AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly p := by
  simp [halfOfPoly, ofPoly, map_mul]

theorem zeta_eq_half_mul_Z :
    zeta = AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z := by
  exact halfOfPoly_eq Z

private theorem of_two :
    AdjoinRoot.of f (2 : ℚ) = (2 : L) :=
  map_ofNat (AdjoinRoot.of f) 2

private theorem of_four :
    AdjoinRoot.of f (4 : ℚ) = (4 : L) :=
  map_ofNat (AdjoinRoot.of f) 4

private theorem of_half_mul_two :
    AdjoinRoot.of f (1 / 2 : ℚ) * (2 : L) = 1 := by
  rw [← of_two, ← map_mul]
  norm_num

private theorem of_quarter_mul_four :
    AdjoinRoot.of f (1 / 4 : ℚ) * (4 : L) = 1 := by
  rw [← of_four, ← map_mul]
  norm_num

private theorem of_half_sq :
    AdjoinRoot.of f (1 / 2 : ℚ) ^ 2 =
      AdjoinRoot.of f (1 / 4 : ℚ) := by
  rw [← map_pow]
  norm_num

/-- The intrinsic torsion unit is a square root of `-1`. -/
theorem zeta_sq :
    zeta ^ 2 = (-1 : L) := by
  have h := ofPoly_eq_of_sub_eq_mul
    (Z ^ 2) (C (-4 : ℚ)) zetaSqQuotient (by
      calc
        Z ^ 2 - C (-4 : ℚ) = Z ^ 2 + 4 := by
          rw [show C (-4 : ℚ) = -(4 : ℚ[X]) by
            rw [map_neg]
            exact congrArg Neg.neg
              (map_natCast (C : ℚ →+* ℚ[X]) 4)]
          ring
        _ = f * zetaSqQuotient := Z_sq_add_four)
  have h' : ofPoly Z ^ 2 = (-4 : L) := by
    simpa [ofPoly, map_pow, AdjoinRoot.mk_C, of_four] using h
  rw [zeta_eq_half_mul_Z]
  calc
    (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) ^ 2 =
        AdjoinRoot.of f (1 / 4 : ℚ) * ofPoly Z ^ 2 := by
      rw [mul_pow, of_half_sq]
    _ = AdjoinRoot.of f (1 / 4 : ℚ) * (-4) := by rw [h']
    _ = -1 := by
      calc
        AdjoinRoot.of f (1 / 4 : ℚ) * (-4) =
            -(AdjoinRoot.of f (1 / 4 : ℚ) * 4) := by ring
        _ = -1 := by rw [of_quarter_mul_four]

/-- The sextic root satisfies a cubic equation over `ℚ(i)`. -/
theorem gaussian_cubic :
    theta ^ 3 + 2 * theta ^ 2 - theta - 1 -
        zeta * (2 * theta * (theta + 1)) = 0 := by
  have h := ofPoly_eq_of_sub_eq_mul
    (2 * cubicA - Z * cubicB) 0 (-4 * X - 2)
    (by simpa using gaussian_cubic_reduction)
  have h' :
      2 * (theta ^ 3 + 2 * theta ^ 2 - theta - 1) -
          ofPoly Z * (2 * theta * (theta + 1)) = 0 := by
    simpa [theta, cubicA, cubicB, ofPoly, map_sub, map_mul, map_add,
      map_pow, map_ofNat] using h
  rw [zeta_eq_half_mul_Z]
  let Aθ := theta ^ 3 + 2 * theta ^ 2 - theta - 1
  let Bθ := 2 * theta * (theta + 1)
  calc
    Aθ - (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * Bθ =
        (AdjoinRoot.of f (1 / 2 : ℚ) * 2) * Aθ -
          AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z * Bθ := by
            rw [of_half_mul_two]
            ring
    _ = AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 * Aθ - ofPoly Z * Bθ) := by ring
    _ = 0 := by rw [show 2 * Aθ - ofPoly Z * Bθ = 0 from h']; ring

/-- The first fundamental unit in the Gaussian cubic basis. -/
theorem e1_short :
    e1 = 1 - theta ^ 2 + (zeta - 1) * theta := by
  have h := ofPoly_eq_of_sub_eq_mul
    E₁ (2 * (1 - X ^ 2) + (Z - 2) * X) (-2)
    e1_short_reduction
  have h' :
      ofPoly E₁ =
        2 * (1 - theta ^ 2) + (ofPoly Z - 2) * theta := by
    simpa [theta, ofPoly, map_sub, map_mul, map_add, map_pow,
      map_ofNat] using h
  rw [show e1 = halfOfPoly E₁ from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly E₁ =
        AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 * (1 - theta ^ 2) + (ofPoly Z - 2) * theta) := by
            rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) *
          (1 - theta ^ 2) +
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z -
          AdjoinRoot.of f (1 / 2 : ℚ) * 2) * theta := by ring
    _ = 1 - theta ^ 2 +
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z - 1) * theta := by
          simp only [of_half_mul_two, one_mul]

/-- The second fundamental unit in the Gaussian cubic basis. -/
theorem e2_short :
    e2 = 1 + zeta * theta ^ 2 + (1 + 2 * zeta) * theta := by
  have h := ofPoly_eq_of_sub_eq_mul
    E₂ (2 + Z * X ^ 2 + (2 + 2 * Z) * X)
    (-(2 * X + 3))
    e2_short_reduction
  have h' :
      ofPoly E₂ =
        2 + ofPoly Z * theta ^ 2 +
          (2 + 2 * ofPoly Z) * theta := by
    simpa [theta, ofPoly, map_sub, map_mul, map_add, map_pow,
      map_ofNat] using h
  rw [show e2 = halfOfPoly E₂ from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly E₂ =
        AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 + ofPoly Z * theta ^ 2 +
            (2 + 2 * ofPoly Z) * theta) := by rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) +
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 +
        ((AdjoinRoot.of f (1 / 2 : ℚ) * 2) +
          2 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z)) * theta := by
            ring
    _ = 1 + (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 +
        (1 + 2 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z)) * theta := by
          rw [of_half_mul_two]

/-- The ramified prime generator over `13` in the Gaussian cubic basis. -/
theorem primeA_short :
    primeA = 1 - zeta * theta ^ 2 - (1 + zeta) * theta := by
  have h := ofPoly_eq_of_sub_eq_mul
    A (2 - Z * X ^ 2 - (2 + Z) * X)
    (2 * X + 1)
    primeA_short_reduction
  have h' :
      ofPoly A =
        2 - ofPoly Z * theta ^ 2 - (2 + ofPoly Z) * theta := by
    simpa [theta, ofPoly, map_sub, map_mul, map_add, map_pow,
      map_ofNat] using h
  rw [show primeA = halfOfPoly A from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly A =
        AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 - ofPoly Z * theta ^ 2 - (2 + ofPoly Z) * theta) := by
            rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) -
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 -
        ((AdjoinRoot.of f (1 / 2 : ℚ) * 2) +
          AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta := by ring
    _ = 1 - (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 -
        (1 + AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta := by
          rw [of_half_mul_two]

/-- The residue-degree-three prime generator over `13` is already linear
in the Gaussian unit. -/
theorem primeQ_short :
    primeQ = 2 - 3 * zeta := by
  have h := congrArg ofPoly primeQ_short_polynomial
  have h' : ofPoly Q = 4 - 3 * ofPoly Z := by
    simpa [ofPoly, map_sub, map_mul, map_ofNat] using h
  rw [show primeQ = halfOfPoly Q from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Q =
        AdjoinRoot.of f (1 / 2 : ℚ) * (4 - 3 * ofPoly Z) := by
          rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) * 2 -
        3 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) := by ring
    _ = 2 - 3 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) := by
      simp only [of_half_mul_two, one_mul]

end

end MazurProof.N13GaussianCubic


