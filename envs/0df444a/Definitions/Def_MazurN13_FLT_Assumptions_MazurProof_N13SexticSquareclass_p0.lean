-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SexticSquareclass_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SexticSquareclass_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:08:07.887029+00:00
-- url     : https://prove2.me/theorems/ce62443a-03f1-470c-9619-b906700d90b3
-- title:
--   FLT.Assumptions.MazurProof.N13SexticSquareclass source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SexticSquareclass

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SexticSquareclass
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_FakeSquareClass_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13Mumford_p0

set_option autoImplicit false




/-!
# The rational-scalar survivor in the N13 fake square-class target

The apparent second local survivor in the weak two-descent is not a second
geometric class.  In the sextic algebra it differs from `13` by an explicit
square.  The proof first compresses the five power-basis expressions to two
degree-five polynomials `B` and `C`; it never expands the final product to
degree thirty-three.
-/

open Polynomial

namespace MazurProof.N13SexticSquareclass

noncomputable section

def f : ℚ[X] :=
  N13Mumford.f ℚ

/-- Twice the order-four torsion unit. -/
def Z : ℚ[X] := 2 * X ^ 5 + 7 * X ^ 4 + 9 * X ^ 3 + X ^ 2 + 4 * X + 3

/-- Twice the first fundamental unit. -/
def E₁ : ℚ[X] := -X ^ 5 - 3 * X ^ 4 - 3 * X ^ 3 - 3 * X

/-- Twice the second fundamental unit. -/
def E₂ : ℚ[X] := -X ^ 5 - 3 * X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 - 1

/-- Twice a generator of the ramification-three prime above 13. -/
def A : ℚ[X] := -X ^ 3 - 2 * X ^ 2 - X + 3

/-- Twice a generator of the residue-degree-three prime above 13. -/
def Q : ℚ[X] :=
  -6 * X ^ 5 - 21 * X ^ 4 - 27 * X ^ 3 - 3 * X ^ 2 - 12 * X - 5

/-- `ζ e₁ a = B / 2` in `ℚ[T]/(f)`. -/
def B : ℚ[X] := 3 * X ^ 5 + 10 * X ^ 4 + 11 * X ^ 3 - 3 * X ^ 2 + 4 * X + 6

/-- `e₂ a q = -C` in `ℚ[T]/(f)`. -/
def C : ℚ[X] := 5 * X ^ 5 + 18 * X ^ 4 + 23 * X ^ 3 - X + 4

def rB : ℚ[X] :=
  2 * X ^ 7 + 9 * X ^ 6 + 16 * X ^ 5 + 6 * X ^ 4 - 5 * X ^ 3 - X ^ 2 + 5 * X - 24

def rC : ℚ[X] :=
  -6 * X ^ 7 - 27 * X ^ 6 - 42 * X ^ 5 + 15 * X ^ 4 + 72 * X ^ 3 + 22 * X ^ 2 - 71 * X + 47

def r13 : ℚ[X] :=
  45 * X ^ 9 + 282 * X ^ 8 + 719 * X ^ 7 + 720 * X ^ 6 + 67 * X ^ 5 + 4 * X ^ 4 +
    828 * X ^ 3 + 148 * X ^ 2 - 236 * X + 196

theorem zeta_e1_a_reduction : Z * E₁ * A - 4 * B = f * rB := by
  simp [f, N13Mumford.f, Z, E₁, A, B, rB]
  ring

theorem e2_a_q_reduction : E₂ * A * Q + 8 * C = f * rC := by
  simp [f, N13Mumford.f, E₂, A, Q, C, rC]
  ring

/-- The compressed squareclass identity: in `ℚ[T]/(f)`,
`(-C) * (B / 2)^2 = 13`. -/
theorem compressed_squareclass_identity : C * B ^ 2 + 52 = f * r13 := by
  simp [f, N13Mumford.f, B, C, r13]
  ring

private theorem zeta_e1_a_scaled_reduction :
    (Polynomial.C (1 / 2 : ℚ) * Z) *
          (Polynomial.C (1 / 2 : ℚ) * E₁) *
          (Polynomial.C (1 / 2 : ℚ) * A) -
        Polynomial.C (1 / 2 : ℚ) * B =
      f * (Polynomial.C (1 / 8 : ℚ) * rB) := by
  calc
    _ = Polynomial.C (1 / 8 : ℚ) * (Z * E₁ * A - 4 * B) := by
      have hcube :
          (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 =
            Polynomial.C (1 / 8 : ℚ) := by
        rw [← map_pow]
        norm_num
      have hfour :
          (Polynomial.C (1 / 8 : ℚ) : ℚ[X]) * 4 =
            Polynomial.C (1 / 2 : ℚ) := by
        rw [show (4 : ℚ[X]) = Polynomial.C (4 : ℚ) by
              exact (map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 4).symm,
          ← map_mul]
        norm_num
      calc
        _ = (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 *
              (Z * E₁ * A) -
            Polynomial.C (1 / 2 : ℚ) * B := by ring
        _ = Polynomial.C (1 / 8 : ℚ) * (Z * E₁ * A) -
            (Polynomial.C (1 / 8 : ℚ) * 4) * B := by
              rw [hcube, hfour]
        _ = _ := by ring
    _ = Polynomial.C (1 / 8 : ℚ) * (f * rB) := by
      rw [zeta_e1_a_reduction]
    _ = _ := by ring

private theorem e2_a_q_scaled_reduction :
    (Polynomial.C (1 / 2 : ℚ) * E₂) *
          (Polynomial.C (1 / 2 : ℚ) * A) *
          (Polynomial.C (1 / 2 : ℚ) * Q) -
        (-C) =
      f * (Polynomial.C (1 / 8 : ℚ) * rC) := by
  calc
    _ = Polynomial.C (1 / 8 : ℚ) * (E₂ * A * Q + 8 * C) := by
      have hcube :
          (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 =
            Polynomial.C (1 / 8 : ℚ) := by
        rw [← map_pow]
        norm_num
      have height :
          (Polynomial.C (1 / 8 : ℚ) : ℚ[X]) * 8 = 1 := by
        rw [show (8 : ℚ[X]) = Polynomial.C (8 : ℚ) by
              exact (map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 8).symm,
          ← map_mul]
        norm_num
      calc
        _ = (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 *
              (E₂ * A * Q) + C := by ring
        _ = Polynomial.C (1 / 8 : ℚ) * (E₂ * A * Q) + 1 * C := by
              rw [hcube]
              simp
        _ = Polynomial.C (1 / 8 : ℚ) * (E₂ * A * Q) +
              (Polynomial.C (1 / 8 : ℚ) * 8) * C := by
                rw [height]
        _ = _ := by ring
    _ = Polynomial.C (1 / 8 : ℚ) * (f * rC) := by
      rw [e2_a_q_reduction]
    _ = _ := by ring

private theorem compressed_scaled_reduction :
    (-C) * (Polynomial.C (1 / 2 : ℚ) * B) ^ 2 -
        Polynomial.C (13 : ℚ) =
      f * (Polynomial.C (-1 / 4 : ℚ) * r13) := by
  calc
    _ = Polynomial.C (-1 / 4 : ℚ) * (C * B ^ 2 + 52) := by
      have hnegQuarter :
          -((Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 2) =
            Polynomial.C (-1 / 4 : ℚ) := by
        rw [← map_pow, ← map_neg]
        norm_num
      have hthirteen :
          (Polynomial.C (-1 / 4 : ℚ) : ℚ[X]) * 52 =
            -(Polynomial.C (13 : ℚ)) := by
        rw [show (52 : ℚ[X]) = Polynomial.C (52 : ℚ) by
              exact (map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 52).symm,
          ← map_mul, ← map_neg]
        norm_num
      calc
        _ = -((Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 2) *
              (C * B ^ 2) - Polynomial.C (13 : ℚ) := by ring
        _ = Polynomial.C (-1 / 4 : ℚ) * (C * B ^ 2) +
              Polynomial.C (-1 / 4 : ℚ) * 52 := by
                rw [hnegQuarter, hthirteen]
                ring
        _ = _ := by ring
    _ = Polynomial.C (-1 / 4 : ℚ) * (f * r13) := by
      rw [compressed_squareclass_identity]
    _ = _ := by ring

abbrev SexticAlgebra : Type :=
  AdjoinRoot f

def ofPoly (p : ℚ[X]) : SexticAlgebra :=
  AdjoinRoot.mk f p

def halfOfPoly (p : ℚ[X]) : SexticAlgebra :=
  ofPoly (Polynomial.C (1 / 2 : ℚ) * p)

def zeta : SexticAlgebra := halfOfPoly Z
def e1 : SexticAlgebra := halfOfPoly E₁
def e2 : SexticAlgebra := halfOfPoly E₂
def primeA : SexticAlgebra := halfOfPoly A
def primeQ : SexticAlgebra := halfOfPoly Q

private theorem ofPoly_eq_of_sub_eq_mul
    (p q r : ℚ[X]) (h : p - q = f * r) :
    ofPoly p = ofPoly q := by
  have hm := congrArg (AdjoinRoot.mk f) h
  rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul] at hm
  exact sub_eq_zero.mp hm

theorem zeta_mul_e1_mul_primeA :
    zeta * e1 * primeA = halfOfPoly B := by
  have hm := ofPoly_eq_of_sub_eq_mul
    ((Polynomial.C (1 / 2 : ℚ) * Z) *
      (Polynomial.C (1 / 2 : ℚ) * E₁) *
      (Polynomial.C (1 / 2 : ℚ) * A))
    (Polynomial.C (1 / 2 : ℚ) * B)
    (Polynomial.C (1 / 8 : ℚ) * rB)
    zeta_e1_a_scaled_reduction
  simpa [zeta, e1, primeA, halfOfPoly, ofPoly, map_mul] using hm

theorem e2_mul_primeA_mul_primeQ :
    e2 * primeA * primeQ = -(ofPoly C) := by
  have hm := ofPoly_eq_of_sub_eq_mul
    ((Polynomial.C (1 / 2 : ℚ) * E₂) *
      (Polynomial.C (1 / 2 : ℚ) * A) *
      (Polynomial.C (1 / 2 : ℚ) * Q))
    (-C)
    (Polynomial.C (1 / 8 : ℚ) * rC)
    e2_a_q_scaled_reduction
  simpa [e2, primeA, primeQ, halfOfPoly, ofPoly, map_mul] using hm

theorem compressed_scaled_identity_in_algebra :
    (-(ofPoly C)) * (halfOfPoly B) ^ 2 =
      algebraMap ℚ SexticAlgebra 13 := by
  have hm := ofPoly_eq_of_sub_eq_mul
    ((-C) * (Polynomial.C (1 / 2 : ℚ) * B) ^ 2)
    (Polynomial.C (13 : ℚ))
    (Polynomial.C (-1 / 4 : ℚ) * r13)
    compressed_scaled_reduction
  simpa [halfOfPoly, ofPoly, map_mul, map_pow] using hm

def survivor : SexticAlgebra :=
  e2 * primeA * primeQ

def squareFactor : SexticAlgebra :=
  zeta * e1 * primeA

/-- The two local representatives differ by a rational scalar and a square. -/
theorem survivor_mul_square :
    survivor * squareFactor ^ 2 =
      algebraMap ℚ SexticAlgebra 13 := by
  rw [survivor, squareFactor, e2_mul_primeA_mul_primeQ,
    zeta_mul_e1_mul_primeA]
  exact compressed_scaled_identity_in_algebra

/-- The apparent survivor therefore has trivial class in
`Lˣ / (Lˣ² · ℚˣ)`.  The equality itself proves that both displayed ring
elements are units, so irreducibility of the sextic is not needed here. -/
theorem survivor_fake_class_eq_one :
    ∃ hz : IsUnit survivor, ∃ _hs : IsUnit squareFactor,
      ((hz.unit : SexticAlgebraˣ) :
        FakeSquareClass.Target (algebraMap ℚ SexticAlgebra)) = 1 := by
  apply FakeSquareClass.exists_units_and_class_eq_one
    (algebraMap ℚ SexticAlgebra) survivor squareFactor
    (Units.mk0 (13 : ℚ) (by norm_num))
  simpa using survivor_mul_square

theorem compressed_identity_in_adjoinRoot :
    (-(AdjoinRoot.mk f C)) * (AdjoinRoot.mk f B) ^ 2 = 52 := by
  have hf : AdjoinRoot.mk f f = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (dvd_refl f)
  have h := congrArg (AdjoinRoot.mk f) compressed_squareclass_identity
  have h' : AdjoinRoot.mk f C * (AdjoinRoot.mk f B) ^ 2 + 52 = 0 := by
    rw [map_add, map_mul, map_pow, map_mul, hf, zero_mul] at h
    change AdjoinRoot.mk f C * (AdjoinRoot.mk f B) ^ 2 + 52 = 0 at h
    exact h
  calc
    -(AdjoinRoot.mk f C) * (AdjoinRoot.mk f B) ^ 2 =
        -(AdjoinRoot.mk f C * (AdjoinRoot.mk f B) ^ 2) := by ring
    _ = -(AdjoinRoot.mk f C * (AdjoinRoot.mk f B) ^ 2 + 52) + 52 := by ring
    _ = 52 := by rw [h']; simp

end

end MazurProof.N13SexticSquareclass


