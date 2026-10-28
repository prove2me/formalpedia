-- Prove2me | Definitions.Def_BitDFT_Numerics
-- name    : BitDFT_Numerics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T12:00:52.990991+00:00
-- url     : https://prove2.me/theorems/d999b0e5-8273-4148-a198-2898540884bc
-- title:
--   Numerical Fourier specification and complete transfer cost
-- statement:
--   Fixed-point Gaussian pairs, unit-disc and ulp-error predicates, rounding compatibility, complex roots, normalised and unnormalised DFT specifications, normalised middle convolution, guard precision, binary transform inputs and the explicit bound T(np)+nT(p)+p lg(p)^2+np. No machine or complexity result is assumed by these definitions.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations.

import Definitions.Def_IntMul_HvdH_FixedPoint
import Definitions.Def_BitDFT_Encoding

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace BitDFT

def value (p : ℕ) (z : ℤ × ℤ) : ℂ :=
  ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / (2 : ℂ) ^ p

def inDisc (p : ℕ) (z : ℤ × ℤ) : Prop := ‖value p z‖ ≤ 1
def vectorDisc {n : ℕ} (p : ℕ) (U : Fin n → ℤ × ℤ) : Prop := ∀ j, inDisc p (U j)

def ulpError (p : ℕ) (z : ℤ × ℤ) (x : ℂ) : ℝ := (2 : ℝ) ^ p * ‖value p z - x‖

def approx {n : ℕ} (p : ℕ) (U : Fin n → ℤ × ℤ) (X : Fin n → ℂ) (e : ℝ) : Prop :=
  ∀ j, ulpError p (U j) (X j) ≤ e

def roundPair (p : ℕ) (z : ℂ) : ℤ × ℤ :=
  (IntMul.HvdH.rho0 (((2 : ℂ) ^ p * z).re),
   IntMul.HvdH.rho0 (((2 : ℂ) ^ p * z).im))

def root (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

/-- Standard negative-sign, unnormalised DFT. -/
def dft {n : ℕ} (X : Fin n → ℂ) : Fin n → ℂ :=
  fun k => ∑ j, (root n) ^ (-((j.val * k.val : ℕ) : ℤ)) * X j

/-- Normalisation used in Harvey--van der Hoeven 2025, equation (3.1). -/
def ndft {n : ℕ} (X : Fin n → ℂ) : Fin n → ℂ := fun k => dft X k / (n : ℂ)

def middle {n : ℕ} (F : Fin n → ℂ) (G : Fin (2 * n - 1) → ℂ) : Fin n → ℂ :=
  fun k => (∑ j : Fin n, F j *
    (if h : k.val + n - 1 - j.val < 2 * n - 1 then G ⟨k.val + n - 1 - j.val, h⟩ else 0)) / (n : ℂ)

/-- Working precision for an absolute 2^-b error in the unnormalised DFT. -/
def guardPrecision (n b : ℕ) : ℕ := b + 3 * IntMul.lg n + 5

/-- All costs remain visible, including root computation and linear tape work. -/
def transferCost (T : ℕ → ℝ) (n p : ℕ) : ℝ :=
  T (n * p) + (n : ℝ) * T p + (p : ℝ) * (IntMul.lg p : ℝ) ^ 2 + (n : ℝ) * p

def fourierInput {n : ℕ} (p : ℕ) (U : Fin n → ℤ × ℤ) : List Bool :=
  encNat n ++ encNat p ++ encVector (p + 1) U

def requestedInput {n : ℕ} (b : ℕ) (U : Fin n → ℤ × ℤ) : List Bool :=
  encNat n ++ encNat b ++ encVector (guardPrecision n b + 1) U

end BitDFT


