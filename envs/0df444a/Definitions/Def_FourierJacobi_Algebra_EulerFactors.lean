-- Prove2me | Definitions.Def_FourierJacobi_Algebra_EulerFactors
-- name    : FourierJacobi_Algebra_EulerFactors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:40:25.011451+00:00
-- url     : https://prove2.me/theorems/a7742c66-43a9-5172-a5f9-e6478180c210
-- title:
--   Euler Factors
-- statement:
--   Definitions and structural lemmas for Euler Factors, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/EulerFactors.lean

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]
def poincare (t : K) : K := 1 + 2 * t ^ 2 + 2 * t ^ 4 + 2 * t ^ 6 + t ^ 8
def satakeNumerator (a b : K) : K := (1 + a) ^ 2 * (1 + b) ^ 2 / (a * b)
def fourFactors (a b x : K) : K :=
  (1 - a * x) * (1 - a⁻¹ * x) * (1 - b * x) * (1 - b⁻¹ * x)
def n₁ (t a b : K) : K := fourFactors a b (t ^ 2)
def n₂ (t a b : K) : K :=
  (1 - a * b * t ^ 2) * (1 - a / b * t ^ 2) *
    (1 - b / a * t ^ 2) * (1 - (a * b)⁻¹ * t ^ 2)
def d₁ (t a b d : K) : K := fourFactors a b (d * t)
def d₂ (t a b d : K) : K := fourFactors a b (t / d)
def closedCore (t a b d : K) : K :=
  satakeNumerator a b * (1 - t ^ 2) * n₁ t a b * n₂ t a b /
    (poincare t * d₁ t a b d * d₂ t a b d)
def piAdjointInverse (t a b : K) : K := (1 - t ^ 2) ^ 2 * n₁ t a b * n₂ t a b
def principalAdjointInverse (t d : K) : K :=
  (1 - d * t) * (1 + d * t) * (1 - t ^ 2) * (1 - t / d) * (1 + t / d)
def principalTensorInverse (t a b d : K) : K :=
  (1 - d * t) * (1 - t / d) * d₁ t a b d * d₂ t a b d
def principalNormalizer (t a b d : K) : K :=
  (1 - t ^ 4) * (1 - t ^ 8) * principalTensorInverse t a b d /
    (piAdjointInverse t a b * principalAdjointInverse t d)
def specialTensorInverse (t a b e : K) : K :=
  (1 - e * t ^ 2) * fourFactors a b (e * t ^ 2)
def specialNormalizer (t a b e : K) : K :=
  (1 - t ^ 4) * (1 - t ^ 8) * specialTensorInverse t a b e /
    (piAdjointInverse t a b * (1 - t ^ 4))
end Algebra
end FourierJacobi


