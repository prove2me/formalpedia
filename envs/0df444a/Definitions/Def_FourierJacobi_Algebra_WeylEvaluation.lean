-- Prove2me | Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
-- name    : FourierJacobi_Algebra_WeylEvaluation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:12:39.205794+00:00
-- url     : https://prove2.me/theorems/f5f3b7f0-ccb4-4c2f-8e91-dabb5f093786
-- title:
--   Weyl Evaluation
-- statement:
--   Definitions and structural lemmas for Weyl Evaluation, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean

import Definitions.Def_FourierJacobi_Algebra_WeylSum
set_option autoImplicit false
namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
def weylScale (a b : K) : Fin 8 → K := ![1, 1, 1, b ^ 2, 1, a ^ 2, b ^ 2, a ^ 2]
def weylKernelDenominator (t a b d : K) (i : Fin 8) : K :=
  d ^ 2 * (1 - d * weylV a b i * t) * (1 - weylV a b i * t / d)
def tensorDenominatorPolynomial (t a b d : K) : K :=
  (1 - a * d * t) * (a - d * t) * (1 - b * d * t) * (b - d * t) *
    (d - a * t) * (a * d - t) * (d - b * t) * (b * d - t)
def weylClosedExpression (t a b d : K) : K :=
  satakeNumerator a b * (1 - t ^ 2) * n₁ t a b * n₂ t a b /
    (d₁ t a b d * d₂ t a b d)
def weylL (a b : K) : Fin 8 → K := ![a * b, a * b, a, a, b, b, 1, 1]
end Algebra
end FourierJacobi


