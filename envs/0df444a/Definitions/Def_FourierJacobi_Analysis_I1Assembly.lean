-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I1Assembly
-- name    : FourierJacobi_Analysis_I1Assembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:25:06.308191+00:00
-- url     : https://prove2.me/theorems/34e563ab-a4fc-52a9-9472-760a4816433b
-- title:
--   I1 Assembly
-- statement:
--   Definitions and structural lemmas for I1 Assembly, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Assembly.lean

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
def i1CellValue (q t d U V T : ℂ) : Fin 17 → ℂ :=
  ![((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0),
    ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹),
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0),
    ((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹),
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹]
def i1CellSimplified (t d U V T : ℂ) : Fin 17 → ℂ :=
  ![regionTerm10 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm11 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    (1-t^2)^2 * d * (T*U) * (T * V)^2 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    (1-t^2)^2 * d * (T*U) * (T * V)^1 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    regionTerm13 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm14 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm15 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm16 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm17 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm18 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm19 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    (1-t^2)^2 * (T*U) * (T * V)^1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    (1-t^2)^2 * (T*U) * 1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    regionTerm21 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm22 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm23 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm24 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)]
def i1StoredRows (t d U V T : ℂ) : Fin 15 → ℂ :=
  ![regionTerm10 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm11 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm12 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm13 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm14 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm15 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm16 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm17 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm18 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm19 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm20 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm21 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm22 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm23 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm24 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)]
end FourierJacobi.Analysis


