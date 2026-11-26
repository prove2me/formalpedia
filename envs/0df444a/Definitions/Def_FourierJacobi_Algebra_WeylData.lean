-- Prove2me | Definitions.Def_FourierJacobi_Algebra_WeylData
-- name    : FourierJacobi_Algebra_WeylData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:50:48.098095+00:00
-- url     : https://prove2.me/theorems/0080feb2-14d1-5024-81c9-027390348895
-- title:
--   Weyl Data
-- statement:
--   Definitions and structural lemmas for Weyl Data, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylData.lean

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
set_option autoImplicit false
namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def weylWall (a b : K) : K := (a - 1) * (a - b) * (b - 1) * (a * b - 1)
def rootFactor (t z : K) : K := (1 - t ^ 2 * z) / (1 - z)
def weylWeights (t a b : K) : Fin 8 → K :=
  ![rootFactor t (b * ((a ^ 1)⁻¹)) * rootFactor t ((b ^ 1)⁻¹) * rootFactor t (((a ^ 1)⁻¹) * ((b ^ 1)⁻¹)) * rootFactor t ((a ^ 1)⁻¹),
    rootFactor t (a * ((b ^ 1)⁻¹)) * rootFactor t ((a ^ 1)⁻¹) * rootFactor t (((a ^ 1)⁻¹) * ((b ^ 1)⁻¹)) * rootFactor t ((b ^ 1)⁻¹),
    rootFactor t (((a ^ 1)⁻¹) * ((b ^ 1)⁻¹)) * rootFactor t b * rootFactor t (b * ((a ^ 1)⁻¹)) * rootFactor t ((a ^ 1)⁻¹),
    rootFactor t (a * b) * rootFactor t ((a ^ 1)⁻¹) * rootFactor t (b * ((a ^ 1)⁻¹)) * rootFactor t b,
    rootFactor t (((a ^ 1)⁻¹) * ((b ^ 1)⁻¹)) * rootFactor t a * rootFactor t (a * ((b ^ 1)⁻¹)) * rootFactor t ((b ^ 1)⁻¹),
    rootFactor t (a * b) * rootFactor t ((b ^ 1)⁻¹) * rootFactor t (a * ((b ^ 1)⁻¹)) * rootFactor t a,
    rootFactor t (b * ((a ^ 1)⁻¹)) * rootFactor t a * rootFactor t (a * b) * rootFactor t b,
    rootFactor t (a * ((b ^ 1)⁻¹)) * rootFactor t b * rootFactor t (a * b) * rootFactor t a]
def weylU (a b : K) : Fin 8 → K := ![(a * b),
    (a * b),
    (a * ((b ^ 1)⁻¹)),
    (a * ((b ^ 1)⁻¹)),
    (b * ((a ^ 1)⁻¹)),
    (b * ((a ^ 1)⁻¹)),
    (((a ^ 1)⁻¹) * ((b ^ 1)⁻¹)),
    (((a ^ 1)⁻¹) * ((b ^ 1)⁻¹))]
def weylV (a b : K) : Fin 8 → K := ![a,
    b,
    a,
    ((b ^ 1)⁻¹),
    b,
    ((a ^ 1)⁻¹),
    ((b ^ 1)⁻¹),
    ((a ^ 1)⁻¹)]
def weylTerms (t a b d : K) (i : Fin 8) : K :=
  weylWeights t a b i * regionKernel t d (weylU a b i) (weylV a b i)
@[irreducible] def weylWeightNumerators (t a b : K) : Fin 8 → K := ![(((t ^ 2) + ((-1) * a)) * ((t ^ 2) + ((-1) * b)) * ((t ^ 2) + ((-1) * a * b)) * (((-1) * a) + (b * (t ^ 2)))),
    ((-1) * ((t ^ 2) + ((-1) * a)) * ((t ^ 2) + ((-1) * b)) * ((t ^ 2) + ((-1) * a * b)) * (((-1) * b) + (a * (t ^ 2)))),
    ((-1) * ((-1) + (b * (t ^ 2))) * ((t ^ 2) + ((-1) * a)) * ((t ^ 2) + ((-1) * a * b)) * (((-1) * a) + (b * (t ^ 2)))),
    (((-1) + (b * (t ^ 2))) * ((-1) + (a * b * (t ^ 2))) * ((t ^ 2) + ((-1) * a)) * (((-1) * a) + (b * (t ^ 2)))),
    (((-1) + (a * (t ^ 2))) * ((t ^ 2) + ((-1) * b)) * ((t ^ 2) + ((-1) * a * b)) * (((-1) * b) + (a * (t ^ 2)))),
    ((-1) * ((-1) + (a * (t ^ 2))) * ((-1) + (a * b * (t ^ 2))) * ((t ^ 2) + ((-1) * b)) * (((-1) * b) + (a * (t ^ 2)))),
    ((-1) * ((-1) + (a * (t ^ 2))) * ((-1) + (b * (t ^ 2))) * ((-1) + (a * b * (t ^ 2))) * (((-1) * a) + (b * (t ^ 2)))),
    (((-1) + (a * (t ^ 2))) * ((-1) + (b * (t ^ 2))) * ((-1) + (a * b * (t ^ 2))) * (((-1) * b) + (a * (t ^ 2))))]
def weylHeight0 (t a b d : K) : K := (((a ^ 2) * (b ^ 2) * (d ^ 2)) + ((a ^ 3) * (b ^ 2) * (d ^ 2)) + ((a ^ 3) * (b ^ 3) * (d ^ 2)) + ((a ^ 5) * (b ^ 3) * (t ^ 6)) + ((-1) * (a ^ 4) * (b ^ 4) * (t ^ 4)) + (d * t * (a ^ 3) * (b ^ 3)) + (d * (a ^ 4) * (b ^ 2) * (t ^ 5)) + (d * (a ^ 4) * (b ^ 4) * (t ^ 5)) + (d * (a ^ 5) * (b ^ 2) * (t ^ 5)) + (d * (a ^ 5) * (b ^ 3) * (t ^ 5)) + (d * (a ^ 5) * (b ^ 4) * (t ^ 5)) + (t * (a ^ 3) * (b ^ 3) * (d ^ 3)) + ((a ^ 4) * (b ^ 2) * (d ^ 3) * (t ^ 5)) + ((a ^ 4) * (b ^ 3) * (d ^ 2) * (t ^ 4)) + ((a ^ 4) * (b ^ 3) * (d ^ 2) * (t ^ 6)) + ((a ^ 4) * (b ^ 4) * (d ^ 3) * (t ^ 5)) + ((a ^ 5) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((a ^ 5) * (b ^ 2) * (d ^ 3) * (t ^ 5)) + ((a ^ 5) * (b ^ 3) * (d ^ 2) * (t ^ 4)) + ((a ^ 5) * (b ^ 3) * (d ^ 2) * (t ^ 6)) + ((a ^ 5) * (b ^ 3) * (d ^ 3) * (t ^ 5)) + ((a ^ 5) * (b ^ 3) * (d ^ 4) * (t ^ 6)) + ((a ^ 5) * (b ^ 4) * (d ^ 2) * (t ^ 4)) + ((a ^ 5) * (b ^ 4) * (d ^ 3) * (t ^ 5)) + ((a ^ 6) * (b ^ 3) * (d ^ 2) * (t ^ 8)) + ((-1) * d * (a ^ 3) * (b ^ 3) * (t ^ 3)) + ((-1) * d * (a ^ 4) * (b ^ 2) * (t ^ 3)) + ((-1) * d * (a ^ 4) * (b ^ 3) * (t ^ 3)) + ((-1) * d * (a ^ 4) * (b ^ 4) * (t ^ 3)) + ((-1) * d * (a ^ 5) * (b ^ 3) * (t ^ 7)) + ((-1) * d * (a ^ 6) * (b ^ 3) * (t ^ 7)) + ((-1) * (a ^ 3) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 3) * (b ^ 3) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 3) * (b ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 4) * (b ^ 2) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 4) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 4) * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 4) * (b ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 4) * (b ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 4) * (b ^ 4) * (d ^ 4) * (t ^ 4)) + ((-1) * (a ^ 5) * (b ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 5) * (b ^ 3) * (d ^ 3) * (t ^ 7)) + ((-1) * (a ^ 5) * (b ^ 4) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 6) * (b ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 6) * (b ^ 3) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 6) * (b ^ 3) * (d ^ 3) * (t ^ 7)) + ((-2) * (a ^ 4) * (b ^ 3) * (d ^ 2) * (t ^ 2)))
def weylHeight1 (t a b d : K) : K := (((a ^ 2) * (b ^ 2) * (d ^ 2)) + ((a ^ 2) * (b ^ 3) * (d ^ 2)) + ((a ^ 3) * (b ^ 3) * (d ^ 2)) + ((a ^ 3) * (b ^ 5) * (t ^ 6)) + ((-1) * (a ^ 4) * (b ^ 4) * (t ^ 4)) + (d * t * (a ^ 3) * (b ^ 3)) + (d * (a ^ 2) * (b ^ 4) * (t ^ 5)) + (d * (a ^ 2) * (b ^ 5) * (t ^ 5)) + (d * (a ^ 3) * (b ^ 5) * (t ^ 5)) + (d * (a ^ 4) * (b ^ 4) * (t ^ 5)) + (d * (a ^ 4) * (b ^ 5) * (t ^ 5)) + (t * (a ^ 3) * (b ^ 3) * (d ^ 3)) + ((a ^ 2) * (b ^ 4) * (d ^ 3) * (t ^ 5)) + ((a ^ 2) * (b ^ 5) * (d ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 5) * (d ^ 3) * (t ^ 5)) + ((a ^ 3) * (b ^ 4) * (d ^ 2) * (t ^ 4)) + ((a ^ 3) * (b ^ 4) * (d ^ 2) * (t ^ 6)) + ((a ^ 3) * (b ^ 5) * (d ^ 2) * (t ^ 4)) + ((a ^ 3) * (b ^ 5) * (d ^ 2) * (t ^ 6)) + ((a ^ 3) * (b ^ 5) * (d ^ 3) * (t ^ 5)) + ((a ^ 3) * (b ^ 5) * (d ^ 4) * (t ^ 6)) + ((a ^ 3) * (b ^ 6) * (d ^ 2) * (t ^ 8)) + ((a ^ 4) * (b ^ 4) * (d ^ 3) * (t ^ 5)) + ((a ^ 4) * (b ^ 5) * (d ^ 2) * (t ^ 4)) + ((a ^ 4) * (b ^ 5) * (d ^ 3) * (t ^ 5)) + ((-1) * d * (a ^ 2) * (b ^ 4) * (t ^ 3)) + ((-1) * d * (a ^ 3) * (b ^ 3) * (t ^ 3)) + ((-1) * d * (a ^ 3) * (b ^ 4) * (t ^ 3)) + ((-1) * d * (a ^ 3) * (b ^ 5) * (t ^ 7)) + ((-1) * d * (a ^ 3) * (b ^ 6) * (t ^ 7)) + ((-1) * d * (a ^ 4) * (b ^ 4) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 3) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 4) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 5) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 2) * (b ^ 6) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 3) * (b ^ 3) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 3) * (b ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 3) * (b ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 3) * (b ^ 5) * (d ^ 3) * (t ^ 7)) + ((-1) * (a ^ 3) * (b ^ 6) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 3) * (b ^ 6) * (d ^ 3) * (t ^ 7)) + ((-1) * (a ^ 4) * (b ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 4) * (b ^ 4) * (d ^ 4) * (t ^ 4)) + ((-1) * (a ^ 4) * (b ^ 5) * (d ^ 2) * (t ^ 6)) + ((-2) * (a ^ 3) * (b ^ 4) * (d ^ 2) * (t ^ 2)))
def weylHeight2 (t a b d : K) : K := (((-1) * (a ^ 4) * (t ^ 4)) + (b * (a ^ 3) * (d ^ 2)) + (b * (a ^ 5) * (t ^ 6)) + (d * (a ^ 4) * (t ^ 5)) + (d * (a ^ 5) * (t ^ 5)) + ((a ^ 2) * (b ^ 2) * (d ^ 2)) + ((a ^ 3) * (b ^ 2) * (d ^ 2)) + ((a ^ 4) * (d ^ 3) * (t ^ 5)) + ((a ^ 5) * (d ^ 2) * (t ^ 4)) + ((a ^ 5) * (d ^ 3) * (t ^ 5)) + ((-1) * d * (a ^ 4) * (t ^ 3)) + ((-1) * (a ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 4) * (d ^ 4) * (t ^ 4)) + ((-1) * (a ^ 5) * (d ^ 2) * (t ^ 6)) + (b * d * t * (a ^ 3)) + (b * d * (a ^ 5) * (t ^ 5)) + (b * t * (a ^ 3) * (d ^ 3)) + (b * (a ^ 4) * (d ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (d ^ 2) * (t ^ 6)) + (b * (a ^ 5) * (d ^ 2) * (t ^ 4)) + (b * (a ^ 5) * (d ^ 2) * (t ^ 6)) + (b * (a ^ 5) * (d ^ 3) * (t ^ 5)) + (b * (a ^ 5) * (d ^ 4) * (t ^ 6)) + (b * (a ^ 6) * (d ^ 2) * (t ^ 8)) + (d * (a ^ 4) * (b ^ 2) * (t ^ 5)) + (d * (a ^ 5) * (b ^ 2) * (t ^ 5)) + ((a ^ 4) * (b ^ 2) * (d ^ 3) * (t ^ 5)) + ((a ^ 5) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((a ^ 5) * (b ^ 2) * (d ^ 3) * (t ^ 5)) + ((-1) * b * d * (a ^ 3) * (t ^ 3)) + ((-1) * b * d * (a ^ 4) * (t ^ 3)) + ((-1) * b * d * (a ^ 5) * (t ^ 7)) + ((-1) * b * d * (a ^ 6) * (t ^ 7)) + ((-1) * b * (a ^ 3) * (d ^ 2) * (t ^ 2)) + ((-1) * b * (a ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * b * (a ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * b * (a ^ 5) * (d ^ 3) * (t ^ 7)) + ((-1) * b * (a ^ 6) * (d ^ 2) * (t ^ 6)) + ((-1) * b * (a ^ 6) * (d ^ 3) * (t ^ 7)) + ((-1) * d * (a ^ 4) * (b ^ 2) * (t ^ 3)) + ((-1) * (a ^ 3) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 4) * (b ^ 2) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 4) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 4) * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 5) * (b ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 6) * (b ^ 2) * (d ^ 2) * (t ^ 6)) + ((-2) * b * (a ^ 4) * (d ^ 2) * (t ^ 2)))
def weylHeight3 (t a b d : K) : K := ((b * (a ^ 3) * (t ^ 6)) + ((a ^ 2) * (b ^ 3) * (d ^ 2)) + ((a ^ 2) * (b ^ 4) * (d ^ 2)) + ((a ^ 3) * (b ^ 3) * (d ^ 2)) + ((a ^ 3) * (d ^ 2) * (t ^ 8)) + ((-1) * d * (a ^ 3) * (t ^ 7)) + ((-1) * (a ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 3) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 3) * (d ^ 3) * (t ^ 7)) + ((-1) * (a ^ 4) * (b ^ 2) * (t ^ 4)) + (b * d * (a ^ 2) * (t ^ 5)) + (b * d * (a ^ 3) * (t ^ 5)) + (b * d * (a ^ 4) * (t ^ 5)) + (b * (a ^ 2) * (d ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (d ^ 3) * (t ^ 5)) + (b * (a ^ 3) * (d ^ 2) * (t ^ 4)) + (b * (a ^ 3) * (d ^ 2) * (t ^ 6)) + (b * (a ^ 3) * (d ^ 3) * (t ^ 5)) + (b * (a ^ 3) * (d ^ 4) * (t ^ 6)) + (b * (a ^ 4) * (d ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (d ^ 3) * (t ^ 5)) + (d * t * (a ^ 3) * (b ^ 3)) + (d * (a ^ 2) * (b ^ 2) * (t ^ 5)) + (d * (a ^ 4) * (b ^ 2) * (t ^ 5)) + (t * (a ^ 3) * (b ^ 3) * (d ^ 3)) + ((a ^ 2) * (b ^ 2) * (d ^ 3) * (t ^ 5)) + ((a ^ 3) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((a ^ 3) * (b ^ 2) * (d ^ 2) * (t ^ 6)) + ((a ^ 4) * (b ^ 2) * (d ^ 3) * (t ^ 5)) + ((-1) * b * d * (a ^ 3) * (t ^ 7)) + ((-1) * b * (a ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * b * (a ^ 3) * (d ^ 3) * (t ^ 7)) + ((-1) * b * (a ^ 4) * (d ^ 2) * (t ^ 6)) + ((-1) * d * (a ^ 2) * (b ^ 2) * (t ^ 3)) + ((-1) * d * (a ^ 3) * (b ^ 2) * (t ^ 3)) + ((-1) * d * (a ^ 3) * (b ^ 3) * (t ^ 3)) + ((-1) * d * (a ^ 4) * (b ^ 2) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 3) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 3) * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 3) * (b ^ 3) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 3) * (b ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 4) * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 4) * (b ^ 2) * (d ^ 4) * (t ^ 4)) + ((-2) * (a ^ 3) * (b ^ 2) * (d ^ 2) * (t ^ 2)))
def weylHeight4 (t a b d : K) : K := (((-1) * (b ^ 4) * (t ^ 4)) + (a * (b ^ 3) * (d ^ 2)) + (a * (b ^ 5) * (t ^ 6)) + (d * (b ^ 4) * (t ^ 5)) + (d * (b ^ 5) * (t ^ 5)) + ((a ^ 2) * (b ^ 2) * (d ^ 2)) + ((a ^ 2) * (b ^ 3) * (d ^ 2)) + ((b ^ 4) * (d ^ 3) * (t ^ 5)) + ((b ^ 5) * (d ^ 2) * (t ^ 4)) + ((b ^ 5) * (d ^ 3) * (t ^ 5)) + ((-1) * d * (b ^ 4) * (t ^ 3)) + ((-1) * (b ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * (b ^ 4) * (d ^ 4) * (t ^ 4)) + ((-1) * (b ^ 5) * (d ^ 2) * (t ^ 6)) + (a * d * t * (b ^ 3)) + (a * d * (b ^ 5) * (t ^ 5)) + (a * t * (b ^ 3) * (d ^ 3)) + (a * (b ^ 4) * (d ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (d ^ 2) * (t ^ 6)) + (a * (b ^ 5) * (d ^ 2) * (t ^ 4)) + (a * (b ^ 5) * (d ^ 2) * (t ^ 6)) + (a * (b ^ 5) * (d ^ 3) * (t ^ 5)) + (a * (b ^ 5) * (d ^ 4) * (t ^ 6)) + (a * (b ^ 6) * (d ^ 2) * (t ^ 8)) + (d * (a ^ 2) * (b ^ 4) * (t ^ 5)) + (d * (a ^ 2) * (b ^ 5) * (t ^ 5)) + ((a ^ 2) * (b ^ 4) * (d ^ 3) * (t ^ 5)) + ((a ^ 2) * (b ^ 5) * (d ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 5) * (d ^ 3) * (t ^ 5)) + ((-1) * a * d * (b ^ 3) * (t ^ 3)) + ((-1) * a * d * (b ^ 4) * (t ^ 3)) + ((-1) * a * d * (b ^ 5) * (t ^ 7)) + ((-1) * a * d * (b ^ 6) * (t ^ 7)) + ((-1) * a * (b ^ 3) * (d ^ 2) * (t ^ 2)) + ((-1) * a * (b ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * a * (b ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * a * (b ^ 5) * (d ^ 3) * (t ^ 7)) + ((-1) * a * (b ^ 6) * (d ^ 2) * (t ^ 6)) + ((-1) * a * (b ^ 6) * (d ^ 3) * (t ^ 7)) + ((-1) * d * (a ^ 2) * (b ^ 4) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 3) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 4) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 5) * (d ^ 2) * (t ^ 6)) + ((-1) * (a ^ 2) * (b ^ 6) * (d ^ 2) * (t ^ 6)) + ((-2) * a * (b ^ 4) * (d ^ 2) * (t ^ 2)))
def weylHeight5 (t a b d : K) : K := ((a * (b ^ 3) * (t ^ 6)) + ((a ^ 3) * (b ^ 2) * (d ^ 2)) + ((a ^ 3) * (b ^ 3) * (d ^ 2)) + ((a ^ 4) * (b ^ 2) * (d ^ 2)) + ((b ^ 3) * (d ^ 2) * (t ^ 8)) + ((-1) * d * (b ^ 3) * (t ^ 7)) + ((-1) * (a ^ 2) * (b ^ 4) * (t ^ 4)) + ((-1) * (b ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * (b ^ 3) * (d ^ 2) * (t ^ 6)) + ((-1) * (b ^ 3) * (d ^ 3) * (t ^ 7)) + (a * d * (b ^ 2) * (t ^ 5)) + (a * d * (b ^ 3) * (t ^ 5)) + (a * d * (b ^ 4) * (t ^ 5)) + (a * (b ^ 2) * (d ^ 2) * (t ^ 4)) + (a * (b ^ 2) * (d ^ 3) * (t ^ 5)) + (a * (b ^ 3) * (d ^ 2) * (t ^ 4)) + (a * (b ^ 3) * (d ^ 2) * (t ^ 6)) + (a * (b ^ 3) * (d ^ 3) * (t ^ 5)) + (a * (b ^ 3) * (d ^ 4) * (t ^ 6)) + (a * (b ^ 4) * (d ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (d ^ 3) * (t ^ 5)) + (d * t * (a ^ 3) * (b ^ 3)) + (d * (a ^ 2) * (b ^ 2) * (t ^ 5)) + (d * (a ^ 2) * (b ^ 4) * (t ^ 5)) + (t * (a ^ 3) * (b ^ 3) * (d ^ 3)) + ((a ^ 2) * (b ^ 2) * (d ^ 3) * (t ^ 5)) + ((a ^ 2) * (b ^ 3) * (d ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 3) * (d ^ 2) * (t ^ 6)) + ((a ^ 2) * (b ^ 4) * (d ^ 3) * (t ^ 5)) + ((-1) * a * d * (b ^ 3) * (t ^ 7)) + ((-1) * a * (b ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * a * (b ^ 3) * (d ^ 3) * (t ^ 7)) + ((-1) * a * (b ^ 4) * (d ^ 2) * (t ^ 6)) + ((-1) * d * (a ^ 2) * (b ^ 2) * (t ^ 3)) + ((-1) * d * (a ^ 2) * (b ^ 3) * (t ^ 3)) + ((-1) * d * (a ^ 2) * (b ^ 4) * (t ^ 3)) + ((-1) * d * (a ^ 3) * (b ^ 3) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 4) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 4) * (d ^ 4) * (t ^ 4)) + ((-1) * (a ^ 3) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 3) * (b ^ 3) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 3) * (b ^ 3) * (d ^ 3) * (t ^ 3)) + ((-2) * (a ^ 2) * (b ^ 3) * (d ^ 2) * (t ^ 2)))
def weylHeight6 (t a b d : K) : K := (((-1) * (b ^ 2) * (t ^ 4)) + (a * b * (t ^ 6)) + (a * (b ^ 3) * (d ^ 2)) + (a * (d ^ 2) * (t ^ 8)) + (b * d * (t ^ 5)) + (b * (d ^ 2) * (t ^ 4)) + (b * (d ^ 3) * (t ^ 5)) + (d * (b ^ 2) * (t ^ 5)) + ((a ^ 2) * (b ^ 3) * (d ^ 2)) + ((a ^ 2) * (b ^ 4) * (d ^ 2)) + ((b ^ 2) * (d ^ 3) * (t ^ 5)) + ((-1) * a * d * (t ^ 7)) + ((-1) * a * (d ^ 2) * (t ^ 6)) + ((-1) * a * (d ^ 3) * (t ^ 7)) + ((-1) * b * (d ^ 2) * (t ^ 6)) + ((-1) * d * (b ^ 2) * (t ^ 3)) + ((-1) * (a ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (b ^ 2) * (d ^ 4) * (t ^ 4)) + (a * b * d * (t ^ 5)) + (a * b * (d ^ 2) * (t ^ 4)) + (a * b * (d ^ 2) * (t ^ 6)) + (a * b * (d ^ 3) * (t ^ 5)) + (a * b * (d ^ 4) * (t ^ 6)) + (a * d * t * (b ^ 3)) + (a * t * (b ^ 3) * (d ^ 3)) + (a * (b ^ 2) * (d ^ 2) * (t ^ 4)) + (a * (b ^ 2) * (d ^ 2) * (t ^ 6)) + (b * d * (a ^ 2) * (t ^ 5)) + (b * (a ^ 2) * (d ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (d ^ 3) * (t ^ 5)) + (d * (a ^ 2) * (b ^ 2) * (t ^ 5)) + ((a ^ 2) * (b ^ 2) * (d ^ 3) * (t ^ 5)) + ((-1) * a * b * d * (t ^ 7)) + ((-1) * a * b * (d ^ 3) * (t ^ 7)) + ((-1) * a * d * (b ^ 2) * (t ^ 3)) + ((-1) * a * d * (b ^ 3) * (t ^ 3)) + ((-1) * a * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * a * (b ^ 3) * (d ^ 2) * (t ^ 2)) + ((-1) * a * (b ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * b * (a ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * d * (a ^ 2) * (b ^ 2) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 3) * (d ^ 2) * (t ^ 4)) + ((-2) * a * (b ^ 2) * (d ^ 2) * (t ^ 2)))
def weylHeight7 (t a b d : K) : K := (((-1) * (a ^ 2) * (t ^ 4)) + (a * b * (t ^ 6)) + (a * d * (t ^ 5)) + (a * (d ^ 2) * (t ^ 4)) + (a * (d ^ 3) * (t ^ 5)) + (b * (a ^ 3) * (d ^ 2)) + (b * (d ^ 2) * (t ^ 8)) + (d * (a ^ 2) * (t ^ 5)) + ((a ^ 2) * (d ^ 3) * (t ^ 5)) + ((a ^ 3) * (b ^ 2) * (d ^ 2)) + ((a ^ 4) * (b ^ 2) * (d ^ 2)) + ((-1) * a * (d ^ 2) * (t ^ 6)) + ((-1) * b * d * (t ^ 7)) + ((-1) * b * (d ^ 2) * (t ^ 6)) + ((-1) * b * (d ^ 3) * (t ^ 7)) + ((-1) * d * (a ^ 2) * (t ^ 3)) + ((-1) * (a ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 2) * (d ^ 4) * (t ^ 4)) + ((-1) * (b ^ 2) * (d ^ 2) * (t ^ 6)) + (a * b * d * (t ^ 5)) + (a * b * (d ^ 2) * (t ^ 4)) + (a * b * (d ^ 2) * (t ^ 6)) + (a * b * (d ^ 3) * (t ^ 5)) + (a * b * (d ^ 4) * (t ^ 6)) + (a * d * (b ^ 2) * (t ^ 5)) + (a * (b ^ 2) * (d ^ 2) * (t ^ 4)) + (a * (b ^ 2) * (d ^ 3) * (t ^ 5)) + (b * d * t * (a ^ 3)) + (b * t * (a ^ 3) * (d ^ 3)) + (b * (a ^ 2) * (d ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (d ^ 2) * (t ^ 6)) + (d * (a ^ 2) * (b ^ 2) * (t ^ 5)) + ((a ^ 2) * (b ^ 2) * (d ^ 3) * (t ^ 5)) + ((-1) * a * b * d * (t ^ 7)) + ((-1) * a * b * (d ^ 3) * (t ^ 7)) + ((-1) * a * (b ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * b * d * (a ^ 2) * (t ^ 3)) + ((-1) * b * d * (a ^ 3) * (t ^ 3)) + ((-1) * b * (a ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * b * (a ^ 3) * (d ^ 2) * (t ^ 2)) + ((-1) * b * (a ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * d * (a ^ 2) * (b ^ 2) * (t ^ 3)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * (a ^ 3) * (b ^ 2) * (d ^ 2) * (t ^ 4)) + ((-2) * b * (a ^ 2) * (d ^ 2) * (t ^ 2)))
def weylHeightNumerators (t a b d : K) : Fin 8 → K := ![weylHeight0 t a b d, weylHeight1 t a b d, weylHeight2 t a b d, weylHeight3 t a b d, weylHeight4 t a b d, weylHeight5 t a b d, weylHeight6 t a b d, weylHeight7 t a b d]
def weylRemainingFactors (t a b d : K) : Fin 8 → K := ![((1 + ((-1) * b * d * t)) * (a + ((-1) * d * t)) * (b + ((-1) * d * t)) * (d + ((-1) * b * t)) * (((-1) * t) + (a * d)) * (((-1) * t) + (b * d))),
    ((1 + ((-1) * a * d * t)) * (a + ((-1) * d * t)) * (b + ((-1) * d * t)) * (d + ((-1) * a * t)) * (((-1) * t) + (a * d)) * (((-1) * t) + (b * d))),
    ((1 + ((-1) * b * d * t)) * (a + ((-1) * d * t)) * (b + ((-1) * d * t)) * (d + ((-1) * b * t)) * (((-1) * t) + (a * d)) * (((-1) * t) + (b * d))),
    ((1 + ((-1) * a * d * t)) * (1 + ((-1) * b * d * t)) * (a + ((-1) * d * t)) * (d + ((-1) * a * t)) * (d + ((-1) * b * t)) * (((-1) * t) + (a * d))),
    ((1 + ((-1) * a * d * t)) * (a + ((-1) * d * t)) * (b + ((-1) * d * t)) * (d + ((-1) * a * t)) * (((-1) * t) + (a * d)) * (((-1) * t) + (b * d))),
    ((1 + ((-1) * a * d * t)) * (1 + ((-1) * b * d * t)) * (b + ((-1) * d * t)) * (d + ((-1) * a * t)) * (d + ((-1) * b * t)) * (((-1) * t) + (b * d))),
    ((1 + ((-1) * a * d * t)) * (1 + ((-1) * b * d * t)) * (a + ((-1) * d * t)) * (d + ((-1) * a * t)) * (d + ((-1) * b * t)) * (((-1) * t) + (a * d))),
    ((1 + ((-1) * a * d * t)) * (1 + ((-1) * b * d * t)) * (b + ((-1) * d * t)) * (d + ((-1) * a * t)) * (d + ((-1) * b * t)) * (((-1) * t) + (b * d)))]
def weylClearedTerms (t a b d : K) (i : Fin 8) : K :=
  weylWeightNumerators t a b i * weylHeightNumerators t a b d i *
    weylRemainingFactors t a b d i
def weylCommonDenominator (t a b d : K) : K :=
  weylWall a b * a ^ 2 * b ^ 2 * d * ((1 + ((-1) * a * d * t)) * (1 + ((-1) * b * d * t)) * (a + ((-1) * d * t)) * (b + ((-1) * d * t)) * (d + ((-1) * a * t)) * (d + ((-1) * b * t)) * (((-1) * t) + (a * d)) * (((-1) * t) + (b * d)))
def weylTargetNumerator (t a b d : K) : K := ((d ^ 5) * ((1 + a) ^ 2) * ((1 + b) ^ 2) * (1 + ((-1) * (t ^ 2))) * (1 + ((-1) * a * (t ^ 2))) * (1 + ((-1) * b * (t ^ 2))) * (1 + ((-1) * a * b * (t ^ 2))) * ((-1) + a) * ((-1) + b) * ((-1) + (a * b)) * (a + ((-1) * b)) * (a + ((-1) * (t ^ 2))) * (a + ((-1) * b * (t ^ 2))) * (b + ((-1) * (t ^ 2))) * (b + ((-1) * a * (t ^ 2))) * (((-1) * (t ^ 2)) + (a * b)))
def evalCoefficients {n : ℕ} (x : K) (c : Fin n → K) : K := ∑ k, c k * x ^ (k : ℕ)
def weylTargetCoefficient (t a b : K) : K := (((1 + a) ^ 2) * ((1 + b) ^ 2) * (1 + ((-1) * (t ^ 2))) * (1 + ((-1) * a * (t ^ 2))) * (1 + ((-1) * b * (t ^ 2))) * (1 + ((-1) * a * b * (t ^ 2))) * ((-1) + a) * ((-1) + b) * ((-1) + (a * b)) * (a + ((-1) * b)) * (a + ((-1) * (t ^ 2))) * (a + ((-1) * b * (t ^ 2))) * (b + ((-1) * (t ^ 2))) * (b + ((-1) * a * (t ^ 2))) * (((-1) * (t ^ 2)) + (a * b)))
@[irreducible] def wh0_0 (t a b : K) : K := ((a ^ 4) * (b ^ 3) * (t ^ 4) * (((-1) * b) + (a * (t ^ 2))))
@[irreducible] def wh0_1 (t a b : K) : K := ((-1) * t * (a ^ 3) * (b ^ 2) * ((-1) + (a * b * (t ^ 2))) * (((-1) * b) + (a * (t ^ 2))) * ((-1) + (t ^ 2) + (a * (t ^ 2))))
@[irreducible] def wh0_2 (t a b : K) : K := ((a ^ 2) * (b ^ 2) * (1 + a + (a * b) + ((a ^ 3) * (t ^ 4)) + ((-1) * a * (t ^ 4)) + ((-1) * (a ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (t ^ 4)) + ((-1) * (a ^ 3) * (t ^ 6)) + ((-1) * (a ^ 4) * (t ^ 6)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 6)) + (b * (a ^ 3) * (t ^ 4)) + (b * (a ^ 3) * (t ^ 6)) + (b * (a ^ 4) * (t ^ 8)) + ((a ^ 3) * (b ^ 2) * (t ^ 4)) + ((-1) * a * b * (t ^ 2)) + ((-1) * b * (a ^ 4) * (t ^ 6)) + ((-1) * (a ^ 3) * (b ^ 2) * (t ^ 6)) + ((-2) * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wh0_3 (t a b : K) : K := ((-1) * t * (a ^ 3) * (b ^ 2) * ((-1) + (a * b * (t ^ 2))) * (((-1) * b) + (a * (t ^ 2))) * ((-1) + (t ^ 2) + (a * (t ^ 2))))
@[irreducible] def wh0_4 (t a b : K) : K := ((a ^ 4) * (b ^ 3) * (t ^ 4) * (((-1) * b) + (a * (t ^ 2))))
@[irreducible] def wr0_0 (t a b : K) : K := ((-1) * a * (b ^ 2) * (t ^ 3))
@[irreducible] def wr0_1 (t a b : K) : K := (b * (t ^ 2) * (a + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr0_2 (t a b : K) : K := ((-1) * t * ((a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (b * (t ^ 4)) + ((a ^ 2) * (b ^ 3)) + ((b ^ 3) * (t ^ 2)) + ((b ^ 3) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 3) * (t ^ 2)) + (3 * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr0_3 (t a b : K) : K := ((t ^ 4) + ((a ^ 2) * (b ^ 2)) + ((a ^ 2) * (t ^ 2)) + ((b ^ 2) * (t ^ 2)) + ((b ^ 2) * (t ^ 6)) + ((b ^ 4) * (t ^ 4)) + (2 * (b ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 4) * (t ^ 2)) + (2 * a * b * (t ^ 2)) + (2 * a * b * (t ^ 4)) + (2 * a * (b ^ 3) * (t ^ 2)) + (2 * a * (b ^ 3) * (t ^ 4)) + (2 * (a ^ 2) * (b ^ 2) * (t ^ 2)))
@[irreducible] def wr0_4 (t a b : K) : K := ((-1) * t * ((a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (b * (t ^ 4)) + ((a ^ 2) * (b ^ 3)) + ((b ^ 3) * (t ^ 2)) + ((b ^ 3) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 3) * (t ^ 2)) + (3 * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr0_5 (t a b : K) : K := (b * (t ^ 2) * (a + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr0_6 (t a b : K) : K := ((-1) * a * (b ^ 2) * (t ^ 3))
def wc0_0 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_0 t a b * wr0_0 t a b))
def wc0_1 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_0 t a b * wr0_1 t a b) + (wh0_1 t a b * wr0_0 t a b))
def wc0_2 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_0 t a b * wr0_2 t a b) + (wh0_1 t a b * wr0_1 t a b) + (wh0_2 t a b * wr0_0 t a b))
def wc0_3 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_0 t a b * wr0_3 t a b) + (wh0_1 t a b * wr0_2 t a b) + (wh0_2 t a b * wr0_1 t a b) + (wh0_3 t a b * wr0_0 t a b))
def wc0_4 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_0 t a b * wr0_4 t a b) + (wh0_1 t a b * wr0_3 t a b) + (wh0_2 t a b * wr0_2 t a b) + (wh0_3 t a b * wr0_1 t a b) + (wh0_4 t a b * wr0_0 t a b))
def wc0_5 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_0 t a b * wr0_5 t a b) + (wh0_1 t a b * wr0_4 t a b) + (wh0_2 t a b * wr0_3 t a b) + (wh0_3 t a b * wr0_2 t a b) + (wh0_4 t a b * wr0_1 t a b))
def wc0_6 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_0 t a b * wr0_6 t a b) + (wh0_1 t a b * wr0_5 t a b) + (wh0_2 t a b * wr0_4 t a b) + (wh0_3 t a b * wr0_3 t a b) + (wh0_4 t a b * wr0_2 t a b))
def wc0_7 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_1 t a b * wr0_6 t a b) + (wh0_2 t a b * wr0_5 t a b) + (wh0_3 t a b * wr0_4 t a b) + (wh0_4 t a b * wr0_3 t a b))
def wc0_8 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_2 t a b * wr0_6 t a b) + (wh0_3 t a b * wr0_5 t a b) + (wh0_4 t a b * wr0_4 t a b))
def wc0_9 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_3 t a b * wr0_6 t a b) + (wh0_4 t a b * wr0_5 t a b))
def wc0_10 (t a b : K) : K := weylWeightNumerators t a b 0 * ((wh0_4 t a b * wr0_6 t a b))
def whCoeffs0 (t a b : K) : Fin 5 → K := ![wh0_0 t a b, wh0_1 t a b, wh0_2 t a b, wh0_3 t a b, wh0_4 t a b]
def wrCoeffs0 (t a b : K) : Fin 7 → K := ![wr0_0 t a b, wr0_1 t a b, wr0_2 t a b, wr0_3 t a b, wr0_4 t a b, wr0_5 t a b, wr0_6 t a b]
def wcCoeffs0 (t a b : K) : Fin 11 → K := ![wc0_0 t a b, wc0_1 t a b, wc0_2 t a b, wc0_3 t a b, wc0_4 t a b, wc0_5 t a b, wc0_6 t a b, wc0_7 t a b, wc0_8 t a b, wc0_9 t a b, wc0_10 t a b]
@[irreducible] def wh1_0 (t a b : K) : K := ((a ^ 3) * (b ^ 4) * (t ^ 4) * (((-1) * a) + (b * (t ^ 2))))
@[irreducible] def wh1_1 (t a b : K) : K := ((-1) * t * (a ^ 2) * (b ^ 3) * ((-1) + (a * b * (t ^ 2))) * (((-1) * a) + (b * (t ^ 2))) * ((-1) + (t ^ 2) + (b * (t ^ 2))))
@[irreducible] def wh1_2 (t a b : K) : K := ((a ^ 2) * (b ^ 2) * (1 + b + (a * b) + ((b ^ 3) * (t ^ 4)) + ((-1) * b * (t ^ 4)) + ((-1) * (b ^ 2) * (t ^ 2)) + ((-1) * (b ^ 2) * (t ^ 4)) + ((-1) * (b ^ 3) * (t ^ 6)) + ((-1) * (b ^ 4) * (t ^ 6)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 6)) + (a * (b ^ 3) * (t ^ 4)) + (a * (b ^ 3) * (t ^ 6)) + (a * (b ^ 4) * (t ^ 8)) + ((a ^ 2) * (b ^ 3) * (t ^ 4)) + ((-1) * a * b * (t ^ 2)) + ((-1) * a * (b ^ 4) * (t ^ 6)) + ((-1) * (a ^ 2) * (b ^ 3) * (t ^ 6)) + ((-2) * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wh1_3 (t a b : K) : K := ((-1) * t * (a ^ 2) * (b ^ 3) * ((-1) + (a * b * (t ^ 2))) * (((-1) * a) + (b * (t ^ 2))) * ((-1) + (t ^ 2) + (b * (t ^ 2))))
@[irreducible] def wh1_4 (t a b : K) : K := ((a ^ 3) * (b ^ 4) * (t ^ 4) * (((-1) * a) + (b * (t ^ 2))))
@[irreducible] def wr1_0 (t a b : K) : K := ((-1) * b * (a ^ 2) * (t ^ 3))
@[irreducible] def wr1_1 (t a b : K) : K := (a * (t ^ 2) * (b + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr1_2 (t a b : K) : K := ((-1) * t * ((a * (b ^ 2)) + (a * (t ^ 2)) + (a * (t ^ 4)) + (b * (a ^ 2)) + (b * (t ^ 2)) + ((a ^ 3) * (b ^ 2)) + ((a ^ 3) * (t ^ 2)) + ((a ^ 3) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 2)) + (3 * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr1_3 (t a b : K) : K := ((t ^ 4) + ((a ^ 2) * (b ^ 2)) + ((a ^ 2) * (t ^ 2)) + ((a ^ 2) * (t ^ 6)) + ((a ^ 4) * (t ^ 4)) + ((b ^ 2) * (t ^ 2)) + (2 * (a ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 2) * (t ^ 4)) + ((a ^ 4) * (b ^ 2) * (t ^ 2)) + (2 * a * b * (t ^ 2)) + (2 * a * b * (t ^ 4)) + (2 * b * (a ^ 3) * (t ^ 2)) + (2 * b * (a ^ 3) * (t ^ 4)) + (2 * (a ^ 2) * (b ^ 2) * (t ^ 2)))
@[irreducible] def wr1_4 (t a b : K) : K := ((-1) * t * ((a * (b ^ 2)) + (a * (t ^ 2)) + (a * (t ^ 4)) + (b * (a ^ 2)) + (b * (t ^ 2)) + ((a ^ 3) * (b ^ 2)) + ((a ^ 3) * (t ^ 2)) + ((a ^ 3) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 2)) + (3 * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr1_5 (t a b : K) : K := (a * (t ^ 2) * (b + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr1_6 (t a b : K) : K := ((-1) * b * (a ^ 2) * (t ^ 3))
def wc1_0 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_0 t a b * wr1_0 t a b))
def wc1_1 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_0 t a b * wr1_1 t a b) + (wh1_1 t a b * wr1_0 t a b))
def wc1_2 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_0 t a b * wr1_2 t a b) + (wh1_1 t a b * wr1_1 t a b) + (wh1_2 t a b * wr1_0 t a b))
def wc1_3 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_0 t a b * wr1_3 t a b) + (wh1_1 t a b * wr1_2 t a b) + (wh1_2 t a b * wr1_1 t a b) + (wh1_3 t a b * wr1_0 t a b))
def wc1_4 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_0 t a b * wr1_4 t a b) + (wh1_1 t a b * wr1_3 t a b) + (wh1_2 t a b * wr1_2 t a b) + (wh1_3 t a b * wr1_1 t a b) + (wh1_4 t a b * wr1_0 t a b))
def wc1_5 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_0 t a b * wr1_5 t a b) + (wh1_1 t a b * wr1_4 t a b) + (wh1_2 t a b * wr1_3 t a b) + (wh1_3 t a b * wr1_2 t a b) + (wh1_4 t a b * wr1_1 t a b))
def wc1_6 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_0 t a b * wr1_6 t a b) + (wh1_1 t a b * wr1_5 t a b) + (wh1_2 t a b * wr1_4 t a b) + (wh1_3 t a b * wr1_3 t a b) + (wh1_4 t a b * wr1_2 t a b))
def wc1_7 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_1 t a b * wr1_6 t a b) + (wh1_2 t a b * wr1_5 t a b) + (wh1_3 t a b * wr1_4 t a b) + (wh1_4 t a b * wr1_3 t a b))
def wc1_8 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_2 t a b * wr1_6 t a b) + (wh1_3 t a b * wr1_5 t a b) + (wh1_4 t a b * wr1_4 t a b))
def wc1_9 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_3 t a b * wr1_6 t a b) + (wh1_4 t a b * wr1_5 t a b))
def wc1_10 (t a b : K) : K := weylWeightNumerators t a b 1 * ((wh1_4 t a b * wr1_6 t a b))
def whCoeffs1 (t a b : K) : Fin 5 → K := ![wh1_0 t a b, wh1_1 t a b, wh1_2 t a b, wh1_3 t a b, wh1_4 t a b]
def wrCoeffs1 (t a b : K) : Fin 7 → K := ![wr1_0 t a b, wr1_1 t a b, wr1_2 t a b, wr1_3 t a b, wr1_4 t a b, wr1_5 t a b, wr1_6 t a b]
def wcCoeffs1 (t a b : K) : Fin 11 → K := ![wc1_0 t a b, wc1_1 t a b, wc1_2 t a b, wc1_3 t a b, wc1_4 t a b, wc1_5 t a b, wc1_6 t a b, wc1_7 t a b, wc1_8 t a b, wc1_9 t a b, wc1_10 t a b]
@[irreducible] def wh2_0 (t a b : K) : K := ((a ^ 4) * (t ^ 4) * ((-1) + (a * b * (t ^ 2))))
@[irreducible] def wh2_1 (t a b : K) : K := ((-1) * t * (a ^ 3) * ((-1) + (a * b * (t ^ 2))) * (((-1) * b) + (a * (t ^ 2))) * ((-1) + (t ^ 2) + (a * (t ^ 2))))
@[irreducible] def wh2_2 (t a b : K) : K := ((a ^ 2) * ((b ^ 2) + (a * b) + (a * (b ^ 2)) + ((a ^ 3) * (t ^ 4)) + ((-1) * (a ^ 3) * (t ^ 6)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 6)) + (b * (a ^ 3) * (t ^ 4)) + (b * (a ^ 3) * (t ^ 6)) + (b * (a ^ 4) * (t ^ 8)) + ((a ^ 3) * (b ^ 2) * (t ^ 4)) + ((-1) * a * b * (t ^ 2)) + ((-1) * a * (b ^ 2) * (t ^ 4)) + ((-1) * b * (a ^ 4) * (t ^ 6)) + ((-1) * (a ^ 2) * (b ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (t ^ 4)) + ((-1) * (a ^ 3) * (b ^ 2) * (t ^ 6)) + ((-1) * (a ^ 4) * (b ^ 2) * (t ^ 6)) + ((-2) * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wh2_3 (t a b : K) : K := ((-1) * t * (a ^ 3) * ((-1) + (a * b * (t ^ 2))) * (((-1) * b) + (a * (t ^ 2))) * ((-1) + (t ^ 2) + (a * (t ^ 2))))
@[irreducible] def wh2_4 (t a b : K) : K := ((a ^ 4) * (t ^ 4) * ((-1) + (a * b * (t ^ 2))))
@[irreducible] def wr2_0 (t a b : K) : K := ((-1) * a * (b ^ 2) * (t ^ 3))
@[irreducible] def wr2_1 (t a b : K) : K := (b * (t ^ 2) * (a + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr2_2 (t a b : K) : K := ((-1) * t * ((a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (b * (t ^ 4)) + ((a ^ 2) * (b ^ 3)) + ((b ^ 3) * (t ^ 2)) + ((b ^ 3) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 3) * (t ^ 2)) + (3 * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr2_3 (t a b : K) : K := ((t ^ 4) + ((a ^ 2) * (b ^ 2)) + ((a ^ 2) * (t ^ 2)) + ((b ^ 2) * (t ^ 2)) + ((b ^ 2) * (t ^ 6)) + ((b ^ 4) * (t ^ 4)) + (2 * (b ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 4) * (t ^ 2)) + (2 * a * b * (t ^ 2)) + (2 * a * b * (t ^ 4)) + (2 * a * (b ^ 3) * (t ^ 2)) + (2 * a * (b ^ 3) * (t ^ 4)) + (2 * (a ^ 2) * (b ^ 2) * (t ^ 2)))
@[irreducible] def wr2_4 (t a b : K) : K := ((-1) * t * ((a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (b * (t ^ 4)) + ((a ^ 2) * (b ^ 3)) + ((b ^ 3) * (t ^ 2)) + ((b ^ 3) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 3) * (t ^ 2)) + (3 * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr2_5 (t a b : K) : K := (b * (t ^ 2) * (a + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr2_6 (t a b : K) : K := ((-1) * a * (b ^ 2) * (t ^ 3))
def wc2_0 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_0 t a b * wr2_0 t a b))
def wc2_1 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_0 t a b * wr2_1 t a b) + (wh2_1 t a b * wr2_0 t a b))
def wc2_2 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_0 t a b * wr2_2 t a b) + (wh2_1 t a b * wr2_1 t a b) + (wh2_2 t a b * wr2_0 t a b))
def wc2_3 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_0 t a b * wr2_3 t a b) + (wh2_1 t a b * wr2_2 t a b) + (wh2_2 t a b * wr2_1 t a b) + (wh2_3 t a b * wr2_0 t a b))
def wc2_4 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_0 t a b * wr2_4 t a b) + (wh2_1 t a b * wr2_3 t a b) + (wh2_2 t a b * wr2_2 t a b) + (wh2_3 t a b * wr2_1 t a b) + (wh2_4 t a b * wr2_0 t a b))
def wc2_5 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_0 t a b * wr2_5 t a b) + (wh2_1 t a b * wr2_4 t a b) + (wh2_2 t a b * wr2_3 t a b) + (wh2_3 t a b * wr2_2 t a b) + (wh2_4 t a b * wr2_1 t a b))
def wc2_6 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_0 t a b * wr2_6 t a b) + (wh2_1 t a b * wr2_5 t a b) + (wh2_2 t a b * wr2_4 t a b) + (wh2_3 t a b * wr2_3 t a b) + (wh2_4 t a b * wr2_2 t a b))
def wc2_7 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_1 t a b * wr2_6 t a b) + (wh2_2 t a b * wr2_5 t a b) + (wh2_3 t a b * wr2_4 t a b) + (wh2_4 t a b * wr2_3 t a b))
def wc2_8 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_2 t a b * wr2_6 t a b) + (wh2_3 t a b * wr2_5 t a b) + (wh2_4 t a b * wr2_4 t a b))
def wc2_9 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_3 t a b * wr2_6 t a b) + (wh2_4 t a b * wr2_5 t a b))
def wc2_10 (t a b : K) : K := weylWeightNumerators t a b 2 * ((wh2_4 t a b * wr2_6 t a b))
def whCoeffs2 (t a b : K) : Fin 5 → K := ![wh2_0 t a b, wh2_1 t a b, wh2_2 t a b, wh2_3 t a b, wh2_4 t a b]
def wrCoeffs2 (t a b : K) : Fin 7 → K := ![wr2_0 t a b, wr2_1 t a b, wr2_2 t a b, wr2_3 t a b, wr2_4 t a b, wr2_5 t a b, wr2_6 t a b]
def wcCoeffs2 (t a b : K) : Fin 11 → K := ![wc2_0 t a b, wc2_1 t a b, wc2_2 t a b, wc2_3 t a b, wc2_4 t a b, wc2_5 t a b, wc2_6 t a b, wc2_7 t a b, wc2_8 t a b, wc2_9 t a b, wc2_10 t a b]
@[irreducible] def wh3_0 (t a b : K) : K := (b * (a ^ 3) * (t ^ 4) * ((t ^ 2) + ((-1) * a * b)))
@[irreducible] def wh3_1 (t a b : K) : K := ((-1) * t * (a ^ 2) * ((t ^ 2) + ((-1) * a * b)) * (((-1) * b) + (a * (t ^ 2))) * ((t ^ 2) + ((-1) * b) + (b * (t ^ 2))))
@[irreducible] def wh3_2 (t a b : K) : K := ((a ^ 2) * ((b ^ 3) + (b ^ 4) + ((-1) * (t ^ 6)) + (a * (b ^ 3)) + (a * (t ^ 8)) + (b * (t ^ 4)) + ((-1) * a * (t ^ 6)) + ((-1) * b * (t ^ 6)) + ((-1) * (b ^ 2) * (t ^ 2)) + ((-1) * (b ^ 2) * (t ^ 4)) + ((-1) * (b ^ 3) * (t ^ 4)) + (a * b * (t ^ 4)) + (a * b * (t ^ 6)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 6)) + (b * (a ^ 2) * (t ^ 4)) + ((-1) * a * (b ^ 3) * (t ^ 2)) + ((-1) * b * (a ^ 2) * (t ^ 6)) + ((-2) * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wh3_3 (t a b : K) : K := ((-1) * t * (a ^ 2) * ((t ^ 2) + ((-1) * a * b)) * (((-1) * b) + (a * (t ^ 2))) * ((t ^ 2) + ((-1) * b) + (b * (t ^ 2))))
@[irreducible] def wh3_4 (t a b : K) : K := (b * (a ^ 3) * (t ^ 4) * ((t ^ 2) + ((-1) * a * b)))
@[irreducible] def wr3_0 (t a b : K) : K := ((-1) * b * (a ^ 2) * (t ^ 3))
@[irreducible] def wr3_1 (t a b : K) : K := (a * (t ^ 2) * (a + b + (b * (a ^ 2)) + (b * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr3_2 (t a b : K) : K := ((-1) * t * (a + (a ^ 3) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + ((a ^ 3) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 4)) + (3 * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr3_3 (t a b : K) : K := ((a ^ 2) + (t ^ 2) + ((a ^ 2) * (t ^ 4)) + ((a ^ 4) * (t ^ 2)) + ((b ^ 2) * (t ^ 4)) + (2 * (a ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 2) * (t ^ 6)) + ((a ^ 4) * (b ^ 2) * (t ^ 4)) + (2 * a * b * (t ^ 2)) + (2 * a * b * (t ^ 4)) + (2 * b * (a ^ 3) * (t ^ 2)) + (2 * b * (a ^ 3) * (t ^ 4)) + (2 * (a ^ 2) * (b ^ 2) * (t ^ 4)))
@[irreducible] def wr3_4 (t a b : K) : K := ((-1) * t * (a + (a ^ 3) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + ((a ^ 3) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 4)) + (3 * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr3_5 (t a b : K) : K := (a * (t ^ 2) * (a + b + (b * (a ^ 2)) + (b * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr3_6 (t a b : K) : K := ((-1) * b * (a ^ 2) * (t ^ 3))
def wc3_0 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_0 t a b * wr3_0 t a b))
def wc3_1 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_0 t a b * wr3_1 t a b) + (wh3_1 t a b * wr3_0 t a b))
def wc3_2 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_0 t a b * wr3_2 t a b) + (wh3_1 t a b * wr3_1 t a b) + (wh3_2 t a b * wr3_0 t a b))
def wc3_3 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_0 t a b * wr3_3 t a b) + (wh3_1 t a b * wr3_2 t a b) + (wh3_2 t a b * wr3_1 t a b) + (wh3_3 t a b * wr3_0 t a b))
def wc3_4 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_0 t a b * wr3_4 t a b) + (wh3_1 t a b * wr3_3 t a b) + (wh3_2 t a b * wr3_2 t a b) + (wh3_3 t a b * wr3_1 t a b) + (wh3_4 t a b * wr3_0 t a b))
def wc3_5 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_0 t a b * wr3_5 t a b) + (wh3_1 t a b * wr3_4 t a b) + (wh3_2 t a b * wr3_3 t a b) + (wh3_3 t a b * wr3_2 t a b) + (wh3_4 t a b * wr3_1 t a b))
def wc3_6 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_0 t a b * wr3_6 t a b) + (wh3_1 t a b * wr3_5 t a b) + (wh3_2 t a b * wr3_4 t a b) + (wh3_3 t a b * wr3_3 t a b) + (wh3_4 t a b * wr3_2 t a b))
def wc3_7 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_1 t a b * wr3_6 t a b) + (wh3_2 t a b * wr3_5 t a b) + (wh3_3 t a b * wr3_4 t a b) + (wh3_4 t a b * wr3_3 t a b))
def wc3_8 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_2 t a b * wr3_6 t a b) + (wh3_3 t a b * wr3_5 t a b) + (wh3_4 t a b * wr3_4 t a b))
def wc3_9 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_3 t a b * wr3_6 t a b) + (wh3_4 t a b * wr3_5 t a b))
def wc3_10 (t a b : K) : K := weylWeightNumerators t a b 3 * ((wh3_4 t a b * wr3_6 t a b))
def whCoeffs3 (t a b : K) : Fin 5 → K := ![wh3_0 t a b, wh3_1 t a b, wh3_2 t a b, wh3_3 t a b, wh3_4 t a b]
def wrCoeffs3 (t a b : K) : Fin 7 → K := ![wr3_0 t a b, wr3_1 t a b, wr3_2 t a b, wr3_3 t a b, wr3_4 t a b, wr3_5 t a b, wr3_6 t a b]
def wcCoeffs3 (t a b : K) : Fin 11 → K := ![wc3_0 t a b, wc3_1 t a b, wc3_2 t a b, wc3_3 t a b, wc3_4 t a b, wc3_5 t a b, wc3_6 t a b, wc3_7 t a b, wc3_8 t a b, wc3_9 t a b, wc3_10 t a b]
@[irreducible] def wh4_0 (t a b : K) : K := ((b ^ 4) * (t ^ 4) * ((-1) + (a * b * (t ^ 2))))
@[irreducible] def wh4_1 (t a b : K) : K := ((-1) * t * (b ^ 3) * ((-1) + (a * b * (t ^ 2))) * (((-1) * a) + (b * (t ^ 2))) * ((-1) + (t ^ 2) + (b * (t ^ 2))))
@[irreducible] def wh4_2 (t a b : K) : K := ((b ^ 2) * ((a ^ 2) + (a * b) + (b * (a ^ 2)) + ((b ^ 3) * (t ^ 4)) + ((-1) * (b ^ 3) * (t ^ 6)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 6)) + (a * (b ^ 3) * (t ^ 4)) + (a * (b ^ 3) * (t ^ 6)) + (a * (b ^ 4) * (t ^ 8)) + ((a ^ 2) * (b ^ 3) * (t ^ 4)) + ((-1) * a * b * (t ^ 2)) + ((-1) * a * (b ^ 4) * (t ^ 6)) + ((-1) * b * (a ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 3) * (t ^ 6)) + ((-1) * (a ^ 2) * (b ^ 4) * (t ^ 6)) + ((-2) * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wh4_3 (t a b : K) : K := ((-1) * t * (b ^ 3) * ((-1) + (a * b * (t ^ 2))) * (((-1) * a) + (b * (t ^ 2))) * ((-1) + (t ^ 2) + (b * (t ^ 2))))
@[irreducible] def wh4_4 (t a b : K) : K := ((b ^ 4) * (t ^ 4) * ((-1) + (a * b * (t ^ 2))))
@[irreducible] def wr4_0 (t a b : K) : K := ((-1) * b * (a ^ 2) * (t ^ 3))
@[irreducible] def wr4_1 (t a b : K) : K := (a * (t ^ 2) * (b + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr4_2 (t a b : K) : K := ((-1) * t * ((a * (b ^ 2)) + (a * (t ^ 2)) + (a * (t ^ 4)) + (b * (a ^ 2)) + (b * (t ^ 2)) + ((a ^ 3) * (b ^ 2)) + ((a ^ 3) * (t ^ 2)) + ((a ^ 3) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 2)) + (3 * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr4_3 (t a b : K) : K := ((t ^ 4) + ((a ^ 2) * (b ^ 2)) + ((a ^ 2) * (t ^ 2)) + ((a ^ 2) * (t ^ 6)) + ((a ^ 4) * (t ^ 4)) + ((b ^ 2) * (t ^ 2)) + (2 * (a ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 2) * (t ^ 4)) + ((a ^ 4) * (b ^ 2) * (t ^ 2)) + (2 * a * b * (t ^ 2)) + (2 * a * b * (t ^ 4)) + (2 * b * (a ^ 3) * (t ^ 2)) + (2 * b * (a ^ 3) * (t ^ 4)) + (2 * (a ^ 2) * (b ^ 2) * (t ^ 2)))
@[irreducible] def wr4_4 (t a b : K) : K := ((-1) * t * ((a * (b ^ 2)) + (a * (t ^ 2)) + (a * (t ^ 4)) + (b * (a ^ 2)) + (b * (t ^ 2)) + ((a ^ 3) * (b ^ 2)) + ((a ^ 3) * (t ^ 2)) + ((a ^ 3) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 2)) + (3 * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr4_5 (t a b : K) : K := (a * (t ^ 2) * (b + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr4_6 (t a b : K) : K := ((-1) * b * (a ^ 2) * (t ^ 3))
def wc4_0 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_0 t a b * wr4_0 t a b))
def wc4_1 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_0 t a b * wr4_1 t a b) + (wh4_1 t a b * wr4_0 t a b))
def wc4_2 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_0 t a b * wr4_2 t a b) + (wh4_1 t a b * wr4_1 t a b) + (wh4_2 t a b * wr4_0 t a b))
def wc4_3 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_0 t a b * wr4_3 t a b) + (wh4_1 t a b * wr4_2 t a b) + (wh4_2 t a b * wr4_1 t a b) + (wh4_3 t a b * wr4_0 t a b))
def wc4_4 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_0 t a b * wr4_4 t a b) + (wh4_1 t a b * wr4_3 t a b) + (wh4_2 t a b * wr4_2 t a b) + (wh4_3 t a b * wr4_1 t a b) + (wh4_4 t a b * wr4_0 t a b))
def wc4_5 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_0 t a b * wr4_5 t a b) + (wh4_1 t a b * wr4_4 t a b) + (wh4_2 t a b * wr4_3 t a b) + (wh4_3 t a b * wr4_2 t a b) + (wh4_4 t a b * wr4_1 t a b))
def wc4_6 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_0 t a b * wr4_6 t a b) + (wh4_1 t a b * wr4_5 t a b) + (wh4_2 t a b * wr4_4 t a b) + (wh4_3 t a b * wr4_3 t a b) + (wh4_4 t a b * wr4_2 t a b))
def wc4_7 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_1 t a b * wr4_6 t a b) + (wh4_2 t a b * wr4_5 t a b) + (wh4_3 t a b * wr4_4 t a b) + (wh4_4 t a b * wr4_3 t a b))
def wc4_8 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_2 t a b * wr4_6 t a b) + (wh4_3 t a b * wr4_5 t a b) + (wh4_4 t a b * wr4_4 t a b))
def wc4_9 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_3 t a b * wr4_6 t a b) + (wh4_4 t a b * wr4_5 t a b))
def wc4_10 (t a b : K) : K := weylWeightNumerators t a b 4 * ((wh4_4 t a b * wr4_6 t a b))
def whCoeffs4 (t a b : K) : Fin 5 → K := ![wh4_0 t a b, wh4_1 t a b, wh4_2 t a b, wh4_3 t a b, wh4_4 t a b]
def wrCoeffs4 (t a b : K) : Fin 7 → K := ![wr4_0 t a b, wr4_1 t a b, wr4_2 t a b, wr4_3 t a b, wr4_4 t a b, wr4_5 t a b, wr4_6 t a b]
def wcCoeffs4 (t a b : K) : Fin 11 → K := ![wc4_0 t a b, wc4_1 t a b, wc4_2 t a b, wc4_3 t a b, wc4_4 t a b, wc4_5 t a b, wc4_6 t a b, wc4_7 t a b, wc4_8 t a b, wc4_9 t a b, wc4_10 t a b]
@[irreducible] def wh5_0 (t a b : K) : K := (a * (b ^ 3) * (t ^ 4) * ((t ^ 2) + ((-1) * a * b)))
@[irreducible] def wh5_1 (t a b : K) : K := ((-1) * t * (b ^ 2) * ((t ^ 2) + ((-1) * a * b)) * (((-1) * a) + (b * (t ^ 2))) * ((t ^ 2) + ((-1) * a) + (a * (t ^ 2))))
@[irreducible] def wh5_2 (t a b : K) : K := ((b ^ 2) * ((a ^ 3) + (a ^ 4) + ((-1) * (t ^ 6)) + (a * (t ^ 4)) + (b * (a ^ 3)) + (b * (t ^ 8)) + ((-1) * a * (t ^ 6)) + ((-1) * b * (t ^ 6)) + ((-1) * (a ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (t ^ 4)) + ((-1) * (a ^ 3) * (t ^ 4)) + (a * b * (t ^ 4)) + (a * b * (t ^ 6)) + (a * (b ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 6)) + ((-1) * a * (b ^ 2) * (t ^ 6)) + ((-1) * b * (a ^ 3) * (t ^ 2)) + ((-2) * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wh5_3 (t a b : K) : K := ((-1) * t * (b ^ 2) * ((t ^ 2) + ((-1) * a * b)) * (((-1) * a) + (b * (t ^ 2))) * ((t ^ 2) + ((-1) * a) + (a * (t ^ 2))))
@[irreducible] def wh5_4 (t a b : K) : K := (a * (b ^ 3) * (t ^ 4) * ((t ^ 2) + ((-1) * a * b)))
@[irreducible] def wr5_0 (t a b : K) : K := ((-1) * a * (b ^ 2) * (t ^ 3))
@[irreducible] def wr5_1 (t a b : K) : K := (b * (t ^ 2) * (a + b + (a * (b ^ 2)) + (a * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr5_2 (t a b : K) : K := ((-1) * t * (b + (b ^ 3) + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (t ^ 2)) + ((b ^ 3) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 3) * (t ^ 2)) + ((a ^ 2) * (b ^ 3) * (t ^ 4)) + (3 * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr5_3 (t a b : K) : K := ((b ^ 2) + (t ^ 2) + ((a ^ 2) * (t ^ 4)) + ((b ^ 2) * (t ^ 4)) + ((b ^ 4) * (t ^ 2)) + (2 * (b ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 2) * (t ^ 6)) + ((a ^ 2) * (b ^ 4) * (t ^ 4)) + (2 * a * b * (t ^ 2)) + (2 * a * b * (t ^ 4)) + (2 * a * (b ^ 3) * (t ^ 2)) + (2 * a * (b ^ 3) * (t ^ 4)) + (2 * (a ^ 2) * (b ^ 2) * (t ^ 4)))
@[irreducible] def wr5_4 (t a b : K) : K := ((-1) * t * (b + (b ^ 3) + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (t ^ 2)) + ((b ^ 3) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 3) * (t ^ 2)) + ((a ^ 2) * (b ^ 3) * (t ^ 4)) + (3 * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr5_5 (t a b : K) : K := (b * (t ^ 2) * (a + b + (a * (b ^ 2)) + (a * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr5_6 (t a b : K) : K := ((-1) * a * (b ^ 2) * (t ^ 3))
def wc5_0 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_0 t a b * wr5_0 t a b))
def wc5_1 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_0 t a b * wr5_1 t a b) + (wh5_1 t a b * wr5_0 t a b))
def wc5_2 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_0 t a b * wr5_2 t a b) + (wh5_1 t a b * wr5_1 t a b) + (wh5_2 t a b * wr5_0 t a b))
def wc5_3 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_0 t a b * wr5_3 t a b) + (wh5_1 t a b * wr5_2 t a b) + (wh5_2 t a b * wr5_1 t a b) + (wh5_3 t a b * wr5_0 t a b))
def wc5_4 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_0 t a b * wr5_4 t a b) + (wh5_1 t a b * wr5_3 t a b) + (wh5_2 t a b * wr5_2 t a b) + (wh5_3 t a b * wr5_1 t a b) + (wh5_4 t a b * wr5_0 t a b))
def wc5_5 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_0 t a b * wr5_5 t a b) + (wh5_1 t a b * wr5_4 t a b) + (wh5_2 t a b * wr5_3 t a b) + (wh5_3 t a b * wr5_2 t a b) + (wh5_4 t a b * wr5_1 t a b))
def wc5_6 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_0 t a b * wr5_6 t a b) + (wh5_1 t a b * wr5_5 t a b) + (wh5_2 t a b * wr5_4 t a b) + (wh5_3 t a b * wr5_3 t a b) + (wh5_4 t a b * wr5_2 t a b))
def wc5_7 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_1 t a b * wr5_6 t a b) + (wh5_2 t a b * wr5_5 t a b) + (wh5_3 t a b * wr5_4 t a b) + (wh5_4 t a b * wr5_3 t a b))
def wc5_8 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_2 t a b * wr5_6 t a b) + (wh5_3 t a b * wr5_5 t a b) + (wh5_4 t a b * wr5_4 t a b))
def wc5_9 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_3 t a b * wr5_6 t a b) + (wh5_4 t a b * wr5_5 t a b))
def wc5_10 (t a b : K) : K := weylWeightNumerators t a b 5 * ((wh5_4 t a b * wr5_6 t a b))
def whCoeffs5 (t a b : K) : Fin 5 → K := ![wh5_0 t a b, wh5_1 t a b, wh5_2 t a b, wh5_3 t a b, wh5_4 t a b]
def wrCoeffs5 (t a b : K) : Fin 7 → K := ![wr5_0 t a b, wr5_1 t a b, wr5_2 t a b, wr5_3 t a b, wr5_4 t a b, wr5_5 t a b, wr5_6 t a b]
def wcCoeffs5 (t a b : K) : Fin 11 → K := ![wc5_0 t a b, wc5_1 t a b, wc5_2 t a b, wc5_3 t a b, wc5_4 t a b, wc5_5 t a b, wc5_6 t a b, wc5_7 t a b, wc5_8 t a b, wc5_9 t a b, wc5_10 t a b]
@[irreducible] def wh6_0 (t a b : K) : K := (b * (t ^ 4) * (((-1) * b) + (a * (t ^ 2))))
@[irreducible] def wh6_1 (t a b : K) : K := ((-1) * t * ((t ^ 2) + ((-1) * a * b)) * (((-1) * b) + (a * (t ^ 2))) * ((t ^ 2) + ((-1) * b) + (b * (t ^ 2))))
@[irreducible] def wh6_2 (t a b : K) : K := ((a * (b ^ 3)) + (a * (t ^ 8)) + (b * (t ^ 4)) + ((a ^ 2) * (b ^ 3)) + ((a ^ 2) * (b ^ 4)) + ((-1) * a * (t ^ 6)) + ((-1) * b * (t ^ 6)) + ((-1) * (a ^ 2) * (t ^ 6)) + (a * b * (t ^ 4)) + (a * b * (t ^ 6)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 2) * (t ^ 6)) + (b * (a ^ 2) * (t ^ 4)) + ((-1) * a * (b ^ 3) * (t ^ 2)) + ((-1) * b * (a ^ 2) * (t ^ 6)) + ((-1) * (a ^ 2) * (b ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (t ^ 4)) + ((-1) * (a ^ 2) * (b ^ 3) * (t ^ 4)) + ((-2) * a * (b ^ 2) * (t ^ 2)))
@[irreducible] def wh6_3 (t a b : K) : K := ((-1) * t * ((t ^ 2) + ((-1) * a * b)) * (((-1) * b) + (a * (t ^ 2))) * ((t ^ 2) + ((-1) * b) + (b * (t ^ 2))))
@[irreducible] def wh6_4 (t a b : K) : K := (b * (t ^ 4) * (((-1) * b) + (a * (t ^ 2))))
@[irreducible] def wr6_0 (t a b : K) : K := ((-1) * b * (a ^ 2) * (t ^ 3))
@[irreducible] def wr6_1 (t a b : K) : K := (a * (t ^ 2) * (a + b + (b * (a ^ 2)) + (b * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr6_2 (t a b : K) : K := ((-1) * t * (a + (a ^ 3) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + ((a ^ 3) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 4)) + (3 * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr6_3 (t a b : K) : K := ((a ^ 2) + (t ^ 2) + ((a ^ 2) * (t ^ 4)) + ((a ^ 4) * (t ^ 2)) + ((b ^ 2) * (t ^ 4)) + (2 * (a ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 2) * (t ^ 6)) + ((a ^ 4) * (b ^ 2) * (t ^ 4)) + (2 * a * b * (t ^ 2)) + (2 * a * b * (t ^ 4)) + (2 * b * (a ^ 3) * (t ^ 2)) + (2 * b * (a ^ 3) * (t ^ 4)) + (2 * (a ^ 2) * (b ^ 2) * (t ^ 4)))
@[irreducible] def wr6_4 (t a b : K) : K := ((-1) * t * (a + (a ^ 3) + (a * (t ^ 2)) + (b * (a ^ 2)) + (b * (t ^ 2)) + ((a ^ 3) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 4) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 2)) + ((a ^ 3) * (b ^ 2) * (t ^ 4)) + (3 * b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr6_5 (t a b : K) : K := (a * (t ^ 2) * (a + b + (b * (a ^ 2)) + (b * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr6_6 (t a b : K) : K := ((-1) * b * (a ^ 2) * (t ^ 3))
def wc6_0 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_0 t a b * wr6_0 t a b))
def wc6_1 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_0 t a b * wr6_1 t a b) + (wh6_1 t a b * wr6_0 t a b))
def wc6_2 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_0 t a b * wr6_2 t a b) + (wh6_1 t a b * wr6_1 t a b) + (wh6_2 t a b * wr6_0 t a b))
def wc6_3 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_0 t a b * wr6_3 t a b) + (wh6_1 t a b * wr6_2 t a b) + (wh6_2 t a b * wr6_1 t a b) + (wh6_3 t a b * wr6_0 t a b))
def wc6_4 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_0 t a b * wr6_4 t a b) + (wh6_1 t a b * wr6_3 t a b) + (wh6_2 t a b * wr6_2 t a b) + (wh6_3 t a b * wr6_1 t a b) + (wh6_4 t a b * wr6_0 t a b))
def wc6_5 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_0 t a b * wr6_5 t a b) + (wh6_1 t a b * wr6_4 t a b) + (wh6_2 t a b * wr6_3 t a b) + (wh6_3 t a b * wr6_2 t a b) + (wh6_4 t a b * wr6_1 t a b))
def wc6_6 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_0 t a b * wr6_6 t a b) + (wh6_1 t a b * wr6_5 t a b) + (wh6_2 t a b * wr6_4 t a b) + (wh6_3 t a b * wr6_3 t a b) + (wh6_4 t a b * wr6_2 t a b))
def wc6_7 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_1 t a b * wr6_6 t a b) + (wh6_2 t a b * wr6_5 t a b) + (wh6_3 t a b * wr6_4 t a b) + (wh6_4 t a b * wr6_3 t a b))
def wc6_8 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_2 t a b * wr6_6 t a b) + (wh6_3 t a b * wr6_5 t a b) + (wh6_4 t a b * wr6_4 t a b))
def wc6_9 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_3 t a b * wr6_6 t a b) + (wh6_4 t a b * wr6_5 t a b))
def wc6_10 (t a b : K) : K := weylWeightNumerators t a b 6 * ((wh6_4 t a b * wr6_6 t a b))
def whCoeffs6 (t a b : K) : Fin 5 → K := ![wh6_0 t a b, wh6_1 t a b, wh6_2 t a b, wh6_3 t a b, wh6_4 t a b]
def wrCoeffs6 (t a b : K) : Fin 7 → K := ![wr6_0 t a b, wr6_1 t a b, wr6_2 t a b, wr6_3 t a b, wr6_4 t a b, wr6_5 t a b, wr6_6 t a b]
def wcCoeffs6 (t a b : K) : Fin 11 → K := ![wc6_0 t a b, wc6_1 t a b, wc6_2 t a b, wc6_3 t a b, wc6_4 t a b, wc6_5 t a b, wc6_6 t a b, wc6_7 t a b, wc6_8 t a b, wc6_9 t a b, wc6_10 t a b]
@[irreducible] def wh7_0 (t a b : K) : K := (a * (t ^ 4) * (((-1) * a) + (b * (t ^ 2))))
@[irreducible] def wh7_1 (t a b : K) : K := ((-1) * t * ((t ^ 2) + ((-1) * a * b)) * (((-1) * a) + (b * (t ^ 2))) * ((t ^ 2) + ((-1) * a) + (a * (t ^ 2))))
@[irreducible] def wh7_2 (t a b : K) : K := ((a * (t ^ 4)) + (b * (a ^ 3)) + (b * (t ^ 8)) + ((a ^ 3) * (b ^ 2)) + ((a ^ 4) * (b ^ 2)) + ((-1) * a * (t ^ 6)) + ((-1) * b * (t ^ 6)) + ((-1) * (b ^ 2) * (t ^ 6)) + (a * b * (t ^ 4)) + (a * b * (t ^ 6)) + (a * (b ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 4)) + (b * (a ^ 2) * (t ^ 6)) + ((-1) * a * (b ^ 2) * (t ^ 6)) + ((-1) * b * (a ^ 3) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (t ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (t ^ 4)) + ((-1) * (a ^ 3) * (b ^ 2) * (t ^ 4)) + ((-2) * b * (a ^ 2) * (t ^ 2)))
@[irreducible] def wh7_3 (t a b : K) : K := ((-1) * t * ((t ^ 2) + ((-1) * a * b)) * (((-1) * a) + (b * (t ^ 2))) * ((t ^ 2) + ((-1) * a) + (a * (t ^ 2))))
@[irreducible] def wh7_4 (t a b : K) : K := (a * (t ^ 4) * (((-1) * a) + (b * (t ^ 2))))
@[irreducible] def wr7_0 (t a b : K) : K := ((-1) * a * (b ^ 2) * (t ^ 3))
@[irreducible] def wr7_1 (t a b : K) : K := (b * (t ^ 2) * (a + b + (a * (b ^ 2)) + (a * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr7_2 (t a b : K) : K := ((-1) * t * (b + (b ^ 3) + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (t ^ 2)) + ((b ^ 3) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 3) * (t ^ 2)) + ((a ^ 2) * (b ^ 3) * (t ^ 4)) + (3 * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr7_3 (t a b : K) : K := ((b ^ 2) + (t ^ 2) + ((a ^ 2) * (t ^ 4)) + ((b ^ 2) * (t ^ 4)) + ((b ^ 4) * (t ^ 2)) + (2 * (b ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 2) * (t ^ 2)) + ((a ^ 2) * (b ^ 2) * (t ^ 6)) + ((a ^ 2) * (b ^ 4) * (t ^ 4)) + (2 * a * b * (t ^ 2)) + (2 * a * b * (t ^ 4)) + (2 * a * (b ^ 3) * (t ^ 2)) + (2 * a * (b ^ 3) * (t ^ 4)) + (2 * (a ^ 2) * (b ^ 2) * (t ^ 4)))
@[irreducible] def wr7_4 (t a b : K) : K := ((-1) * t * (b + (b ^ 3) + (a * (b ^ 2)) + (a * (t ^ 2)) + (b * (t ^ 2)) + ((b ^ 3) * (t ^ 2)) + (a * (b ^ 2) * (t ^ 4)) + (a * (b ^ 4) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 4)) + ((a ^ 2) * (b ^ 3) * (t ^ 2)) + ((a ^ 2) * (b ^ 3) * (t ^ 4)) + (3 * a * (b ^ 2) * (t ^ 2))))
@[irreducible] def wr7_5 (t a b : K) : K := (b * (t ^ 2) * (a + b + (a * (b ^ 2)) + (a * (t ^ 2)) + (a * (b ^ 2) * (t ^ 2)) + (b * (a ^ 2) * (t ^ 2))))
@[irreducible] def wr7_6 (t a b : K) : K := ((-1) * a * (b ^ 2) * (t ^ 3))
def wc7_0 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_0 t a b * wr7_0 t a b))
def wc7_1 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_0 t a b * wr7_1 t a b) + (wh7_1 t a b * wr7_0 t a b))
def wc7_2 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_0 t a b * wr7_2 t a b) + (wh7_1 t a b * wr7_1 t a b) + (wh7_2 t a b * wr7_0 t a b))
def wc7_3 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_0 t a b * wr7_3 t a b) + (wh7_1 t a b * wr7_2 t a b) + (wh7_2 t a b * wr7_1 t a b) + (wh7_3 t a b * wr7_0 t a b))
def wc7_4 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_0 t a b * wr7_4 t a b) + (wh7_1 t a b * wr7_3 t a b) + (wh7_2 t a b * wr7_2 t a b) + (wh7_3 t a b * wr7_1 t a b) + (wh7_4 t a b * wr7_0 t a b))
def wc7_5 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_0 t a b * wr7_5 t a b) + (wh7_1 t a b * wr7_4 t a b) + (wh7_2 t a b * wr7_3 t a b) + (wh7_3 t a b * wr7_2 t a b) + (wh7_4 t a b * wr7_1 t a b))
def wc7_6 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_0 t a b * wr7_6 t a b) + (wh7_1 t a b * wr7_5 t a b) + (wh7_2 t a b * wr7_4 t a b) + (wh7_3 t a b * wr7_3 t a b) + (wh7_4 t a b * wr7_2 t a b))
def wc7_7 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_1 t a b * wr7_6 t a b) + (wh7_2 t a b * wr7_5 t a b) + (wh7_3 t a b * wr7_4 t a b) + (wh7_4 t a b * wr7_3 t a b))
def wc7_8 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_2 t a b * wr7_6 t a b) + (wh7_3 t a b * wr7_5 t a b) + (wh7_4 t a b * wr7_4 t a b))
def wc7_9 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_3 t a b * wr7_6 t a b) + (wh7_4 t a b * wr7_5 t a b))
def wc7_10 (t a b : K) : K := weylWeightNumerators t a b 7 * ((wh7_4 t a b * wr7_6 t a b))
def whCoeffs7 (t a b : K) : Fin 5 → K := ![wh7_0 t a b, wh7_1 t a b, wh7_2 t a b, wh7_3 t a b, wh7_4 t a b]
def wrCoeffs7 (t a b : K) : Fin 7 → K := ![wr7_0 t a b, wr7_1 t a b, wr7_2 t a b, wr7_3 t a b, wr7_4 t a b, wr7_5 t a b, wr7_6 t a b]
def wcCoeffs7 (t a b : K) : Fin 11 → K := ![wc7_0 t a b, wc7_1 t a b, wc7_2 t a b, wc7_3 t a b, wc7_4 t a b, wc7_5 t a b, wc7_6 t a b, wc7_7 t a b, wc7_8 t a b, wc7_9 t a b, wc7_10 t a b]
end Algebra
end FourierJacobi


