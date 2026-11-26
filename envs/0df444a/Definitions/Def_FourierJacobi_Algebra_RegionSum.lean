-- Prove2me | Definitions.Def_FourierJacobi_Algebra_RegionSum
-- name    : FourierJacobi_Algebra_RegionSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:45:56.837841+00:00
-- url     : https://prove2.me/theorems/ee359315-be01-4fd0-80aa-be765688541f
-- title:
--   Region Sum
-- statement:
--   Definitions and structural lemmas for Region Sum, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/RegionSum.lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
def regionTerm0 (t d U V P N E F G : K) : K := ((P ^ 1)⁻¹)
def regionNumerator0 (t d U V P N E F G : K) : K := (E * F * G * N * (d ^ 2))
def regionTerm1 (t d U V P N E F G : K) : K := (U * ((G ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (t ^ 4) * (1 + ((-1) * (t ^ 2))))
def regionNumerator1 (t d U V P N E F G : K) : K := ((-1) * E * F * N * U * (d ^ 2) * (t ^ 4) * (1 + t) * ((-1) + t))
def regionTerm2 (t d U V P N E F G : K) : K := (V * ((E ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (t ^ 2) * (1 + V) * (1 + ((-1) * (t ^ 2))))
def regionNumerator2 (t d U V P N E F G : K) : K := ((-1) * F * G * N * V * (d ^ 2) * (t ^ 2) * (1 + V) * (1 + t) * ((-1) + t))
def regionTerm3 (t d U V P N E F G : K) : K := (U * ((E ^ 1)⁻¹) * ((F ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (t ^ 2) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator3 (t d U V P N E F G : K) : K := (G * N * U * (d ^ 2) * (t ^ 2) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm4 (t d U V P N E F G : K) : K := (((F ^ 1)⁻¹) * ((G ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (U ^ 2) * (t ^ 6) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator4 (t d U V P N E F G : K) : K := (E * N * (U ^ 2) * (d ^ 2) * (t ^ 6) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm5 (t d U V P N E F G : K) : K := (V * t * ((N ^ 1)⁻¹) * ((d ^ 1)⁻¹))
def regionNumerator5 (t d U V P N E F G : K) : K := (E * F * G * P * V * d * t)
def regionTerm6 (t d U V P N E F G : K) : K := (U * V * ((G ^ 1)⁻¹) * ((N ^ 1)⁻¹) * ((d ^ 1)⁻¹) * (t ^ 5) * (1 + ((-1) * (t ^ 2))))
def regionNumerator6 (t d U V P N E F G : K) : K := ((-1) * E * F * P * U * V * d * (t ^ 5) * (1 + t) * ((-1) + t))
def regionTerm7 (t d U V P N E F G : K) : K := (((E ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (V ^ 2) * ((d ^ 1)⁻¹) * (t ^ 3) * (1 + V) * (1 + ((-1) * (t ^ 2))))
def regionNumerator7 (t d U V P N E F G : K) : K := ((-1) * F * G * P * d * (V ^ 2) * (t ^ 3) * (1 + V) * (1 + t) * ((-1) + t))
def regionTerm8 (t d U V P N E F G : K) : K := (U * V * ((E ^ 1)⁻¹) * ((F ^ 1)⁻¹) * ((N ^ 1)⁻¹) * ((d ^ 1)⁻¹) * (t ^ 3) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator8 (t d U V P N E F G : K) : K := (G * P * U * V * d * (t ^ 3) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm9 (t d U V P N E F G : K) : K := (V * ((F ^ 1)⁻¹) * ((G ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (U ^ 2) * ((d ^ 1)⁻¹) * (t ^ 7) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator9 (t d U V P N E F G : K) : K := (E * P * V * d * (U ^ 2) * (t ^ 7) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm10 (t d U V P N E F G : K) : K := (U * d * t * ((P ^ 1)⁻¹) * (1 + ((-1) * (t ^ 2))))
def regionNumerator10 (t d U V P N E F G : K) : K := ((-1) * E * F * G * N * U * t * (d ^ 3) * (1 + t) * ((-1) + t))
def regionTerm11 (t d U V P N E F G : K) : K := (U * V * d * ((G ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (t ^ 3) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator11 (t d U V P N E F G : K) : K := (E * F * N * U * V * (d ^ 3) * (t ^ 3) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm12 (t d U V P N E F G : K) : K := (U * V * d * ((E ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (t ^ 3) * ((1 + ((-1) * (t ^ 2))) ^ 2) * (1 + V))
def regionNumerator12 (t d U V P N E F G : K) : K := (F * G * N * U * V * (d ^ 3) * (t ^ 3) * ((1 + t) ^ 2) * (((-1) + t) ^ 2) * (1 + V))
def regionTerm13 (t d U V P N E F G : K) : K := (U * V * d * t * ((E ^ 1)⁻¹) * ((P ^ 1)⁻¹) * ((1 + ((-1) * (t ^ 2))) ^ 2) * (1 + ((-2) * (t ^ 2))))
def regionNumerator13 (t d U V P N E F G : K) : K := ((-1) * F * G * N * U * V * t * (d ^ 3) * ((1 + t) ^ 2) * (((-1) + t) ^ 2) * ((-1) + (2 * (t ^ 2))))
def regionTerm14 (t d U V P N E F G : K) : K := (d * t * ((E ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (V ^ 2) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator14 (t d U V P N E F G : K) : K := (F * G * N * t * (V ^ 2) * (d ^ 3) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm15 (t d U V P N E F G : K) : K := (V * d * ((E ^ 1)⁻¹) * ((F ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (U ^ 2) * (t ^ 3) * ((1 + ((-1) * (t ^ 2))) ^ 3))
def regionNumerator15 (t d U V P N E F G : K) : K := ((-1) * G * N * V * (U ^ 2) * (d ^ 3) * (t ^ 3) * ((1 + t) ^ 3) * (((-1) + t) ^ 3))
def regionTerm16 (t d U V P N E F G : K) : K := (V * d * ((F ^ 1)⁻¹) * ((G ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (U ^ 2) * (t ^ 5) * ((1 + ((-1) * (t ^ 2))) ^ 3))
def regionNumerator16 (t d U V P N E F G : K) : K := ((-1) * E * N * V * (U ^ 2) * (d ^ 3) * (t ^ 5) * ((1 + t) ^ 3) * (((-1) + t) ^ 3))
def regionTerm17 (t d U V P N E F G : K) : K := (V * (t ^ 2) * (1 + ((-1) * (t ^ 2))))
def regionNumerator17 (t d U V P N E F G : K) : K := ((-1) * E * F * G * N * P * V * (d ^ 2) * (t ^ 2) * (1 + t) * ((-1) + t))
def regionTerm18 (t d U V P N E F G : K) : K := (U * t * ((N ^ 1)⁻¹) * ((d ^ 1)⁻¹) * (1 + ((-1) * (t ^ 2))))
def regionNumerator18 (t d U V P N E F G : K) : K := ((-1) * E * F * G * P * U * d * t * (1 + t) * ((-1) + t))
def regionTerm19 (t d U V P N E F G : K) : K := (U * ((G ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (t ^ 2) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator19 (t d U V P N E F G : K) : K := (E * F * P * U * (d ^ 2) * (t ^ 2) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm20 (t d U V P N E F G : K) : K := (U * ((E ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (t ^ 2) * ((1 + ((-1) * (t ^ 2))) ^ 2) * (1 + V))
def regionNumerator20 (t d U V P N E F G : K) : K := (F * G * P * U * (d ^ 2) * (t ^ 2) * ((1 + t) ^ 2) * (((-1) + t) ^ 2) * (1 + V))
def regionTerm21 (t d U V P N E F G : K) : K := (U * ((E ^ 1)⁻¹) * ((N ^ 1)⁻¹) * ((1 + ((-1) * (t ^ 2))) ^ 2) * (1 + ((-2) * (t ^ 2))))
def regionNumerator21 (t d U V P N E F G : K) : K := ((-1) * F * G * P * U * (d ^ 2) * ((1 + t) ^ 2) * (((-1) + t) ^ 2) * ((-1) + (2 * (t ^ 2))))
def regionTerm22 (t d U V P N E F G : K) : K := (V * ((E ^ 1)⁻¹) * ((N ^ 1)⁻¹) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator22 (t d U V P N E F G : K) : K := (F * G * P * V * (d ^ 2) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm23 (t d U V P N E F G : K) : K := (((E ^ 1)⁻¹) * ((F ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (U ^ 2) * (t ^ 2) * ((1 + ((-1) * (t ^ 2))) ^ 3))
def regionNumerator23 (t d U V P N E F G : K) : K := ((-1) * G * P * (U ^ 2) * (d ^ 2) * (t ^ 2) * ((1 + t) ^ 3) * (((-1) + t) ^ 3))
def regionTerm24 (t d U V P N E F G : K) : K := (((F ^ 1)⁻¹) * ((G ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (U ^ 2) * (t ^ 4) * ((1 + ((-1) * (t ^ 2))) ^ 3))
def regionNumerator24 (t d U V P N E F G : K) : K := ((-1) * E * P * (U ^ 2) * (d ^ 2) * (t ^ 4) * ((1 + t) ^ 3) * (((-1) + t) ^ 3))
def regionTerm25 (t d U V P N E F G : K) : K := ((-1) * ((P ^ 1)⁻¹) * (U ^ 2) * (d ^ 2) * (t ^ 4))
def regionNumerator25 (t d U V P N E F G : K) : K := ((-1) * E * F * G * N * (U ^ 2) * (d ^ 4) * (t ^ 4))
def regionTerm26 (t d U V P N E F G : K) : K := ((-1) * U * V * d * (t ^ 5))
def regionNumerator26 (t d U V P N E F G : K) : K := ((-1) * E * F * G * N * P * U * V * (d ^ 3) * (t ^ 5))
def regionTerm27 (t d U V P N E F G : K) : K := ((-1) * U * V * d * ((G ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (t ^ 3) * (1 + ((-1) * (t ^ 2))))
def regionNumerator27 (t d U V P N E F G : K) : K := (E * F * N * U * V * (d ^ 3) * (t ^ 3) * (1 + t) * ((-1) + t))
def regionTerm28 (t d U V P N E F G : K) : K := ((-1) * d * ((E ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (U ^ 2) * (t ^ 3) * (1 + ((-1) * (t ^ 2))) * (1 + (V * (t ^ 2))))
def regionNumerator28 (t d U V P N E F G : K) : K := (F * G * N * (U ^ 2) * (d ^ 3) * (t ^ 3) * (1 + t) * (1 + (V * (t ^ 2))) * ((-1) + t))
def regionTerm29 (t d U V P N E F G : K) : K := (V * d * ((E ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (U ^ 2) * (t ^ 3) * (1 + ((-2) * (t ^ 2))) * ((-1) + (t ^ 2)))
def regionNumerator29 (t d U V P N E F G : K) : K := ((-1) * F * G * N * V * (U ^ 2) * (d ^ 3) * (t ^ 3) * (1 + t) * ((-1) + t) * ((-1) + (2 * (t ^ 2))))
def regionTerm30 (t d U V P N E F G : K) : K := ((-1) * U * d * ((E ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (V ^ 2) * (t ^ 3) * (((-1) + (t ^ 2)) ^ 2))
def regionNumerator30 (t d U V P N E F G : K) : K := ((-1) * F * G * N * U * (V ^ 2) * (d ^ 3) * (t ^ 3) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm31 (t d U V P N E F G : K) : K := (d * ((E ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (V ^ 3) * (t ^ 3) * ((-1) + (t ^ 2)))
def regionNumerator31 (t d U V P N E F G : K) : K := (F * G * N * (V ^ 3) * (d ^ 3) * (t ^ 3) * (1 + t) * ((-1) + t))
def regionTerm32 (t d U V P N E F G : K) : K := ((-1) * V * d * ((E ^ 1)⁻¹) * ((F ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (U ^ 3) * (t ^ 5) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator32 (t d U V P N E F G : K) : K := ((-1) * G * N * V * (U ^ 3) * (d ^ 3) * (t ^ 5) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm33 (t d U V P N E F G : K) : K := ((-1) * V * d * ((F ^ 1)⁻¹) * ((G ^ 1)⁻¹) * ((P ^ 1)⁻¹) * (U ^ 2) * (t ^ 5) * (((-1) + (t ^ 2)) ^ 2))
def regionNumerator33 (t d U V P N E F G : K) : K := ((-1) * E * N * V * (U ^ 2) * (d ^ 3) * (t ^ 5) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm34 (t d U V P N E F G : K) : K := ((-1) * (V ^ 2) * (t ^ 4))
def regionNumerator34 (t d U V P N E F G : K) : K := ((-1) * E * F * G * N * P * (V ^ 2) * (d ^ 2) * (t ^ 4))
def regionTerm35 (t d U V P N E F G : K) : K := (U * V * (t ^ 4) * ((-1) + (t ^ 2)))
def regionNumerator35 (t d U V P N E F G : K) : K := (E * F * G * N * P * U * V * (d ^ 2) * (t ^ 4) * (1 + t) * ((-1) + t))
def regionTerm36 (t d U V P N E F G : K) : K := (((G ^ 1)⁻¹) * (U ^ 2) * (t ^ 4) * ((-1) + (t ^ 2)))
def regionNumerator36 (t d U V P N E F G : K) : K := (E * F * N * P * (U ^ 2) * (d ^ 2) * (t ^ 4) * (1 + t) * ((-1) + t))
def regionTerm37 (t d U V P N E F G : K) : K := ((-1) * U * V * ((d ^ 1)⁻¹) * (t ^ 5))
def regionNumerator37 (t d U V P N E F G : K) : K := ((-1) * E * F * G * N * P * U * V * d * (t ^ 5))
def regionTerm38 (t d U V P N E F G : K) : K := ((U ^ 2) * ((d ^ 1)⁻¹) * (t ^ 3) * ((-1) + (t ^ 2)))
def regionNumerator38 (t d U V P N E F G : K) : K := (E * F * G * N * P * d * (U ^ 2) * (t ^ 3) * (1 + t) * ((-1) + t))
def regionTerm39 (t d U V P N E F G : K) : K := ((-1) * V * ((G ^ 1)⁻¹) * (U ^ 2) * ((d ^ 1)⁻¹) * (t ^ 5) * ((1 + ((-1) * (t ^ 2))) ^ 2))
def regionNumerator39 (t d U V P N E F G : K) : K := ((-1) * E * F * N * P * V * d * (U ^ 2) * (t ^ 5) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm40 (t d U V P N E F G : K) : K := ((-1) * ((N ^ 1)⁻¹) * (U ^ 2) * ((d ^ 2)⁻¹) * (t ^ 4))
def regionNumerator40 (t d U V P N E F G : K) : K := ((-1) * E * F * G * P * (U ^ 2) * (t ^ 4))
def regionTerm41 (t d U V P N E F G : K) : K := (V * ((N ^ 1)⁻¹) * (U ^ 2) * ((d ^ 2)⁻¹) * (t ^ 4) * ((-1) + (t ^ 2)))
def regionNumerator41 (t d U V P N E F G : K) : K := (E * F * G * P * V * (U ^ 2) * (t ^ 4) * (1 + t) * ((-1) + t))
def regionTerm42 (t d U V P N E F G : K) : K := ((-1) * ((G ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (U ^ 2) * (V ^ 2) * ((d ^ 2)⁻¹) * (t ^ 6) * (((-1) + (t ^ 2)) ^ 2))
def regionNumerator42 (t d U V P N E F G : K) : K := ((-1) * E * F * P * (U ^ 2) * (V ^ 2) * (t ^ 6) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm43 (t d U V P N E F G : K) : K := (U * V * ((G ^ 1)⁻¹) * ((N ^ 1)⁻¹) * ((d ^ 1)⁻¹) * (t ^ 3) * ((-1) + (t ^ 2)))
def regionNumerator43 (t d U V P N E F G : K) : K := (E * F * P * U * V * d * (t ^ 3) * (1 + t) * ((-1) + t))
def regionTerm44 (t d U V P N E F G : K) : K := (((E ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (U ^ 2) * (t ^ 4) * (1 + V) * ((-1) + (t ^ 2)))
def regionNumerator44 (t d U V P N E F G : K) : K := (F * G * P * (U ^ 2) * (d ^ 2) * (t ^ 4) * (1 + V) * (1 + t) * ((-1) + t))
def regionTerm45 (t d U V P N E F G : K) : K := (((E ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (U ^ 2) * (t ^ 2) * (1 + ((-2) * (t ^ 2))) * ((-1) + (t ^ 2)))
def regionNumerator45 (t d U V P N E F G : K) : K := ((-1) * F * G * P * (U ^ 2) * (d ^ 2) * (t ^ 2) * (1 + t) * ((-1) + t) * ((-1) + (2 * (t ^ 2))))
def regionTerm46 (t d U V P N E F G : K) : K := ((-1) * U * V * ((E ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (t ^ 2) * (((-1) + (t ^ 2)) ^ 2))
def regionNumerator46 (t d U V P N E F G : K) : K := ((-1) * F * G * P * U * V * (d ^ 2) * (t ^ 2) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm47 (t d U V P N E F G : K) : K := (((E ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (V ^ 2) * (t ^ 2) * ((-1) + (t ^ 2)))
def regionNumerator47 (t d U V P N E F G : K) : K := (F * G * P * (V ^ 2) * (d ^ 2) * (t ^ 2) * (1 + t) * ((-1) + t))
def regionTerm48 (t d U V P N E F G : K) : K := ((-1) * ((E ^ 1)⁻¹) * ((F ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (U ^ 3) * (t ^ 4) * (((-1) + (t ^ 2)) ^ 2))
def regionNumerator48 (t d U V P N E F G : K) : K := ((-1) * G * P * (U ^ 3) * (d ^ 2) * (t ^ 4) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def regionTerm49 (t d U V P N E F G : K) : K := ((-1) * ((F ^ 1)⁻¹) * ((G ^ 1)⁻¹) * ((N ^ 1)⁻¹) * (U ^ 3) * (t ^ 6) * (((-1) + (t ^ 2)) ^ 2))
def regionNumerator49 (t d U V P N E F G : K) : K := ((-1) * E * P * (U ^ 3) * (d ^ 2) * (t ^ 6) * ((1 + t) ^ 2) * (((-1) + t) ^ 2))
def rawRegionTerms (t d U V P N E F G : K) : Fin 50 → K :=
  ![regionTerm0 t d U V P N E F G, regionTerm1 t d U V P N E F G, regionTerm2 t d U V P N E F G, regionTerm3 t d U V P N E F G, regionTerm4 t d U V P N E F G, regionTerm5 t d U V P N E F G, regionTerm6 t d U V P N E F G, regionTerm7 t d U V P N E F G, regionTerm8 t d U V P N E F G, regionTerm9 t d U V P N E F G, regionTerm10 t d U V P N E F G, regionTerm11 t d U V P N E F G, regionTerm12 t d U V P N E F G, regionTerm13 t d U V P N E F G, regionTerm14 t d U V P N E F G, regionTerm15 t d U V P N E F G, regionTerm16 t d U V P N E F G, regionTerm17 t d U V P N E F G, regionTerm18 t d U V P N E F G, regionTerm19 t d U V P N E F G, regionTerm20 t d U V P N E F G, regionTerm21 t d U V P N E F G, regionTerm22 t d U V P N E F G, regionTerm23 t d U V P N E F G, regionTerm24 t d U V P N E F G, regionTerm25 t d U V P N E F G, regionTerm26 t d U V P N E F G, regionTerm27 t d U V P N E F G, regionTerm28 t d U V P N E F G, regionTerm29 t d U V P N E F G, regionTerm30 t d U V P N E F G, regionTerm31 t d U V P N E F G, regionTerm32 t d U V P N E F G, regionTerm33 t d U V P N E F G, regionTerm34 t d U V P N E F G, regionTerm35 t d U V P N E F G, regionTerm36 t d U V P N E F G, regionTerm37 t d U V P N E F G, regionTerm38 t d U V P N E F G, regionTerm39 t d U V P N E F G, regionTerm40 t d U V P N E F G, regionTerm41 t d U V P N E F G, regionTerm42 t d U V P N E F G, regionTerm43 t d U V P N E F G, regionTerm44 t d U V P N E F G, regionTerm45 t d U V P N E F G, regionTerm46 t d U V P N E F G, regionTerm47 t d U V P N E F G, regionTerm48 t d U V P N E F G, regionTerm49 t d U V P N E F G]
def rawRegionNumerators (t d U V P N E F G : K) : Fin 50 → K :=
  ![regionNumerator0 t d U V P N E F G, regionNumerator1 t d U V P N E F G, regionNumerator2 t d U V P N E F G, regionNumerator3 t d U V P N E F G, regionNumerator4 t d U V P N E F G, regionNumerator5 t d U V P N E F G, regionNumerator6 t d U V P N E F G, regionNumerator7 t d U V P N E F G, regionNumerator8 t d U V P N E F G, regionNumerator9 t d U V P N E F G, regionNumerator10 t d U V P N E F G, regionNumerator11 t d U V P N E F G, regionNumerator12 t d U V P N E F G, regionNumerator13 t d U V P N E F G, regionNumerator14 t d U V P N E F G, regionNumerator15 t d U V P N E F G, regionNumerator16 t d U V P N E F G, regionNumerator17 t d U V P N E F G, regionNumerator18 t d U V P N E F G, regionNumerator19 t d U V P N E F G, regionNumerator20 t d U V P N E F G, regionNumerator21 t d U V P N E F G, regionNumerator22 t d U V P N E F G, regionNumerator23 t d U V P N E F G, regionNumerator24 t d U V P N E F G, regionNumerator25 t d U V P N E F G, regionNumerator26 t d U V P N E F G, regionNumerator27 t d U V P N E F G, regionNumerator28 t d U V P N E F G, regionNumerator29 t d U V P N E F G, regionNumerator30 t d U V P N E F G, regionNumerator31 t d U V P N E F G, regionNumerator32 t d U V P N E F G, regionNumerator33 t d U V P N E F G, regionNumerator34 t d U V P N E F G, regionNumerator35 t d U V P N E F G, regionNumerator36 t d U V P N E F G, regionNumerator37 t d U V P N E F G, regionNumerator38 t d U V P N E F G, regionNumerator39 t d U V P N E F G, regionNumerator40 t d U V P N E F G, regionNumerator41 t d U V P N E F G, regionNumerator42 t d U V P N E F G, regionNumerator43 t d U V P N E F G, regionNumerator44 t d U V P N E F G, regionNumerator45 t d U V P N E F G, regionNumerator46 t d U V P N E F G, regionNumerator47 t d U V P N E F G, regionNumerator48 t d U V P N E F G, regionNumerator49 t d U V P N E F G]
def kernelNumerator (t d U V : K) : K :=
  ((d ^ 2) + ((U ^ 2) * (t ^ 3) * (((-1) * d) + ((-1) * t) + ((-1) * (d ^ 3)) + (d * (t ^ 2)) + ((d ^ 3) * (t ^ 2)) + ((-1) * t * (d ^ 4)))) + ((-1) * (V ^ 4) * (d ^ 2) * (t ^ 6)) + (d * (V ^ 2) * (t ^ 2) * ((t ^ 3) + ((-1) * d) + ((-1) * t) + ((d ^ 2) * (t ^ 3)) + ((-1) * d * (t ^ 2)) + ((-1) * t * (d ^ 2)))) + ((-1) * U * (V ^ 2) * (t ^ 4) * (((-1) * (d ^ 2)) + ((-1) * (t ^ 2)) + (d * (t ^ 3)) + ((d ^ 3) * (t ^ 3)) + ((-1) * d * t) + ((-1) * t * (d ^ 3)) + ((-1) * (d ^ 2) * (t ^ 2)) + ((-1) * (d ^ 4) * (t ^ 2)))) + ((-1) * d * (V ^ 3) * (t ^ 4) * (((-1) * d) + ((-1) * t) + (d * (t ^ 2)) + ((-1) * t * (d ^ 2)))) + (U * V * d * (t ^ 2) * (((-1) * t) + ((-2) * d) + (d * (t ^ 2)) + (d * (t ^ 4)) + ((-1) * t * (d ^ 2)))) + (U * d * (V ^ 3) * (t ^ 6) * (((-1) * d) + ((-1) * t) + (d * (t ^ 2)) + ((-1) * t * (d ^ 2)))) + ((-1) * U * d * (1 + t) * ((-1) + t) * (d + t + (t * (d ^ 2)))) + ((-1) * V * d * (U ^ 2) * (t ^ 4) * (((-1) * d) + ((-1) * t) + (d * (t ^ 2)) + ((-1) * t * (d ^ 2)))) + ((-1) * V * (d ^ 2) * (1 + t) * (1 + (t ^ 2)) * ((-1) + t)))
def regionTerms (t d U V : K) : Fin 50 → K :=
  rawRegionTerms t d U V (1 - d * V * t) (1 - V * t / d)
    (1 - V ^ 2 * t ^ 2) (1 - U * t ^ 2) (1 - U * t ^ 4)
def regionKernel (t d U V : K) : K :=
  kernelNumerator t d U V / (d ^ 2 * (1 - d * V * t) * (1 - V * t / d))
def rawNumeratorSum (t d U V P N E F G : K) : K := ((E * F * G * N * (d ^ 2)) + (E * N * (U ^ 2) * (d ^ 2) * (t ^ 6)) + (E * N * (U ^ 2) * (d ^ 2) * (t ^ 10)) + (E * P * (U ^ 2) * (d ^ 2) * (t ^ 4)) + (F * G * P * U * (d ^ 2)) + (F * G * P * V * (d ^ 2)) + (G * N * U * (d ^ 2) * (t ^ 2)) + (G * N * U * (d ^ 2) * (t ^ 6)) + (G * P * (U ^ 2) * (d ^ 2) * (t ^ 2)) + ((-1) * E * P * (U ^ 2) * (d ^ 2) * (t ^ 10)) + ((-1) * E * P * (U ^ 3) * (d ^ 2) * (t ^ 6)) + ((-1) * E * P * (U ^ 3) * (d ^ 2) * (t ^ 10)) + ((-1) * G * P * (U ^ 2) * (d ^ 2) * (t ^ 8)) + ((-1) * G * P * (U ^ 3) * (d ^ 2) * (t ^ 4)) + ((-1) * G * P * (U ^ 3) * (d ^ 2) * (t ^ 8)) + ((-3) * E * P * (U ^ 2) * (d ^ 2) * (t ^ 6)) + ((-3) * G * P * (U ^ 2) * (d ^ 2) * (t ^ 4)) + ((-2) * E * N * (U ^ 2) * (d ^ 2) * (t ^ 8)) + ((-2) * G * N * U * (d ^ 2) * (t ^ 4)) + (2 * E * P * (U ^ 3) * (d ^ 2) * (t ^ 8)) + (2 * G * P * (U ^ 3) * (d ^ 2) * (t ^ 6)) + (3 * E * P * (U ^ 2) * (d ^ 2) * (t ^ 8)) + (3 * G * P * (U ^ 2) * (d ^ 2) * (t ^ 6)) + (E * F * N * U * (d ^ 2) * (t ^ 4)) + (E * F * P * U * (d ^ 2) * (t ^ 2)) + (E * F * P * U * (d ^ 2) * (t ^ 6)) + (E * P * V * d * (U ^ 2) * (t ^ 7)) + (E * P * V * d * (U ^ 2) * (t ^ 11)) + (F * G * N * V * (d ^ 2) * (t ^ 2)) + (F * G * N * t * (V ^ 2) * (d ^ 3)) + (F * G * N * (U ^ 2) * (d ^ 3) * (t ^ 5)) + (F * G * N * (V ^ 2) * (d ^ 2) * (t ^ 2)) + (F * G * N * (V ^ 2) * (d ^ 3) * (t ^ 5)) + (F * G * N * (V ^ 3) * (d ^ 3) * (t ^ 5)) + (F * G * P * V * (d ^ 2) * (t ^ 4)) + (F * G * P * d * (V ^ 2) * (t ^ 3)) + (F * G * P * d * (V ^ 3) * (t ^ 3)) + (F * G * P * (V ^ 2) * (d ^ 2) * (t ^ 4)) + (G * N * V * (U ^ 2) * (d ^ 3) * (t ^ 3)) + (G * P * U * V * d * (t ^ 3)) + (G * P * U * V * d * (t ^ 7)) + ((-1) * E * F * G * P * (U ^ 2) * (t ^ 4)) + ((-1) * E * F * N * U * (d ^ 2) * (t ^ 6)) + ((-1) * E * F * P * (U ^ 2) * (V ^ 2) * (t ^ 6)) + ((-1) * E * F * P * (U ^ 2) * (V ^ 2) * (t ^ 10)) + ((-1) * E * N * V * (U ^ 2) * (d ^ 3) * (t ^ 7)) + ((-1) * E * N * V * (U ^ 2) * (d ^ 3) * (t ^ 11)) + ((-1) * F * G * N * V * (d ^ 2) * (t ^ 4)) + ((-1) * F * G * N * (U ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * F * G * N * (V ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * F * G * N * (V ^ 3) * (d ^ 3) * (t ^ 3)) + ((-1) * F * G * P * U * (d ^ 2) * (t ^ 6)) + ((-1) * F * G * P * d * (V ^ 2) * (t ^ 5)) + ((-1) * F * G * P * d * (V ^ 3) * (t ^ 5)) + ((-1) * F * G * P * (U ^ 2) * (d ^ 2) * (t ^ 2)) + ((-1) * F * G * P * (U ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * F * G * P * (V ^ 2) * (d ^ 2) * (t ^ 2)) + ((-1) * G * N * V * (U ^ 2) * (d ^ 3) * (t ^ 9)) + ((-1) * G * N * V * (U ^ 3) * (d ^ 3) * (t ^ 5)) + ((-1) * G * N * V * (U ^ 3) * (d ^ 3) * (t ^ 9)) + ((-3) * F * G * P * U * (d ^ 2) * (t ^ 2)) + ((-3) * G * N * V * (U ^ 2) * (d ^ 3) * (t ^ 5)) + ((-2) * E * F * P * U * (d ^ 2) * (t ^ 4)) + ((-2) * E * P * V * d * (U ^ 2) * (t ^ 9)) + ((-2) * F * G * N * (V ^ 2) * (d ^ 3) * (t ^ 3)) + ((-2) * F * G * P * V * (d ^ 2) * (t ^ 2)) + ((-2) * G * P * U * V * d * (t ^ 5)) + (2 * E * F * P * (U ^ 2) * (V ^ 2) * (t ^ 8)) + (2 * E * N * V * (U ^ 2) * (d ^ 3) * (t ^ 9)) + (2 * F * G * P * (U ^ 2) * (d ^ 2) * (t ^ 4)) + (2 * G * N * V * (U ^ 3) * (d ^ 3) * (t ^ 7)) + (3 * F * G * P * U * (d ^ 2) * (t ^ 4)) + (3 * G * N * V * (U ^ 2) * (d ^ 3) * (t ^ 7)) + (E * F * G * N * U * t * (d ^ 3)) + (E * F * G * P * U * d * t) + (E * F * G * P * V * d * t) + (E * F * G * P * V * (U ^ 2) * (t ^ 6)) + (E * F * N * P * (U ^ 2) * (d ^ 2) * (t ^ 6)) + (E * F * N * U * V * (d ^ 3) * (t ^ 7)) + (F * G * N * U * V * t * (d ^ 3)) + (F * G * P * V * (U ^ 2) * (d ^ 2) * (t ^ 6)) + ((-1) * E * F * G * N * U * (d ^ 3) * (t ^ 3)) + ((-1) * E * F * G * N * (U ^ 2) * (d ^ 4) * (t ^ 4)) + ((-1) * E * F * G * P * U * d * (t ^ 3)) + ((-1) * E * F * G * P * V * (U ^ 2) * (t ^ 4)) + ((-1) * E * F * N * P * (U ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * E * F * N * U * V * (d ^ 3) * (t ^ 5)) + ((-1) * E * F * P * U * V * d * (t ^ 3)) + ((-1) * E * F * P * U * V * d * (t ^ 7)) + ((-1) * F * G * N * U * V * (d ^ 3) * (t ^ 7)) + ((-1) * F * G * N * V * (U ^ 2) * (d ^ 3) * (t ^ 3)) + ((-1) * F * G * N * V * (U ^ 2) * (d ^ 3) * (t ^ 7)) + ((-1) * F * G * P * V * (U ^ 2) * (d ^ 2) * (t ^ 4)) + ((-3) * F * G * N * U * V * (d ^ 3) * (t ^ 3)) + (2 * E * F * P * U * V * d * (t ^ 5)) + (2 * F * G * N * V * (U ^ 2) * (d ^ 3) * (t ^ 5)) + (3 * F * G * N * U * V * (d ^ 3) * (t ^ 5)) + (E * F * G * N * P * V * (d ^ 2) * (t ^ 2)) + (E * F * G * N * P * d * (U ^ 2) * (t ^ 5)) + ((-1) * E * F * G * N * P * V * (d ^ 2) * (t ^ 4)) + ((-1) * E * F * G * N * P * d * (U ^ 2) * (t ^ 3)) + ((-1) * E * F * G * N * P * (V ^ 2) * (d ^ 2) * (t ^ 4)) + ((-1) * E * F * N * P * V * d * (U ^ 2) * (t ^ 5)) + ((-1) * E * F * N * P * V * d * (U ^ 2) * (t ^ 9)) + (2 * E * F * N * P * V * d * (U ^ 2) * (t ^ 7)) + (E * F * G * N * P * U * V * (d ^ 2) * (t ^ 6)) + ((-1) * E * F * G * N * P * U * V * d * (t ^ 5)) + ((-1) * E * F * G * N * P * U * V * (d ^ 2) * (t ^ 4)) + ((-1) * E * F * G * N * P * U * V * (d ^ 3) * (t ^ 5)))
end Algebra
end FourierJacobi


