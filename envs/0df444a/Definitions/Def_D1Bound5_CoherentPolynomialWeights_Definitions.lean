-- Prove2me | Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
-- name    : D1Bound5_CoherentPolynomialWeights_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:51:01.471985+00:00
-- url     : https://prove2.me/theorems/eafcab27-93b3-4fe5-9cb0-e4d1afe695de
-- title:
--   Coherent Polynomial Weights
-- statement:
--   The integral polynomial weights for two anchors. The named objects in this bundle include `coherentVandermonde2`, `coherentVandermonde3`, `coherentVandermonde4`, `coherentWeights2`, `coherentWeights3`, `coherentWeights4`.
-- source:
--   D1Bound5/CoherentPolynomialWeights.lean, lines 8-9, SHA-256 f098961571ae9eda9b1aeb7c0bb7cf7d0b039a9b7e5f64da44f922daabe473a5; D1Bound5/CoherentPolynomialWeights.lean, lines 11-12, SHA-256 f098961571ae9eda9b1aeb7c0bb7cf7d0b039a9b7e5f64da44f922daabe473a5; D1Bound5/CoherentPolynomialWeights.lean, lines 14-16, SHA-256 f098961571ae9eda9b1aeb7c0bb7cf7d0b039a9b7e5f64da44f922daabe473a5; D1Bound5/CoherentPolynomialWeights.lean, lines 18-20, SHA-256 f098961571ae9eda9b1aeb7c0bb7cf7d0b039a9b7e5f64da44f922daabe473a5; D1Bound5/CoherentPolynomialWeights.lean, lines 22-24, SHA-256 f098961571ae9eda9b1aeb7c0bb7cf7d0b039a9b7e5f64da44f922daabe473a5; D1Bound5/CoherentPolynomialWeights.lean, lines 26-31, SHA-256 f098961571ae9eda9b1aeb7c0bb7cf7d0b039a9b7e5f64da44f922daabe473a5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset

namespace D1Bound5

def coherentVandermonde2 {R : Type*} [CommRing R] (a : Fin 2 → R) : R :=
  a 0 - a 1

def coherentVandermonde3 {R : Type*} [CommRing R] (a : Fin 3 → R) : R :=
  (a 0 - a 1) * (a 0 - a 2) * (a 1 - a 2)

def coherentVandermonde4 {R : Type*} [CommRing R] (a : Fin 4 → R) : R :=
  (a 0 - a 1) * (a 0 - a 2) * (a 0 - a 3) *
    (a 1 - a 2) * (a 1 - a 3) * (a 2 - a 3)

/-- The integral polynomial weights for two anchors. -/
def coherentWeights2 {R : Type*} [CommRing R] (_a : Fin 2 → R) : Fin 2 → R :=
  ![1, -1]

/-- The integral polynomial weights for three anchors. -/
def coherentWeights3 {R : Type*} [CommRing R] (a : Fin 3 → R) : Fin 3 → R :=
  ![a 0 * (a 1 - a 2), -a 1 * (a 0 - a 2), a 2 * (a 0 - a 1)]

/-- The integral polynomial weights for four anchors. -/
def coherentWeights4 {R : Type*} [CommRing R] (a : Fin 4 → R) : Fin 4 → R :=
  ![(a 0)^2 * (a 1 - a 2) * (a 1 - a 3) * (a 2 - a 3),
    -(a 1)^2 * (a 0 - a 2) * (a 0 - a 3) * (a 2 - a 3),
    (a 2)^2 * (a 0 - a 1) * (a 0 - a 3) * (a 1 - a 3),
    -(a 3)^2 * (a 0 - a 1) * (a 0 - a 2) * (a 1 - a 2)]



















end D1Bound5
end


