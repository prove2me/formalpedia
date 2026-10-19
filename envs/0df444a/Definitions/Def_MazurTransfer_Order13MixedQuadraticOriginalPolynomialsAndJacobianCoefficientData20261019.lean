-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalPolynomialsAndJacobianCoefficientData20261019
-- name    : MazurTransfer_Order13MixedQuadraticOriginalPolynomialsAndJacobianCoefficientData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T02:17:08.177573+00:00
-- url     : https://prove2.me/theorems/33cb1d24-cd92-497c-9918-5c3985c44d24
-- title:
--   Original mixed quadratic chart polynomials and Jacobian coefficients
-- statement:
--   Twelve original polynomials and integral coefficient functions for the ordinary and reciprocal actual mixed quadratic charts. All twelve complete types and whole values are compared with the original source. Named downstream consumers: the integral Jacobian identities and actual dyadic affine chart smoothness.
-- source:
--   MazurTheorem original mixed quadratic coordinate and integral Jacobian constructions; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: explicit integral Jacobian certificates for the two mixed
quadratic charts proposed at two. Named downstream consumer: genuine
smoothness of their coordinate algebras over the localization of Z at two.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.Order13MixedQuadraticJacobianCertificates
open Polynomial
universe u
variable (R : Type u) [CommRing R]

def ordinaryH : Polynomial R := X ^ 3 + X ^ 2 + 1
def ordinaryF : Polynomial R := X * (X + 1)
def reciprocalH : Polynomial R := 1 + X + X ^ 3
def reciprocalF : Polynomial R := X ^ 4 + X ^ 5

def ordinaryB0 (x : R) : R := 624 * x ^ 4 + 289 * x ^ 3 - 101 * x ^ 2 + 1713 * x + 232
def ordinaryB1 (x : R) : R := -450 * x ^ 2 + 924 * x - 535
def ordinaryC0 (x : R) : R := -1350 * x ^ 3 - 624 * x ^ 2 - 289 * x + 349
def ordinaryC1 (x : R) : R := 1350 * x ^ 4 + 1102 * x + 1233

def reciprocalB0 (x : R) : R := 90 * x ^ 5 + 442 * x ^ 4 + 427 * x ^ 3 + 151 * x ^ 2 + 452 * x + 244
def reciprocalB1 (x : R) : R := 30 * x ^ 2 + 392 * x + 293
def reciprocalC0 (x : R) : R := 944 * x ^ 5 + 1818 * x ^ 4 + 898 * x ^ 3 + 39 * x ^ 2 - 39 * x + 39
def reciprocalC1 (x : R) : R := 180 * x ^ 4 - 340 * x + 29

end MazurTransfer.Order13MixedQuadraticJacobianCertificates
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.ordinaryH
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.ordinaryF
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.reciprocalH
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.reciprocalF
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.ordinaryB0
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.ordinaryB1
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.ordinaryC0
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.ordinaryC1
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.reciprocalB0
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.reciprocalB1
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.reciprocalC0
#print axioms MazurTransfer.Order13MixedQuadraticJacobianCertificates.reciprocalC1


