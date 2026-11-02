-- Prove2me | Definitions.Def_Grothendieck_Gaussian
-- name    : Grothendieck_Gaussian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-02T04:14:30.31312+00:00
-- url     : https://prove2.me/theorems/ce87cb62-957a-4120-8dbe-b0369fd9ff28
-- title:
--   The standard Gaussian matrix and Grothendieck's rounding expectation
-- statement:
--   Let $r,n$ be positive integers. An $r\times n$ **standard Gaussian matrix** is a random matrix $Z$ whose $rn$ entries are independent random variables, each normally distributed with mean $0$ and variance $1$. For a vector $u\in\mathbb R^n$ the product $Zu\in\mathbb R^r$ is the vector whose coordinates are the inner products of the rows of $Z$ with $u$; it is again Gaussian.
--
--   Grothendieck's rounding identity, in the matrix form proved in Lemma 2.1 of the paper, concerns the **rounding expectation**
--
--   $$
--   \mathbb E\Big[\frac{Zu}{\lVert Zu\rVert}\cdot\frac{Zv}{\lVert Zv\rVert}\Big],
--   $$
--
--   the expected inner product of the two random unit vectors obtained by normalizing $Zu$ and $Zv$ — in other words, the expected correlation of two Gaussian projections after rounding them to the sphere. Normalizing a Gaussian vector to the sphere is exactly the rounding step of the Goemans-Williamson algorithm and, in the paper, step 4 of Algorithm A.
--
--   This file provides the random matrix together with the three pieces of notation the identity needs: the matrix-vector product $Zu$ read as an element of the Euclidean space $\mathbb R^r$ (so that its norm is the Euclidean one), the normalization $y\mapsto y/\lVert y\rVert$ onto the unit sphere, and the expectation itself, integrated against the law of $Z$.
--
--   **Formalization Note** The law of $Z$ is `Measure.pi` of `ProbabilityTheory.gaussianReal 0 1` over the entries, the entries being encoded as a function `Fin r → Fin n → ℝ`. On the null set where $\lVert Zu\rVert=0$ Lean's convention $0^{-1}=0$ applies; since $Z$ has independent continuous entries and $u\neq0$, that set has measure zero and does not affect the integral.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, Lemma 1.1, p. 81; Lemma 2.1, p. 84; Algorithm A, p. 82. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib

/-!
# Gaussian matrix rounding: the expectations of Grothendieck's identity

Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite
programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77--105.

The probabilistic objects of Lemma 1.1, Lemma 2.1 and Algorithm A: a random matrix
`Z ∈ R^{r×n}` with independent standard normal entries, the vectors `Z u` and `Z v`,
their normalizations `Zu/‖Zu‖`, and the rounding expectation
`E[(Zu/‖Zu‖)·(Zv/‖Zv‖)]`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- The law of an `r × n` matrix whose entries are independent `N(0,1)` random
variables (p. 81, Lemma 1.1 and p. 84, Lemma 2.1). -/
def gaussianMatrix (r n : ℕ) : Measure (Fin r → Fin n → ℝ) :=
  Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1

/-- `Z u`: the vector obtained by applying the matrix `Z ∈ R^{r×n}` (encoded as a function
`Fin r → Fin n → ℝ`, which is definitionally `Matrix (Fin r) (Fin n) ℝ`) to `u ∈ R^n`,
regarded as an element of the Euclidean space `R^r`. -/
def mulVecE (r n : ℕ) (Z : Fin r → Fin n → ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin r) :=
  (EuclideanSpace.equiv (Fin r) ℝ).symm ((Matrix.of Z).mulVec ((EuclideanSpace.equiv (Fin n) ℝ) u))

/-- The normalization `y/‖y‖` of a vector, landing on the unit sphere. -/
def normalize (r : ℕ) (y : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℝ (Fin r) :=
  (‖y‖)⁻¹ • y

/-- The expectation `E[(Zu/‖Zu‖)·(Zv/‖Zv‖)]` of Lemma 2.1 (p. 84), where `Z` is an
`r × n` standard Gaussian matrix and `u, v ∈ R^n`. -/
def grothendieckExpectation (r n : ℕ) (u v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ Z, inner ℝ (normalize r (mulVecE r n Z u)) (normalize r (mulVecE r n Z v))
    ∂(gaussianMatrix r n)

end Grothendieck


