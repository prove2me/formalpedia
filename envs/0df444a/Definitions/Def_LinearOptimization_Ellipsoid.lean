-- Prove2me | Definitions.Def_LinearOptimization_Ellipsoid
-- name    : LinearOptimization_Ellipsoid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-06T14:42:01.53276+00:00
-- url     : https://prove2.me/theorems/a5932281-d090-4927-ba02-e3dd88cd4ec5
-- title:
--   Ellipsoid $E(z, D)$ with positive definite matrix $D$
-- statement:
--   **(Definitions 8.4-8.6, p. 364, and Definition 8.7, p. 370)** An $n \times n$ symmetric matrix $D$ is called *positive definite* if $\mathbf{x}'D\mathbf{x} > 0$ for all nonzero vectors $\mathbf{x} \in \mathbb{R}^n$ (Def 8.4; Mathlib's Matrix.PosDef).
--
--   A set $E$ of vectors in $\mathbb{R}^n$ of the form
--
--   $$E = E(\mathbf{z}, D) = \{\mathbf{x} \in \mathbb{R}^n \mid (\mathbf{x}-\mathbf{z})'D^{-1}(\mathbf{x}-\mathbf{z}) \le 1\},$$
--
--   where $D$ is an $n \times n$ positive definite symmetric matrix, is called an *ellipsoid* with center $\mathbf{z} \in \mathbb{R}^n$ (Def 8.5); for any $r > 0$, $E(\mathbf{z}, r^2 I) = \{\mathbf{x} \mid \|\mathbf{x}-\mathbf{z}\| \le r\}$ is the ball centered at $\mathbf{z}$ of radius $r$.
--
--   If $D$ is an $n \times n$ nonsingular matrix and $\mathbf{b} \in \mathbb{R}^n$, the mapping $S(\mathbf{x}) = D\mathbf{x} + \mathbf{b}$ is called an *affine transformation*, with image $S(L) = \{\mathbf{y} \mid \mathbf{y} = D\mathbf{x} + \mathbf{b} \text{ for some } \mathbf{x} \in L\}$ (Def 8.6).
--
--   The *volume* of $L \subset \mathbb{R}^n$ is $\mathrm{Vol}(L) = \int_{\mathbf{x} \in L} d\mathbf{x}$ (Lebesgue volume). A polyhedron is *full-dimensional* if it has positive volume (Def 8.7).
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definitions 8.4-8.6, p. 364; Definition 8.7, p. 370

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Ellipsoids, affine transformations, and full-dimensional sets.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997:

- **Definition 8.4 (p. 364).** An `n × n` symmetric matrix `D` is positive
  definite if `x'Dx > 0` for every nonzero `x` — this is Mathlib's
  `Matrix.PosDef` (whose `IsHermitian` component, over `ℝ`, is exactly
  symmetry); no custom Def is minted (Mathlib-first).
- **Definition 8.5 (p. 364).** A set of the form
  `E = E(z, D) = {x ∈ ℝⁿ | (x − z)'D⁻¹(x − z) ≤ 1}`, with `D` an `n × n`
  positive definite symmetric matrix, is an *ellipsoid* with center `z`.
  For `r > 0`, `E(z, r²I) = {x | ‖x − z‖ ≤ r}` is the ball centered at `z`
  with radius `r` (the def `ellipsoidBall` below packages `E(z, r²I)`).
- **Definition 8.6 (p. 364).** For `S : ℝⁿ → ℝⁿ` of the form `S(x) = Dx + b`
  with `D` an `n × n` nonsingular matrix and `b ∈ ℝⁿ`, `S` is an *affine
  transformation*, with image `S(L) = {y | y = Dx + b for some x ∈ L}`.
- **Volume (p. 365).** `Vol(L) = ∫_{x ∈ L} dx` — Mathlib's Lebesgue
  `MeasureTheory.volume` on `Fin n → ℝ` (the pi measure); no custom Def.
- **Definition 8.7 (p. 370).** A polyhedron is *full-dimensional* if it has
  positive volume. (Stated for an arbitrary subset of `ℝⁿ`.)

The `D⁻¹` in `ellipsoid` is Mathlib's `Matrix.inv` (junk `D⁻¹ = 0` for
singular `D`); every theorem using `ellipsoid` carries a `Matrix.PosDef`
guard, per the series faithfulness rules.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Definition 8.5 (p. 364).** The ellipsoid with center `z` and
(positive definite symmetric) shape matrix `D`:
`E(z, D) = {x | (x − z)'D⁻¹(x − z) ≤ 1}`. (`D⁻¹` is Mathlib matrix
inverse; statements guard `D` with `Matrix.PosDef`.) -/
def ellipsoid {n : ℕ} (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  {x | (x - z) ⬝ᵥ D⁻¹.mulVec (x - z) ≤ 1}

/-- **Bertsimas & Tsitsiklis, Definition 8.5 (p. 364), ball case.** `E(z, r²I)`, the ball
centered at `z` of radius `r` (for `r > 0` it equals
`{x | ‖x − z‖ ≤ r}`). -/
def ellipsoidBall {n : ℕ} (z : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  ellipsoid z (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))

/-- **Bertsimas & Tsitsiklis, Definition 8.6 (p. 364).** The image `S(L)` of `L ⊆ ℝⁿ` under the
affine transformation `S(x) = Dx + b` (`D` nonsingular in the book's
definition; the nonsingularity hypothesis appears in the statements that
need it, e.g. Lemma 8.1's volume scaling). -/
def affineTransformImage {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (L : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∃ x ∈ L, y = D.mulVec x + b}

/-- **Bertsimas & Tsitsiklis, Definition 8.7 (p. 370).** A set (in particular, a polyhedron) is
*full-dimensional* if it has positive (Lebesgue) volume. -/
def IsFullDimensional {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  0 < MeasureTheory.volume S

end LinearOptimization


