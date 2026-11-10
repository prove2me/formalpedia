-- Prove2me | Definitions.Def_KikuchiMoore_Moore_Operators
-- name    : KikuchiMoore_Moore_Operators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:13.688198+00:00
-- url     : https://prove2.me/theorems/06bf3427-c90e-49d2-9812-262d5d1228ea
-- title:
--   Euclidean norm and degree-plus-mean normalization
-- statement:
--   For a finite real adjacency matrix $A$, define $d(i)=\sum_j A_{ij}$, the realized mean $\bar d=|I|^{-1}\sum_i d(i)$, $\Gamma(i)=d(i)+\bar d$, and $K_{ij}=A_{ij}/\sqrt{\Gamma(i)\Gamma(j)}$. The norm is the induced Euclidean operator norm, implemented by the continuous linear map on Euclidean coordinate space. A lift with projection $p:X\to I$ and raw matrix $W$ inherits entries $L_{xy}=W_{xy}/\sqrt{\Gamma(p(x))\Gamma(p(y))}$, so truncating a lift does not recompute its normalization. These definitions also cover nonnegative weighted graphs and their parallel-edge sums. Total division returns zero outside the positive-mean domain; the norm lemma explicitly assumes positive mean. The mean on an empty index type is zero.
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Definitions and constructions, Sections 3–5, printed p. 14 = PDF p. 14, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Mathlib

noncomputable section
open scoped BigOperators

namespace KikuchiMoore.Moore

def opNorm {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) A‖

def degree {I : Type*} [Fintype I] (A : Matrix I I ℝ) (i : I) : ℝ := ∑ j, A i j

def meanDegree {I : Type*} [Fintype I] (A : Matrix I I ℝ) : ℝ :=
  (∑ i, degree A i) / Fintype.card I

def gamma {I : Type*} [Fintype I] (A : Matrix I I ℝ) (i : I) : ℝ :=
  degree A i + meanDegree A

def normalized {I : Type*} [Fintype I] (A : Matrix I I ℝ) : Matrix I I ℝ :=
  fun i j => A i j / Real.sqrt (gamma A i * gamma A j)

/-- The lift inherits base normalization, rather than recomputing degrees after truncation. -/
def normalizedLift {I X : Type*} [Fintype I]
    (A : Matrix I I ℝ) (row : X → I) (W : Matrix X X ℝ) : Matrix X X ℝ :=
  fun x y => W x y / Real.sqrt (gamma A (row x) * gamma A (row y))

end KikuchiMoore.Moore


