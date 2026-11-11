-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_Analysis
-- name    : EntAssistOneWay_Separation_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:25.24788+00:00
-- url     : https://prove2.me/theorems/bad6bc4d-5d90-4888-8969-d0f1ec03833e
-- title:
--   Finite expectations and Euclidean matrix norms
-- statement:
--   For a finite type $T$ and a real vector space $V$, the uniform average of $a:T\to V$ is
--   $$\mathbb E_{t\in T}a(t)=|T|^{-1}\sum_{t\in T}a(t).$$
--   For a complex matrix $A$ acting on a finite coordinate Hilbert space, $\|A\|_\infty$ is its operator norm for the Euclidean vector norm, and $\|A\|_1$ is the sum of its singular values, counted with multiplicity. The latter is the full Schatten-1 norm. Complex matrices carry the product sigma algebra of their entries. The notation $\log_2 x$ means the logarithm to base two, and $L(d)=\lceil\log_2 d\rceil$ for positive integer $d$.
--
--   The norms are aliases of the published Wilde Schatten-1 norm and SYKEdge Euclidean operator norm. These definitions fix the norm and normalization conventions used in the probability estimates and remote preparation task. The uniform average returns zero on an empty type; every use in a theorem is on a nonempty sample type. $L(0)$ is zero and is never used as a register count in a theorem.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), pp. 11, 16, 19, 27–28, matrix norms, expectation and logarithm conventions

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_SYKEdge_MatrixNorms

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- The entrywise product sigma algebra on a complex matrix. -/
instance matrixMeasurable (I J : Type*) : MeasurableSpace (Matrix I J ℂ) :=
  inferInstanceAs (MeasurableSpace (I → J → ℂ))

/-- Finite uniform expectation, including real, complex, and matrix-valued quantities. -/
def uniformAverage {α V : Type*} [Fintype α] [AddCommMonoid V] [Module ℝ V]
    (f : α → V) : V := (Fintype.card α : ℝ)⁻¹ • ∑ a, f a

/-- The spectral operator norm on Euclidean coordinate spaces. -/
abbrev spectralNorm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : ℝ := SYKEdge.opNorm A

/-- The published full Schatten-1 norm, given a local square-matrix name. -/
abbrev traceNorm {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : ℝ := WildeQIT.traceNorm A

/-- Binary logarithm. -/
def log₂ (x : ℝ) : ℝ := Real.logb 2 x

/-- Number of qubits for a d-dimensional register, used only at d ≥ 1. -/
def logCeil (d : ℕ) : ℕ := ⌈log₂ d⌉₊

end

end EntAssistOneWay.Separation


