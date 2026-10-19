-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P09
-- name    : QAlgorithms_Papers_Independent_Frontier18_P09
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:58:51.5174+00:00
-- url     : https://prove2.me/theorems/727378b8-2a6d-4952-b4dc-1ba3b72f0b6f
-- title:
--   Definitions for Squashed entanglement in infinite dimensions
-- statement:
--   The objects the formalized statements of *Squashed entanglement in infinite dimensions* (arXiv:1507.08964) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `partialTraceRightCoeff`: Partial trace over B in orthonormal coordinates (PDF p.4, Section 2). On trace-class inputs each diagonal block series is absolutely convergent. The unrestricted array formula is used below only on density operators.
--   - `partialTraceLeftCoeff`: Partial trace over A in orthonormal coordinates (PDF p.4, Section 2). The sum is the actual partial trace for every trace-class input.
--   - `marginalStatesA`: The set S_A of all A marginals of states in S (Lemma 1, PDF p.4). The marginal is computed from the joint operator, rather than supplied as independent data. Equality of coefficients is equality of operators.
--   - `marginalStatesB`: The set S_B of all B marginals of states in S (Lemma 1, PDF p.4).
--   - `traceConverges`: Trace-norm convergence of operator coefficients (PDF p.4, Section 2). The nuclear norm `traceSize` is the trace norm on trace-class operators. Extended nonnegative values avoid a default real infimum for nonnuclear arrays; the statements below use only trace-class differences.
-- source:
--   Squashed entanglement in infinite dimensions, arXiv:1507.08964v5, https://arxiv.org/abs/1507.08964v5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

/-!
# Squashed entanglement in infinite dimensions: preliminary state-space results

Source: M. E. Shirokov, arXiv:1507.08964v5, PDF pp.4–5.
The pinned accepted library `Dependency50.P33` supplies all trace-class density
operators, pure states, and the trace-norm topology. Countable nonempty
orthonormal coordinate sets represent all nonzero separable complex Hilbert
spaces, and Cartesian-product coordinates represent their completed Hilbert
tensor product. No finite-rank or finite-energy restriction is imposed.
The remaining planned nodes are explicitly recorded in this unit's HARD.md
and GAPS.json; no substitute finite-dimensional statement is asserted.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier18.P09

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize)

/-- Partial trace over B in orthonormal coordinates (PDF p.4, Section 2).
On trace-class inputs each diagonal block series is absolutely convergent.
The unrestricted array formula is used below only on density operators. -/
def partialTraceRightCoeff {I J : Type}
    (X : Matrix (I × J) (I × J) ℂ) : Matrix I I ℂ :=
  fun i j => ∑' b : J, X (i, b) (j, b)

/-- Partial trace over A in orthonormal coordinates (PDF p.4, Section 2).
The sum is the actual partial trace for every trace-class input. -/
def partialTraceLeftCoeff {I J : Type}
    (X : Matrix (I × J) (I × J) ℂ) : Matrix J J ℂ :=
  fun i j => ∑' a : I, X (a, i) (a, j)

/-- The set S_A of all A marginals of states in S (Lemma 1, PDF p.4).
The marginal is computed from the joint operator, rather than supplied as
independent data. Equality of coefficients is equality of operators. -/
def marginalStatesA {I J : Type} (S : Set (State (I × J))) : Set (State I) :=
  {sigma | ∃ rho ∈ S,
    sigma.coefficients = partialTraceRightCoeff rho.coefficients}

/-- The set S_B of all B marginals of states in S (Lemma 1, PDF p.4). -/
def marginalStatesB {I J : Type} (S : Set (State (I × J))) : Set (State J) :=
  {sigma | ∃ rho ∈ S,
    sigma.coefficients = partialTraceLeftCoeff rho.coefficients}

/-- Trace-norm convergence of operator coefficients (PDF p.4, Section 2).
The nuclear norm `traceSize` is the trace norm on trace-class operators.
Extended nonnegative values avoid a default real infimum for nonnuclear
arrays; the statements below use only trace-class differences. -/
def traceConverges {I : Type} (rho : ℕ → Matrix I I ℂ)
    (sigma : Matrix I I ℂ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ᶠ k in Filter.atTop, traceSize (rho k - sigma) < ENNReal.ofReal epsilon

example {I J : Type} :
    partialTraceRightCoeff (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  funext i j
  simp [partialTraceRightCoeff]

example {I J : Type} :
    partialTraceLeftCoeff (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  funext i j
  simp [partialTraceLeftCoeff]

example {I J : Type} (S : Set (State (I × J))) (rho : State (I × J))
    (hrho : rho ∈ S) (sigma : State I)
    (h : sigma.coefficients = partialTraceRightCoeff rho.coefficients) :
    sigma ∈ marginalStatesA S := by
  exact ⟨rho, hrho, h⟩

example {I J : Type} : marginalStatesB (∅ : Set (State (I × J))) = ∅ := by
  ext sigma
  simp [marginalStatesB]

example {I : Type} (rho : ℕ → Matrix I I ℂ) (sigma : Matrix I I ℂ)
    (h : traceConverges rho sigma) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ k in Filter.atTop, traceSize (rho k - sigma) < ENNReal.ofReal epsilon := by
  exact h epsilon hepsilon

end QAlgorithms.Papers.Independent.Frontier18.P09


