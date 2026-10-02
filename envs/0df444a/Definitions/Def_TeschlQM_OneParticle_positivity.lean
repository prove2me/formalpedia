-- Prove2me | Definitions.Def_TeschlQM_OneParticle_positivity
-- name    : TeschlQM_OneParticle_positivity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:53:48.415114+00:00
-- url     : https://prove2.me/theorems/513f97a1-60c2-4313-9f96-e01a0c9bdfd8
-- title:
--   Positive and strictly positive functions; positivity improving and real operators on L²(ℝⁿ)
-- statement:
--   A function $f \in L^2(\mathbb R^n)$ is **positive** if $f \ge 0$ a.e. and $f \not\equiv 0$, and **strictly positive** if $f > 0$ a.e. A bounded operator $A$ on $L^2(\mathbb R^n)$ is **positivity improving** if
--   $$f \text{ positive} \implies Af > 0 \text{ a.e.},$$
--   and **real** if it maps real functions to real functions.
--
--   These notions drive the proof that the ground state of a Schrödinger operator is simple with a positive eigenfunction.
--
--   **Formalization Note.** Values are complex; $0 \le f(x)$ and $0 < f(x)$ are taken in Mathlib's `ComplexOrder`, i.e. $f(x)$ is a nonnegative, respectively positive, real number. The book writes "$f \ge 0$ implies $Af > 0$"; since $A0 = 0$, the implication is required for positive $f$ (nonzero), which is also what the book's equivalent formulation "$\langle f, Ag\rangle > 0$ for $f, g \ge 0$" means.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 235, Section 10.5

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator

namespace TeschlQM.OneParticle

open MeasureTheory
open scoped ComplexOrder

/-- Teschl, p. 235: `f ∈ L²(ℝⁿ)` is **positive** if `f ≥ 0` a.e. and `f ≢ 0`. The order on `ℂ` is
`ComplexOrder`, so `0 ≤ f(x)` means that `f(x)` is a nonnegative real number. -/
def IsPositive {n : ℕ} (f : L2 n) : Prop :=
  (∀ᵐ x ∂volume, 0 ≤ (f : EuclideanSpace ℝ (Fin n) → ℂ) x) ∧ f ≠ 0

/-- Teschl, p. 235: `f ∈ L²(ℝⁿ)` is **strictly positive** if `f > 0` a.e. (`f(x)` is a positive
real number for a.e. `x`). -/
def IsStrictlyPositive {n : ℕ} (f : L2 n) : Prop :=
  ∀ᵐ x ∂volume, 0 < (f : EuclideanSpace ℝ (Fin n) → ℂ) x

/-- Teschl, p. 235: a bounded operator `A` is **positivity improving** if `f ≥ 0` implies `Af > 0`.
The implication is required for positive `f` (`f ≥ 0`, `f ≢ 0`): for `f = 0` it would fail for
every linear `A`, and the book's equivalent form "`⟨f, Ag⟩ > 0` for `f, g ≥ 0`" likewise concerns
nonzero `f, g`. -/
def IsPositivityImproving {n : ℕ} (A : L2 n →L[ℂ] L2 n) : Prop :=
  ∀ f : L2 n, IsPositive f → IsStrictlyPositive (A f)

/-- Teschl, Theorem 10.11, p. 236: `A` is **real**, it maps real functions to real functions. -/
def IsRealOperator {n : ℕ} (A : L2 n →L[ℂ] L2 n) : Prop :=
  ∀ f : L2 n, (∀ᵐ x ∂volume, ((f : EuclideanSpace ℝ (Fin n) → ℂ) x).im = 0) →
    ∀ᵐ x ∂volume, ((A f : L2 n) x).im = 0

end TeschlQM.OneParticle


