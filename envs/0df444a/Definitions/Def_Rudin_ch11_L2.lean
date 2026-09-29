-- Prove2me | Definitions.Def_Rudin_ch11_L2
-- name    : Rudin_ch11_L2
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T20:06:34.834695+00:00
-- url     : https://prove2.me/theorems/192a7d3c-8661-4c87-aca4-12b99b4aac70
-- title:
--   The space $\mathscr{L}^2(\mu)$, its norm, Cauchy sequences and convergence in the mean
-- statement:
--   Rudin's space of square-integrable functions, as functions rather than as equivalence classes. A measurable $f$ belongs to $\mathscr{L}^2(\mu)$ when $\int |f|^2\,d\mu < \infty$ (Definition 11.34), and its norm is $\|f\|_2 = \left(\int |f|^2\,d\mu\right)^{1/2}$. A sequence $\{f_n\}$ **converges in the mean** to $f$ if $\|f_n - f\|_2 \to 0$, and is a **Cauchy sequence in $\mathscr{L}^2(\mu)$** if for every $\varepsilon > 0$ there is an $N$ with $\|f_n - f_m\|_2 < \varepsilon$ for all $m, n \ge N$ (Definition 11.41). The underlying measure theory — measurable spaces, measures, measurability, integrability and the integral itself — is Mathlib's and is reused; what is introduced here is Rudin's $\mathscr{L}^2$ of genuine functions, with the explicit $\varepsilon$-$N$ conditions, as opposed to Mathlib's quotient space $L^p$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, pp. 326-329, Definitions 11.34 and 11.41

import Mathlib

/-!
# Rudin, Chapter 11 — the space `ℒ²(μ)`

Definitions transcribed from Walter Rudin, *Principles of Mathematical Analysis*, 3rd edition,
Chapter 11 (Definitions 11.34, 11.39, 11.41, 11.44 and equation (86) of Chapter 8).

Rudin builds measure theory from scratch — rings of sets, outer measures, the Carathéodory
extension, measurable functions and the integral — and all of that is available in Mathlib and
is reused: `MeasureTheory.OuterMeasure`, `MeasurableSet`, `Measurable`, `Integrable`, and the
Bochner integral `∫ x, f x ∂μ`.

What is set up here is Rudin's space `ℒ²(μ)` in his own terms — a measurable function whose
square is integrable — together with the norm `‖f‖₂ = (∫ |f|² dμ)^{1/2}`, Cauchy sequences and
convergence *in the mean*, phrased with explicit `ε`'s rather than through Mathlib's `Lp`
quotient space.  Working with functions rather than with equivalence classes is what makes the
statement of the Riesz–Fischer theorem match the book.
-/

namespace Rudin

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- Rudin, Definition 11.34: `f ∈ ℒ²(μ)`, a measurable real function whose square is
integrable. -/
def MemL2 (μ : Measure X) (f : X → ℝ) : Prop :=
  Measurable f ∧ Integrable (fun x => (f x) ^ 2) μ

/-- Rudin, Definition 11.34: the norm `‖f‖₂ = (∫ |f|² dμ)^{1/2}`. -/
noncomputable def L2Norm (μ : Measure X) (f : X → ℝ) : ℝ :=
  Real.sqrt (∫ x, (f x) ^ 2 ∂μ)

/-- Rudin, Definition 11.41: `{fₙ}` **converges to `f` in the mean** (that is, in `ℒ²(μ)`) if
`‖fₙ - f‖₂ → 0`. -/
def TendstoL2 (μ : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
  Filter.Tendsto (fun n => L2Norm μ fun x => f n x - g x) Filter.atTop (nhds 0)

/-- Rudin, Definition 11.41: `{fₙ}` is a **Cauchy sequence in `ℒ²(μ)`** if for every `ε > 0`
there is an `N` with `‖fₙ - fₘ‖₂ < ε` for all `m, n ≥ N`. -/
def CauchyL2 (μ : Measure X) (f : ℕ → X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, L2Norm μ (fun x => f n x - f m x) < ε

end Rudin


