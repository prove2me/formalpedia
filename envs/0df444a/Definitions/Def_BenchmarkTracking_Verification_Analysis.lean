-- Prove2me | Definitions.Def_BenchmarkTracking_Verification_Analysis
-- name    : BenchmarkTracking_Verification_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:28.657772+00:00
-- url     : https://prove2.me/theorems/5a5242f4-9987-4845-8faa-46645c7514f8
-- title:
--   Lebesgue–Stieltjes integrals against continuous nondecreasing paths, and partial derivatives on closed domains
-- statement:
--   Two pieces of notation used throughout the paper.
--
--   1. **Stieltjes integrals.** For a path $A:[0,\infty)\to\mathbb R$ and a nonnegative integrand $f$, the integral $\int_0^\infty f(s)\,dA_s\in[0,\infty]$ is the Lebesgue integral of $f$ over $[0,\infty)$ against the Lebesgue–Stieltjes measure of $A$ extended by $0$ on $(-\infty,0)$. It is used for paths that are continuous, nondecreasing and vanish at $0$ (the regulators $L^X$, $K^h$, $G^h$), so the measure has no atom at $0$. If the extension is not nondecreasing and right-continuous, the value is set to $+\infty$.
--   2. **Partial derivatives.** For a function $f(a,b)$ or $f(a,b,c)$ and a set $S\subseteq\mathbb R$ of admissible values of one coordinate, the partial derivative in that coordinate is the derivative of the coordinate section within $S$. On an endpoint of $S$ it is one-sided. Higher and mixed derivatives are iterates: $f_{ab}=\partial_b(\partial_af)$.
--
--   These are the integrals in the objective (2.5) and in the representation (3.1), and the derivatives in the Neumann problems (2.8), (3.8), (3.15), (3.38) and in the HJB equation (4.2).
--
--   **Formalization Note** The integral is a `lintegral` against `StieltjesFunction.measure`, so it is never a junk value. Derivatives are `derivWithin` of coordinate sections; for a function that is $C^2$ on a closed product domain they agree with the partial derivatives up to the boundary.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, notation of (2.5), p. 6, (3.1), p. 8, (2.8), p. 7

import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace BenchmarkTracking.Verification

/-!
Bo, Huang & Yu, arXiv:2302.08302v4: two pieces of analysis notation used throughout §§2–4 —
Lebesgue–Stieltjes integrals `∫_0^∞ f(s) dA_s` against a continuous nondecreasing path `A` with
`A_0 = 0` (the integrals against `dL^X`, `dK^h`, `dG^h` in (2.5), (3.1), (3.13)), and partial
derivatives of functions of two and three real variables on closed (half-)domains.
-/

/-- The zero extension of a path `A` given on `[0, ∞)`: `A t` for `t ≥ 0`, `0` for `t < 0`. -/
noncomputable def zeroExt (A : ℝ → ℝ) (t : ℝ) : ℝ := if 0 ≤ t then A t else 0

open scoped Classical in
/-- `∫_{[0,∞)} f(s) dA_s ∈ [0, ∞]` for a nonnegative integrand `f`: the `lintegral` of `f` over
`[0, ∞)` against the Lebesgue–Stieltjes measure of the zero extension of `A`. It is defined when
that extension is nondecreasing and right-continuous (for the paths of the paper: `A` continuous,
nondecreasing, `A_0 = 0`, so there is no atom at `0`); otherwise the value is `∞`, never a
spurious finite number. -/
noncomputable def stieltjesLIntegral (A : ℝ → ℝ) (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  if h : Monotone (zeroExt A) ∧ ∀ x, ContinuousWithinAt (zeroExt A) (Ici x) x then
    ∫⁻ t in Ici 0, f t ∂(StieltjesFunction.mk (zeroExt A) h.1 h.2).measure
  else ∞

/-- Partial derivative in the first variable of `f(a, b)`, taken within the set `S` of admissible
first arguments (one-sided at an endpoint of `S`). -/
noncomputable def pd2₁ (f : ℝ → ℝ → ℝ) (S : Set ℝ) (a b : ℝ) : ℝ :=
  derivWithin (fun a' => f a' b) S a

/-- Partial derivative in the second variable of `f(a, b)`, within the set `S` of admissible
second arguments. -/
noncomputable def pd2₂ (f : ℝ → ℝ → ℝ) (S : Set ℝ) (a b : ℝ) : ℝ :=
  derivWithin (fun b' => f a b') S b

/-- Partial derivative in the first variable of `f(a, b, c)`, within `S`. -/
noncomputable def pd3₁ (f : ℝ → ℝ → ℝ → ℝ) (S : Set ℝ) (a b c : ℝ) : ℝ :=
  derivWithin (fun a' => f a' b c) S a

/-- Partial derivative in the second variable of `f(a, b, c)`, within `S`. -/
noncomputable def pd3₂ (f : ℝ → ℝ → ℝ → ℝ) (S : Set ℝ) (a b c : ℝ) : ℝ :=
  derivWithin (fun b' => f a b' c) S b

/-- Partial derivative in the third variable of `f(a, b, c)`, within `S`. -/
noncomputable def pd3₃ (f : ℝ → ℝ → ℝ → ℝ) (S : Set ℝ) (a b c : ℝ) : ℝ :=
  derivWithin (fun c' => f a b c') S c

end BenchmarkTracking.Verification


