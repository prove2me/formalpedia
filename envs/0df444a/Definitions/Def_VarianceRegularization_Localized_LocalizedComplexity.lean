-- Prove2me | Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
-- name    : VarianceRegularization_Localized_LocalizedComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:13:06.399187+00:00
-- url     : https://prove2.me/theorems/2397e694-2484-42e5-a12c-78d6da8c153c
-- title:
--   §2.2, §3.2, (20) — Rademacher complexity, sub-root functions, the localized class and the localization inequality
-- statement:
--   This module fixes the complexity notions of Section 3.2 of Duchi and Namkoong.
--
--   Let $P$ be a probability measure on $\mathcal X$, $\mathcal F$ a class of real functions on $\mathcal X$, and $x_1,\dots,x_n$ a sample.
--
--   1. **Empirical Rademacher complexity** (§2.2, p. 7). For i.i.d. uniform signs $\varepsilon_i\in\{-1,1\}$ independent of the sample,
--   $$
--   \mathfrak R_n(\mathcal F)=\mathbb E_\varepsilon\Big[\sup_{f\in\mathcal F}\frac1n\sum_{i=1}^n\varepsilon_i f(x_i)\Big],
--   $$
--   and $\mathbb E[\mathfrak R_n(\mathcal F)]$ is its expectation over an i.i.d. sample $x_1,\dots,x_n\sim P$.
--   2. **Sub-root functions** (p. 14). A function $\psi:\mathbb R_+\to\mathbb R_+$ is sub-root if it is nonnegative, nondecreasing, and $r\mapsto\psi(r)/\sqrt r$ is nonincreasing on $r>0$.
--   3. **The localized class** at level $r$ is $\{cf : f\in\mathcal F,\ c\in[0,1],\ \mathbb E[c^2f^2]\le r\}$.
--   4. **The localization inequality (20).** A function $\psi_n$ bounds the localized complexity if, for every $r\ge0$,
--   $$
--   \psi_n(r)\ \ge\ \mathbb E\big[\mathfrak R_n(\{cf : f\in\mathcal F,\ c\in[0,1],\ \mathbb E[c^2f^2]\le r\})\big].
--   $$
--
--   Theorem 4 and Lemmas D.2 and D.3 are stated for classes satisfying (20) with a sub-root $\psi_n$.
--
--   **Formalization Note** $\mathfrak R_n$ at a sample is the published `UnderstandingML.rademacher` of the evaluation set $\{(f(x_1),\dots,f(x_n)) : f\in\mathcal F\}$: the average over the $2^n$ sign vectors of a real supremum, which is the true supremum when the evaluation set is nonempty and bounded (the localized class of a nonempty class of $[0,M]$-valued functions contains $0$ and is bounded by $M$). The expectation over the sample is a Bochner integral against the product measure $P^n$; the localization predicate requires the integrand to be integrable for every $r\ge0$, so that the integral is the true expectation and (20) cannot hold vacuously. $\psi$ is a function $\mathbb R\to\mathbb R$ of which only the values on $[0,\infty)$ are constrained.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 7, §2.2 (empirical Rademacher complexity); p. 14, §3.2 (sub-root functions, localized class, inequality (20))

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher

namespace VarianceRegularization.Localized

open MeasureTheory

/-- A **sub-root** function (p. 14, after Bartlett, Bousquet and Mendelson): `ψ : ℝ₊ → ℝ₊` is
nonnegative, nondecreasing, and `r ↦ ψ(r)/√r` is nonincreasing on `r > 0`. Only the values of `ψ`
on `[0, ∞)` matter. -/
def IsSubRoot (ψ : ℝ → ℝ) : Prop :=
  (∀ r, 0 ≤ r → 0 ≤ ψ r) ∧ MonotoneOn ψ (Set.Ici 0) ∧
    AntitoneOn (fun r => ψ r / Real.sqrt r) (Set.Ioi 0)

/-- The localized class `{c f : f ∈ F, c ∈ [0, 1], E[c² f²] ≤ r}` (p. 14). -/
def localizedClass {X : Type*} [MeasurableSpace X] (P : Measure X) (F : Set (X → ℝ)) (r : ℝ) :
    Set (X → ℝ) :=
  {g | ∃ f ∈ F, ∃ c ∈ Set.Icc (0 : ℝ) 1, g = (fun x => c * f x) ∧ ∫ x, (c * f x) ^ 2 ∂P ≤ r}

/-- The empirical Rademacher complexity `ℜ_n(F) = E_ε[sup_{f ∈ F} (1/n) ∑ᵢ εᵢ f(xᵢ)]` at the
sample `s = (x₁, …, x_n)` (§2.2, p. 7): the expectation over i.i.d. uniform signs, at the fixed
sample. It is `UnderstandingML.rademacher` of the evaluation set `{(f(x₁), …, f(x_n)) : f ∈ F}`. -/
noncomputable def empRademacher {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (s : Fin n → X) : ℝ :=
  UnderstandingML.rademacher (UnderstandingML.evalSet F s)

/-- The expected Rademacher complexity `E[ℜ_n(F)]`, the empirical complexity integrated over an
i.i.d. sample `s ∼ Pⁿ`. Every statement that uses it also assumes the integrand is integrable,
so that this Bochner integral is the true expectation. -/
noncomputable def expRademacher {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (F : Set (X → ℝ)) : ℝ :=
  ∫ s, empRademacher F s ∂(Measure.pi fun _ : Fin n => P)

/-- The localization inequality (20) (p. 14): for every level `r ≥ 0`, the empirical Rademacher
complexity of the localized class at level `r` is integrable over the sample and
`ψ_n(r) ≥ E[ℜ_n({c f : f ∈ F, c ∈ [0, 1], E[c² f²] ≤ r})]`. -/
def LocalizationBound {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (n : ℕ) (F : Set (X → ℝ)) (ψ : ℝ → ℝ) : Prop :=
  ∀ r, 0 ≤ r →
    Integrable (fun s : Fin n → X => empRademacher (localizedClass P F r) s)
        (Measure.pi fun _ : Fin n => P) ∧
      expRademacher P n (localizedClass P F r) ≤ ψ r

end VarianceRegularization.Localized


