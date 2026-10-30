-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_empMean
-- name    : BartlettBousquetMendelson_LocalRad_empMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:28.499008+00:00
-- url     : https://prove2.me/theorems/cc6d7f87-7e38-495b-ac67-eb289db22c02
-- title:
--   Empirical mean $P_nf=\frac1n\sum_{i=1}^n f(X_i)$
-- statement:
--   For a function $f:\mathcal X\to\mathbb R$ and a sample $X_1,\dots,X_n$ of points of $\mathcal X$, the **empirical mean** of $f$ is
--
--   $$
--   P_nf=\frac1n\sum_{i=1}^n f(X_i).
--   $$
--
--   The true mean is $Pf=\mathbb E f(X)$, the integral of $f$ against the underlying probability measure $P$. Every error bound of the paper compares $Pf$ with $P_nf$ uniformly over a class of functions.
--
--   **Formalization Note** The sample is a point $\omega=(X_1,\dots,X_n)$ of the product space $\mathcal X^n$, written `Fin n → X`; the statements put the product law $P^{\otimes n}$ on it. For $n=0$ Lean returns $0$; every statement assumes $n\ge1$.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), §1, p. 3 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib

namespace BartlettBousquetMendelson.LocalRad

/-- **Empirical mean `Pₙf = (1/n) Σᵢ f(Xᵢ)`.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), §1, p. 3: "For a function f : X → R, define Pnf = (1/n) Σ_{i=1}^n f(Xi)".

`empMean n f ω` is the average of `f` over the sample `ω = (X₁, …, Xₙ) : Fin n → X`.

**Formalization Note.** The sample is a point `ω : Fin n → X` of the product space; the iid law
`Pⁿ` is put on it by the statements that use it. For `n = 0` Lean's `1/0 = 0` gives the value
`0`; every statement of the mission assumes `0 < n`. -/
noncomputable def empMean {X : Type*} (n : ℕ) (f : X → ℝ) (ω : Fin n → X) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f (ω i)

end BartlettBousquetMendelson.LocalRad


