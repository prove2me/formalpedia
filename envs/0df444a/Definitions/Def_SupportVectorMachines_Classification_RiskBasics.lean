-- Prove2me | Definitions.Def_SupportVectorMachines_Classification_RiskBasics
-- name    : SupportVectorMachines_Classification_RiskBasics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:08:46.409257+00:00
-- url     : https://prove2.me/theorems/0e147acf-cee1-4764-be1f-61b377b2b218
-- title:
--   The $L$-risk and Bayes risk of a loss function
-- statement:
--   A **loss function** on a measurable space $X$ with label set $Y \subset \mathbb R$ closed is
--   a measurable map $L : X \times Y \times \mathbb R \to [0,\infty)$ (Steinwart & Christmann,
--   *Support Vector Machines*, Springer 2008, Definition 2.1, p. 22), restated locally in this
--   chunk's own sub-namespace per Hard Rule 9.
--
--   Given a probability distribution $P$ on $X \times Y$, the **$L$-risk** of a measurable
--   function $f : X \to \mathbb R$ is (Definition 2.2, p. 22)
--   $$
--   R_{L,P}(f) := \int_{X \times Y} L(x,y,f(x)) \, dP(x,y),
--   $$
--   and the **Bayes risk** $R^*_{L,P}$ is the smallest $L$-risk any measurable function can
--   achieve (Definition 2.3, pp. 22-23):
--   $$
--   R^*_{L,P} := \inf \{ R_{L,P}(f) : f : X \to \mathbb R \text{ measurable} \}.
--   $$
--   These are the basic risk quantities Theorem 8.1's oracle inequality is stated in terms of.
--
--   **Formalization Note** Loss is `X → ℝ → ℝ → ℝ`. `risk` is the ordinary (real-valued) Bochner
--   integral over the joint measure `P` on `X × ℝ`, and `bayesRisk` the real infimum of its range
--   over measurable `f` — the same convention as this series' `01-loss-functions` mission,
--   restated here rather than imported.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22-23, Definitions 2.1-2.3

import Mathlib

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- A loss function (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22, restated locally per Hard Rule 9), represented as a curried function
`X → ℝ → ℝ → ℝ`. -/
abbrev Loss (X : Type*) : Type _ := X → ℝ → ℝ → ℝ

/-- The `L`-risk of `f` with respect to a distribution `P` on `X × ℝ` (Definition 2.2, p. 22):
`R_{L,P}(f) := ∫_{X×Y} L(x,y,f(x)) dP(x,y)`, as an ordinary (junk-at-non-integrable) Bochner
integral. -/
noncomputable def risk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ))
    (f : X → ℝ) : ℝ :=
  ∫ p, L p.1 p.2 (f p.1) ∂P

/-- The Bayes (minimal) `L`-risk with respect to `P` (Definition 2.3, p. 22-23):
`R*_{L,P} := inf { R_{L,P}(f) : f : X → ℝ measurable }`. -/
noncomputable def bayesRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ)) :
    ℝ :=
  sInf {r : ℝ | ∃ f : X → ℝ, Measurable f ∧ risk L P f = r}

end SupportVectorMachines.Classification


