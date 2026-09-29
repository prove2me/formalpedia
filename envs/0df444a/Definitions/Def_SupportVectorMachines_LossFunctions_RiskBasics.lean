-- Prove2me | Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics
-- name    : SupportVectorMachines_LossFunctions_RiskBasics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:18:44.019986+00:00
-- url     : https://prove2.me/theorems/730523c2-7387-4a81-855d-41d054aab24f
-- title:
--   The $L$-risk and Bayes risk of a loss function
-- statement:
--   A **loss function** on a measurable space $X$ with label set $Y \subset \mathbb R$ closed is
--   a measurable map $L : X \times Y \times \mathbb R \to [0,\infty)$ (Steinwart & Christmann,
--   *Support Vector Machines*, Springer 2008, Definition 2.1, p. 22): $L(x,y,f(x))$ is read as the
--   cost of predicting $y$ by $f(x)$ when $x$ is observed.
--
--   Given a probability distribution $P$ on $X \times Y$, the **$L$-risk** of a measurable
--   function $f : X \to \mathbb R$ is the average cost of using $f$ to predict a pair drawn from
--   $P$ (Definition 2.2, p. 22):
--
--   $$
--   R_{L,P}(f) := \int_{X \times Y} L(x,y,f(x)) \, dP(x,y).
--   $$
--
--   The **Bayes risk** $R^*_{L,P}$ is the smallest $L$-risk any measurable function can achieve
--   (Definition 2.3, pp. 22-23):
--
--   $$
--   R^*_{L,P} := \inf \{ R_{L,P}(f) : f : X \to \mathbb R \text{ measurable} \}.
--   $$
--
--   These two quantities are the basic vocabulary of the chapter: every learning goal in the book
--   is phrased as making $R_{L,P}(f) - R^*_{L,P}$, the excess risk, small.
--
--   **Formalization Note** The loss is represented as a plain function `X → ℝ → ℝ → ℝ`
--   (`SupportVectorMachines.LossFunctions.Loss`); nonnegativity and the restriction of the middle
--   argument to a specific label set $Y$ are supplied as hypotheses where a concrete loss is used,
--   rather than built into the type. `risk` is the ordinary (real-valued) Bochner integral over
--   the joint measure `P` on `X × ℝ`, and `bayesRisk` the real infimum of its range over
--   measurable `f`.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22-23, Definitions 2.1-2.3

import Mathlib

open MeasureTheory

namespace SupportVectorMachines.LossFunctions

/-- A loss function (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22): given a measurable space `X` and closed label set `Y ⊂ ℝ`, a loss is a
measurable map `L : X × Y × ℝ → [0,∞)`. Here it is represented as a curried function
`X → ℝ → ℝ → ℝ` (the middle argument ranges over the ambient reals; hypotheses fixing it to the
relevant label set `Y` and its nonnegativity are supplied where a specific loss is used, not
baked into the type). -/
abbrev Loss (X : Type*) : Type _ := X → ℝ → ℝ → ℝ

/-- The `L`-risk of `f` with respect to a distribution `P` on `X × ℝ` (Definition 2.2, p. 22):
`R_{L,P}(f) := ∫_{X×Y} L(x,y,f(x)) dP(x,y)`. -/
noncomputable def risk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ))
    (f : X → ℝ) : ℝ :=
  ∫ p, L p.1 p.2 (f p.1) ∂P

/-- The Bayes (minimal) `L`-risk with respect to `P` (Definition 2.3, p. 22-23):
`R*_{L,P} := inf { R_{L,P}(f) : f : X → ℝ measurable }`. The witness `f` is required to have an
`L`-integrable composition against `P`, so that the Bochner integral defining `risk L P f` is
never a junk (non-integrable) `0` masquerading as a genuine candidate risk. -/
noncomputable def bayesRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ)) :
    ℝ :=
  sInf {r : ℝ | ∃ f : X → ℝ, Measurable f ∧
    Integrable (fun p : X × ℝ => L p.1 p.2 (f p.1)) P ∧ risk L P f = r}

end SupportVectorMachines.LossFunctions


