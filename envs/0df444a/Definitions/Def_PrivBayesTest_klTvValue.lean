-- Prove2me | Definitions.Def_PrivBayesTest_klTvValue
-- name    : PrivBayesTest_klTvValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:10.324251+00:00
-- url     : https://prove2.me/theorems/68dcd9ab-993a-4dff-9f7b-fe1de8d602e7
-- title:
--   KL–TV objective $F_\alpha$ and value $\sup_\alpha\inf_{R,S}F_\alpha(R,S)$
-- statement:
--   For $\alpha\in\mathbb R$ let $\tilde\alpha=\min(\alpha,1-\alpha)$. For $\varepsilon>0$ and probability measures $P,Q$ on $\mathcal X$, the **KL–TV objective** at a pair $(R,S)$ is
--
--   $$
--   F_\alpha(R,S) \;=\; \alpha\,\mathrm{KL}(R\,\|\,P) + (1-\alpha)\,\mathrm{KL}(S\,\|\,Q) + \tilde\alpha\,\varepsilon\,\mathrm{TV}(R,S),
--   $$
--
--   with $\mathrm{TV}(R,S)=\sup_A |R(A)-S(A)|$ over measurable $A$. Its infimum over pairs of probability measures is $\inf_{R,S\in\Delta(\mathcal X)^2}F_\alpha(R,S)$ (the right-hand side of display (4)), and the **KL–TV value** is
--
--   $$
--   \sup_{\alpha\in(0,1)}\ \inf_{R,S\in\Delta(\mathcal X)^2} F_\alpha(R,S),
--   $$
--
--   the right-hand side of Theorem 1.3 and Lemma 2.1.
--
--   **Formalization Note** $F_\alpha$ is computed in $[0,\infty]$ with Mathlib's KL divergence ($+\infty$ unless $R\ll P$ with integrable log-likelihood ratio, the convention of Definition B.4) and the published total variation `FoundationsRL.DECLower.tvDist`; no $\infty-\infty$ occurs. The outer supremum is an extended-real supremum.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Theorem 1.3, p.5; Proposition 2.3 and display (4), p.9

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory

namespace PrivBayesTest

/-- `α̃ = min(α, 1 − α)` (Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Theorem 1.3, p.5). -/
noncomputable def alphaTilde (α : ℝ) : ℝ := min α (1 - α)

/-- The **KL–TV objective**
`F_α(R, S) = α KL(R ∥ P) + (1 − α) KL(S ∥ Q) + α̃ ε TV(R, S)`
of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Proposition 2.3, p.9 (the bracket of Theorem 1.3, p.5, and of display (4), p.9).

**Formalization Note** Computed in `ENNReal`: KL is Mathlib's `InformationTheory.klDiv` (`= ∞`
unless `R ≪ P` with integrable log-likelihood ratio, the convention of Definition B.4, p.28), the
weights are `ENNReal.ofReal α`, `ENNReal.ofReal (1 − α)`, and TV is the published
`FoundationsRL.DECLower.tvDist` (`sup_A |R(A) − S(A)|` over measurable `A`, Lemma B.7, p.28).
No `∞ − ∞` can occur. -/
noncomputable def klTvObj {X : Type*} [MeasurableSpace X] (ε : ℝ) (P Q : Measure X) (α : ℝ)
    (R S : Measure X) : ENNReal :=
  ENNReal.ofReal α * InformationTheory.klDiv R P + ENNReal.ofReal (1 - α) * InformationTheory.klDiv S Q
    + ENNReal.ofReal (alphaTilde α * ε * FoundationsRL.DECLower.tvDist R S)

/-- The infimum `inf_{R,S ∈ Δ(X)²} F_α(R, S)` over pairs of probability measures on `X`
(Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), display (4), p.9). -/
noncomputable def klTvInf {X : Type*} [MeasurableSpace X] (ε : ℝ) (P Q : Measure X) (α : ℝ) :
    ENNReal :=
  ⨅ (R : ProbabilityMeasure X) (S : ProbabilityMeasure X), klTvObj ε P Q α R S

/-- The **KL–TV value** `sup_{α ∈ (0,1)} inf_{R,S ∈ Δ(X)²} F_α(R, S)`, the right-hand side of
Theorem 1.3 (p.5) and Lemma 2.1 (p.9) of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef).

**Formalization Note** The supremum over `α ∈ (0,1)` is taken in `EReal` (the infima are coerced
from `ENNReal`), so it is never a junk value. -/
noncomputable def klTvValue {X : Type*} [MeasurableSpace X] (ε : ℝ) (P Q : Measure X) : EReal :=
  ⨆ α ∈ Set.Ioo (0 : ℝ) 1, ((klTvInf ε P Q α : ENNReal) : EReal)

end PrivBayesTest


