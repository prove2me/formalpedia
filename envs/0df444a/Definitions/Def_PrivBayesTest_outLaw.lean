-- Prove2me | Definitions.Def_PrivBayesTest_outLaw
-- name    : PrivBayesTest_outLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:55.39231+00:00
-- url     : https://prove2.me/theorems/841adccf-f716-424b-a07a-278deb00eeab
-- title:
--   Output law $M(P^n)$ of a mechanism on an i.i.d. sample
-- statement:
--   A **mechanism** on $n$ data points with output space $\mathcal Y$ is a Markov kernel $M$ from $\mathcal X^n$ (product $\sigma$-algebra) to $\mathcal Y$: on input $x\in\mathcal X^n$ it outputs a random element of $\mathcal Y$ with law $M(x)$. For a probability measure $P$ on $\mathcal X$, the **output law** of $M$ on an i.i.d. sample from $P$ is
--
--   $$
--   M(P^n)(S) \;=\; \int_{\mathcal X^n} M(x)(S)\, dP^n(x), \qquad S\subseteq \mathcal Y \text{ measurable},
--   $$
--
--   the law of $M(X)$ when $X\sim P^n$. It appears in Definition 1.2 and throughout §2.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Definition 1.2, eq. (3), p.5

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PrivBayesTest

/-- The **output law** `M(Pⁿ)` of a randomized mechanism `M` run on an i.i.d. sample of size `n`
from `P` (Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), §1.3.1, p.5, Definition 1.2).

**Formalization Note** A mechanism on `n` data points is a Markov kernel `κ` from `Xⁿ = Fin n → X`
(product σ-algebra) to its output space `Y`; `M(Pⁿ)` is the composition `κ ∘ₘ Pⁿ` of the kernel with
the product measure `Pⁿ = Measure.pi (fun _ => P)`. -/
noncomputable def outLaw {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (κ : Kernel (Fin n → X) Y) (P : Measure X) [IsProbabilityMeasure P] : Measure Y :=
  κ ∘ₘ Measure.pi (fun _ : Fin n => P)

end PrivBayesTest


