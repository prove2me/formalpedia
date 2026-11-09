-- Prove2me | Definitions.Def_HierADA_failureProb
-- name    : HierADA_failureProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:11.598817+00:00
-- url     : https://prove2.me/theorems/5af3b5a9-de45-4dec-bf5f-764c40713242
-- title:
--   Failure probability $\Pr[\exists t\le k: |a_t-\mathbb E_P f_t|>\alpha]$
-- statement:
--   Let $\mu$ be a probability measure on seeds, $M$ a randomized mechanism on $N$ samples over a finite domain $X$, $P$ a distribution on $X$, $A$ an adaptive analyst, $\alpha\in\mathbb R$ and $k\in\mathbb N$. The **failure probability** is
--
--   $$
--   \Pr_{S\sim P^N,\ \omega\sim\mu}\Big[\exists t\le k:\ \big|a_t-\mathbb E_{x\sim P}f_t(x)\big|>\alpha\Big]
--   =\sum_{s\in X^N}P^N(s)\,\mu\{\omega:\ \text{the }k\text{-round transcript of }A\text{ with }M_\omega\text{ on }s\text{ has an error}>\alpha\},
--   $$
--
--   where $f_t$ and $a_t$ are the queries and answers of the $k$-round interaction. The error is measured against the **population** mean, not the empirical one.
--
--   **Formalization Note** The interaction, the i.i.d. sample law $P^N$, the population mean and the error event are the published `IsRandomnessNecessaryADA.Plain` objects. The seed measure is applied to each section of the bad set directly, which is Lean's outer measure; the goal theorem also requires each section to be measurable.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Theorem 3.8, p.25

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_RandMechanism

set_option autoImplicit false

open MeasureTheory IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Failure probability of a randomized ADA mechanism** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint
(version of 2026-11-03, sha256 f220ae51…), Theorem 3.8, p.25.

For a seed law `μ`, a randomized mechanism `M` on `N` samples, a distribution `P` on the finite
domain `X`, an analyst `A`, an accuracy `α` and a number of queries `k`, this is the probability,
over the sample `S ∼ P^N` and the seed `ω ∼ μ`, that the `k`-round interaction of `A` with
`M ω` on `S` contains an answer whose distance to the **population** mean of its query exceeds `α`:
$$\Pr_{S\sim P^N,\ \omega\sim\mu}\bigl[\exists t\le k:\ |a_t-\mathbb E_{X\sim P}f_t(X)|>\alpha\bigr]
 =\sum_{s}P^N(s)\,\mu\{\omega : \text{the transcript on } s \text{ has an error}>\alpha\}.$$

**Formalization Note.** The interaction, the i.i.d. sample law, the population mean and the error
event are those of the published `IsRandomnessNecessaryADA.Plain`. The sample space is finite, so the
product law is the sum over samples of the sample's mass times the seed measure of the section.
The seed measure is applied to the section directly (Lean's outer measure); the goal theorem
additionally asks that every section be measurable. -/
noncomputable def failureProb {Ω X : Type} [MeasurableSpace Ω] [Fintype X] {N : ℕ}
    (μ : Measure Ω) (M : RandMechanism Ω X N) (P : PMF X) (A : Analyst X) (α : ℝ) (k : ℕ) :
    ENNReal :=
  ∑' s : Fin N → X, iid P N s * μ {ω | interaction (M ω) A s k ∈ errorEvent P α}

end HierADA


