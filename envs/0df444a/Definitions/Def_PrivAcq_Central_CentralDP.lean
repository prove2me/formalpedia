-- Prove2me | Definitions.Def_PrivAcq_Central_CentralDP
-- name    : PrivAcq_Central_CentralDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:29.825036+00:00
-- url     : https://prove2.me/theorems/e41e2244-e848-4222-bbcc-4bf5af45fe43
-- title:
--   Definition 1, p. 8 — heterogeneous central differential privacy $(\varepsilon_i)_{i=1}^n$
-- statement:
--   Let $\mathcal X$ be a data space and let $n$ be the number of users. A randomized algorithm $\mathcal A$ that maps a dataset $S = (S_1,\dots,S_n) \in \mathcal X^n$ to a real-valued output is described by the law $\mathcal A(S)$ of its output, a measure on $\mathbb R$. Given a vector of privacy levels $\varepsilon = (\varepsilon_i)_{i=1}^n$, the algorithm is **$\varepsilon$-centrally differentially private** if, for every user $i$, every two datasets $S, S' \in \mathcal X^n$ that differ only in user $i$'s entry, and every measurable set $W \subseteq \mathbb R$,
--
--   $$
--   \mathbb P\big(\mathcal A(S) \in W\big) \le e^{\varepsilon_i}\, \mathbb P\big(\mathcal A(S') \in W\big).
--   $$
--
--   Unlike the usual (homogeneous) definition, each user has an individual privacy level $\varepsilon_i$, which bounds how much the output distribution can change when that user's data changes. This is the privacy notion the platform guarantees in the central setting.
--
--   **Formalization Note** The algorithm is represented by the map $S \mapsto$ law of the output (a `Measure ℝ`). "Differ in the $i$-th component" is encoded as agreement on every coordinate $j \ne i$, which also admits $S = S'$ (where the inequality is automatic for $\varepsilon_i \ge 0$). The platform's published `PrivLearn.Generic.IsDP` is the homogeneous notion and is not used here.
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, p. 8, Definition 1

import Mathlib

namespace PrivAcq.Central

open MeasureTheory

/-- Definition 1 (Fallah et al., arXiv:2201.03968v2, p. 8): heterogeneous central differential
privacy. A randomized algorithm, given by the law `A S` of its real-valued output on the dataset
`S : Fin n → X`, is `ε`-centrally differentially private when, for every user `i`, every two
datasets `S, S'` that differ only in user `i`'s entry, and every measurable set `W ⊆ ℝ`,
`P(A(S) ∈ W) ≤ exp(ε i) · P(A(S') ∈ W)`. -/
def IsCentralDP {X : Type*} {n : ℕ} (A : (Fin n → X) → Measure ℝ) (ε : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, ∀ S S' : Fin n → X, (∀ j : Fin n, j ≠ i → S j = S' j) →
    ∀ W : Set ℝ, MeasurableSet W → A S W ≤ ENNReal.ofReal (Real.exp (ε i)) * A S' W

end PrivAcq.Central


