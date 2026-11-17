-- Prove2me | Definitions.Def_BlockBochner_Supplement_fugacityProb
-- name    : BlockBochner_Supplement_fugacityProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:30:14.265238+00:00
-- url     : https://prove2.me/theorems/ff90149c-e9ae-4e66-b4d6-7c39403ade52
-- title:
--   Fugacity measure $\mu(S)\propto\prod_{i\in S}\lambda_i$ on independent sets
-- statement:
--   Let $M=(E,\mathcal I)$ be a finite matroid and $\lambda\in(0,\infty)^E$ a fugacity vector. The fugacity measure is the probability measure on $\mathcal I$
--   $$
--   \mu(S)=\frac1Z\prod_{i\in S}\lambda_i\quad(S\in\mathcal I),\qquad Z=\sum_{S\in\mathcal I}\prod_{i\in S}\lambda_i .
--   $$
--   When every $\lambda_i=1$ it is the uniform distribution on independent sets.
--
--   **Formalization Note** The ground set is a finite type; the family $\mathcal I$ is a predicate on finite subsets (in the theorems, the independent sets of a Mathlib matroid). $\mu(S)$ is set to $0$ for $S\notin\mathcal I$. Positivity of $\lambda$ is a hypothesis of the theorems; then $Z>0$ because $\emptyset\in\mathcal I$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 5, p.30 (PDF p.31)

import Mathlib

namespace BlockBochner.Supplement

open Classical in
/-- **Fugacity measure on independent sets.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 5, p.30: for a finite
matroid `M = (E, I)` and a fugacity vector `λ ∈ (0,∞)^E`,
```
µ(S) = (1/Z) Π_{i∈S} λ_i   (S ∈ I),      Z = Σ_{S∈I} Π_{i∈S} λ_i .
```
`fugacityProb I lam S` is `µ(S)` for `S` in the family `I`, and `0` for `S ∉ I`.

**Formalization Note** The ground set is the finite type `α`; the family of independent sets is
a predicate `I` on finite subsets (instantiated in the theorems by `M.Indep` of a Mathlib matroid).
The theorems assume `λ_i > 0`; then `Z > 0` because `∅ ∈ I`. -/
noncomputable def fugacityProb {α : Type*} [Fintype α] (I : Finset α → Prop) (lam : α → ℝ)
    (S : Finset α) : ℝ :=
  if I S then (∏ i ∈ S, lam i) / ∑ T ∈ Finset.univ.filter I, ∏ i ∈ T, lam i else 0

end BlockBochner.Supplement


