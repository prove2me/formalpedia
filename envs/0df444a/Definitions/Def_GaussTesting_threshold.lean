-- Prove2me | Definitions.Def_GaussTesting_threshold
-- name    : GaussTesting_threshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:32.959655+00:00
-- url     : https://prove2.me/theorems/0d30de88-084c-4c89-a2ff-c59439e9d0e0
-- title:
--   The threshold $\theta(p_1,p_2)$ of Lemma 2.14 and Algorithm 1
-- statement:
--   For $0\le p_1<p_2\le1$,
--
--   $$
--   \theta(p_1,p_2)=\begin{cases}\dfrac{\log\frac{1-p_1}{1-p_2}}{\log\frac{p_2(1-p_1)}{p_1(1-p_2)}} & \text{if } p_1\ne0 \text{ and } p_2\ne1,\\[2ex] \dfrac{p_2+p_1}{2} & \text{otherwise.}\end{cases}
--   $$
--
--   It is the decision threshold for the sample mean in Lemma 2.14 and in line 6 of Algorithm 1 (with $(p_1,p_2)=(q_1,q_2)$).
--
--   **Formalization Note** For $0<p_1<p_2<1$ both logarithms have arguments greater than $1$, so the formula uses no default value of `Real.log` or of division.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Lemma 2.14, p.19; Algorithm 1, line 6, p.28

import Mathlib

namespace GaussTesting

/-- The threshold of Lemma 2.14 and of line 6 of Algorithm 1:
`θ = log((1−p₁)/(1−p₂)) / log(p₂(1−p₁)/(p₁(1−p₂)))` if `p₁ ≠ 0` and `p₂ ≠ 1`, and `θ = (p₂ + p₁)/2`
otherwise.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Lemma 2.14, p.19; Algorithm 1, line 6, p.28.

**Formalization Note.** For `0 < p₁ < p₂ < 1` both logarithms have arguments `> 1`, so no junk value of
`Real.log` or of division by zero is used in the range where the formula applies. -/
noncomputable def threshold (p₁ p₂ : ℝ) : ℝ :=
  if p₁ ≠ 0 ∧ p₂ ≠ 1 then
    Real.log ((1 - p₁) / (1 - p₂)) / Real.log (p₂ * (1 - p₁) / (p₁ * (1 - p₂)))
  else (p₂ + p₁) / 2

end GaussTesting


