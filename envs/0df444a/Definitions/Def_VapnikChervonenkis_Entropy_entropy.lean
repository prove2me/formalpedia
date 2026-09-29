-- Prove2me | Definitions.Def_VapnikChervonenkis_Entropy_entropy
-- name    : VapnikChervonenkis_Entropy_entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:04:22.25437+00:00
-- url     : https://prove2.me/theorems/aa398a77-08cf-4acb-b7a3-62c74444a481
-- title:
--   The entropy H^S(l) = E log₂ Δ^S(x_1, …, x_l)
-- statement:
--   Let $(X, P)$ be a probability space, $S$ a collection of subsets of $X$, and let $x_1, \dots, x_l$ be an independent sample of size $l$ from $P$, i.e. a point of $X^l$ distributed according to the product measure $P^l$. The **entropy of the system of events $S$ in samples of size $l$** is the expected binary logarithm of the index:
--
--   $$
--   H^S(l) = \mathbf{E}\, \log_2 \Delta^S(x_1, \dots, x_l) = \int_{X^l} \log_2 \Delta^S(x_1, \dots, x_l)\, dP^l .
--   $$
--
--   Since $1 \le \Delta^S \le 2^l$ for nonempty $S$, one has $0 \le H^S(l) \le l$. Unlike the growth function, the entropy depends on the distribution $P$. Theorem 4 shows that uniform convergence in probability of relative frequencies to probabilities over $S$ holds exactly when $H^S(l)/l \to 0$.
--
--   **Formalization Note.** The paper assumes (p. 273) that the index is a measurable function of the sample; the theorems of the mission carry this as a hypothesis, under which the integrand is bounded and measurable and the Bochner integral is the genuine expectation. The logarithm is `Real.logb 2`, with `Real.logb 2 0 = 0`; the index is $0$ only for $S = \emptyset$, where $H^S(l) = 0$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 273, Subsection 6

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index

namespace VapnikChervonenkis.Entropy

open MeasureTheory

/-- The **entropy** `H^S(l) = E log₂ Δ^S(x_1, …, x_l)` of the system of events `S` in samples of
size `l` (Vapnik and Chervonenkis 1971, p. 273, Subsection 6): the expectation, under the
product law `P^l` of an independent sample of size `l`, of the binary logarithm of the index.
The index takes values in `{0, 1, …, 2^l}`; `Real.logb 2 0 = 0` (the value `0` occurs only when
`S = ∅`). The paper assumes the index is measurable (p. 273); under that assumption the integrand
is bounded and measurable, so the Bochner integral is the genuine expectation. -/
noncomputable def entropy {X : Type*} [MeasurableSpace X] (S : Set (Set X)) (P : Measure X)
    (l : ℕ) : ℝ :=
  ∫ x, Real.logb 2 (Shared.index S x : ℝ) ∂(Measure.pi fun _ : Fin l => P)

end VapnikChervonenkis.Entropy


