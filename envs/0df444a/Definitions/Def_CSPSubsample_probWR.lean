-- Prove2me | Definitions.Def_CSPSubsample_probWR
-- name    : CSPSubsample_probWR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:20.392232+00:00
-- url     : https://prove2.me/theorems/04299bcf-a4e9-4bf1-9de0-3f535b6552e2
-- title:
--   Sampling $N$ variables uniformly with replacement: probabilities, expectations, and the set of unique variables
-- statement:
--   Sample $N$ variables $i_1,\dots,i_N$ independently and uniformly from $[n]$. The **set of unique variables** of the sample is $U=\{i\in[n]:\exists t,\ i_t=i\}$. The probability of an event $E$ and the expectation of a quantity $F$ of the sample are
--   $$
--   \Pr[E]=\frac{\#\{(i_1,\dots,i_N)\in[n]^N: E\}}{n^N},\qquad \mathbb E[F]=\frac{1}{n^N}\sum_{(i_1,\dots,i_N)\in[n]^N}F(i_1,\dots,i_N).
--   $$
--   These are the random samples of the concentration lemma, of Definition 4.1 and of Claim A.2.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Lemma 3.1, p.6 (PDF p.8); §4, p.8 (PDF p.10); Claim A.2, p.27 (PDF p.29)

import Mathlib

set_option autoImplicit false

namespace CSPSubsample

/-- The set of unique variables of a sample `s = (i_1, …, i_N)` of `N` variables drawn from
`[n]` (arXiv:2608.00203 (PDF sha256 fd9ae011…), Lemma 3.1, p.6 = PDF p.8, "let U be the resulting
set of unique variables"; Claim A.2, p.27 = PDF p.29, `U_2 = {i : ∃ t, I_t = i}`). -/
def sampleSet {n N : ℕ} (s : Fin N → Fin n) : Finset (Fin n) :=
  Finset.univ.image s

/-- The probability of an event when **`N` variables are sampled uniformly with replacement from
`[n]`** (arXiv:2608.00203 (PDF sha256 fd9ae011…), Lemma 3.1, p.6, Definition 4.1 and the pairs
`(i_t, a_t)`, p.8, Claim A.2, p.27): `#{s : [N] → [n] : E(s)} / n^N`.

**Formalization Note** The sample is a sequence `s : Fin N → Fin n`, uniform over the `n^N`
sequences (i.i.d. uniform draws). -/
noncomputable def probWR (n N : ℕ) (E : (Fin N → Fin n) → Prop) [DecidablePred E] : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (n : ℝ) ^ N

/-- The expectation of `F(s)` when `s` is a sample of `N` variables drawn uniformly with
replacement from `[n]` (arXiv:2608.00203 (PDF sha256 fd9ae011…), `E[f(Z)]`, Lemmas 4.2 and 4.4,
pp.8–10): `(1/n^N) ∑_{s : [N] → [n]} F(s)`. -/
noncomputable def expWR (n N : ℕ) (F : (Fin N → Fin n) → ℝ) : ℝ :=
  (∑ s : Fin N → Fin n, F s) / (n : ℝ) ^ N

end CSPSubsample


