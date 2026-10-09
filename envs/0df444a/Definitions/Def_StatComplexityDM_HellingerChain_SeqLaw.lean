-- Prove2me | Definitions.Def_StatComplexityDM_HellingerChain_SeqLaw
-- name    : StatComplexityDM_HellingerChain_SeqLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T19:21:52.993203+00:00
-- url     : https://prove2.me/theorems/c67ddbd2-b5b6-4905-8f7e-9b1ed53bf8e9
-- title:
--   Lemma A.13's setting, p. 73 — sequential kernels P⁽ⁱ⁾(· | x₁:ᵢ₋₁), their joint law P, and E_P[Σᵢ D²_H(P⁽ⁱ⁾, Q⁽ⁱ⁾)]
-- statement:
--   This file sets up the objects of Lemma A.13 of Foster, Kakade, Qian and Rakhlin on finite alphabets.
--
--   Let $n \in \mathbb N$ and let $\mathcal X_1, \dots, \mathcal X_n$ be finite sets. A full sequence is $x = (x_1, \dots, x_n)$ with $x_i \in \mathcal X_i$, and $x_{1:i-1} = (x_1, \dots, x_{i-1})$ is its prefix.
--
--   1. **Sequential kernels.** A family $P = (P^{(i)})_{i=1}^n$ is a family of sequential kernels if, for every $i$ and every sequence $x$, $P^{(i)}(\cdot \mid x)$ is a probability vector on $\mathcal X_i$, and $P^{(i)}(\cdot \mid x)$ depends on $x$ only through the prefix $x_{1:i-1}$. Thus $P^{(i)}(\cdot \mid x_{1:i-1})$ is a probability kernel from $\mathcal X^{(i-1)} = \prod_{t=1}^{i-1} \mathcal X_t$ to $\mathcal X_i$.
--   2. **Sequential law.** The law of $X_1, \dots, X_n$ under $X_i \sim P^{(i)}(\cdot \mid X_{1:i-1})$ is
--   $$
--   \mathbb P(x) = \prod_{i=1}^{n} P^{(i)}(x_i \mid x_{1:i-1}).
--   $$
--   3. **Expected summed conditional Hellinger distance.** For two families $P$, $Q$,
--   $$
--   \mathbb E_{\mathbb P}\Big[\sum_{i=1}^n D^2_{\mathrm H}\big(P^{(i)}(\cdot \mid X_{1:i-1}), Q^{(i)}(\cdot \mid X_{1:i-1})\big)\Big] = \sum_{x} \mathbb P(x) \sum_{i=1}^n D^2_{\mathrm H}\big(P^{(i)}(\cdot \mid x_{1:i-1}), Q^{(i)}(\cdot \mid x_{1:i-1})\big),
--   $$
--   where $D^2_{\mathrm H}(p, q) = \sum_a (\sqrt{p(a)} - \sqrt{q(a)})^2$ is the squared Hellinger distance (5), p. 10.
--
--   These are the objects of the subadditivity inequality (97) and of its bounded-ratio variant (98): the right side of both is the third quantity, and the left side compares the two sequential laws.
--
--   **Formalization Note** The paper works with measurable spaces; this formalization restricts to finite alphabets, so laws are probability vectors and expectations are finite sums. Coordinates are indexed by `Fin n` (0-based). A kernel is a function `P i x` of the whole sequence `x`; the prefix clause of `IsSeqKernel` (equal coordinates `j < i` give equal values) is what makes it a kernel from the prefix. That `seqLaw P` is a probability vector is a consequence, not part of the definition.
-- source:
--   arXiv:2112.13487v3, App. A.2, Lemma A.13 (setting), p. 73; (5), p. 10

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace StatComplexityDM.HellingerChain

open FoundationsRL.GeneralDM

/-- A family of sequential probability kernels on finite alphabets `X 0, …, X (n-1)`
(arXiv:2112.13487v3, App. A.2, Lemma A.13, p. 73): `P i x` is the conditional law of the
`i`-th coordinate given the sequence `x`. It is a probability vector on `X i`, and it depends
only on the prefix `x_{1:i−1}` (the coordinates `j < i`), so that `P i` is a probability kernel
from `X^{(i−1)}` to `X_i`. Coordinates are indexed by `Fin n` (0-based). -/
def IsSeqKernel {n : ℕ} {X : Fin n → Type*} [∀ i, Fintype (X i)]
    (P : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ) : Prop :=
  (∀ i x, (∀ a, 0 ≤ P i x a) ∧ ∑ a, P i x a = 1) ∧
    ∀ i x x', (∀ j, j < i → x j = x' j) → P i x = P i x'

/-- The law of `X_1, …, X_n` under `X_i ∼ P^{(i)}(· | X_{1:i−1})` (Lemma A.13, p. 73): the
probability of the whole sequence `x` is the product of the conditional probabilities,
`P(x) = ∏_i P^{(i)}(x_i | x_{1:i−1})`. -/
noncomputable def seqLaw {n : ℕ} {X : Fin n → Type*}
    (P : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ) (x : (j : Fin n) → X j) : ℝ :=
  ∏ i, P i x (x i)

/-- The expected summed conditional squared Hellinger distance of (97), p. 73:
`E_P[Σ_{i=1}^n D²_H(P^{(i)}(· | X_{1:i−1}), Q^{(i)}(· | X_{1:i−1}))]`, the expectation taken
under the sequential law of `P`. -/
noncomputable def condHellingerSum {n : ℕ} {X : Fin n → Type*} [∀ i, Fintype (X i)]
    (P Q : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ) : ℝ :=
  ∑ x : (j : Fin n) → X j, seqLaw P x * ∑ i, hellingerSq (P i x) (Q i x)

end StatComplexityDM.HellingerChain


