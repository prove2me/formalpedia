-- Prove2me | Definitions.Def_HellingerSubadd_condKLSum
-- name    : HellingerSubadd_condKLSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:48:20.419935+00:00
-- url     : https://prove2.me/theorems/2ae80dab-cc3c-4692-9e83-0fad523e2cd0
-- title:
--   Sum of conditional KL divergences along a trajectory
-- statement:
--   With kernels $\kappa_k,\eta_k$ as above and a trajectory $x=(x_0,x_1,\dots,x_n)$, define
--
--   $$
--   K_n(x)=\sum_{i=1}^{n}D_{\mathrm{KL}}\bigl(\kappa_{i-1}(\cdot\mid x_0,x_{1:i-1})\,\big\|\,\eta_{i-1}(\cdot\mid x_0,x_{1:i-1})\bigr)\in[0,\infty],
--   $$
--
--   where $D_{\mathrm{KL}}(P\|Q)=\int\log(dP/dQ)\,dP$ if $P\ll Q$ and $+\infty$ otherwise. This is the integrand of the chain rule for KL divergence in the proof of Lemma A.13.
--
--   **Formalization Note** KL divergence is Mathlib's `klDiv`, which is $+\infty$ unless $P\ll Q$ and the log-likelihood ratio is $P$-integrable. For probability measures the negative part of $\log(dP/dQ)$ is always integrable, so a non-integrable log-likelihood ratio has integral $+\infty$: this is the paper's definition.
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, proof of Lemma A.13, p. 73; KL divergence as defined in Section 2, p. 10

import Mathlib

open MeasureTheory ProbabilityTheory InformationTheory Finset Preorder
open scoped ENNReal

namespace HellingerSubadd

/-- **Sum of conditional KL divergences along a trajectory**
`x ↦ Σ_{i=1}^n D_KL(P^(i)(· | x_{1:i−1}) ∥ Q^(i)(· | x_{1:i−1}))`.
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, proof of Lemma A.13, p. 73 (the integrand of the chain rule for KL
divergence, "Term I"); KL divergence as defined in Section 2, p. 10.

For a trajectory `x = (x_0, …, x_n)` the `k`-th summand (`k = 0, …, n − 1`, the paper's
`i = k + 1`) is `D_KL(κ k (x_0, …, x_k) ∥ η k (x_0, …, x_k))`.

**Formalization Note.** KL divergence is Mathlib's `InformationTheory.klDiv : ℝ≥0∞`, which is `∞`
unless the first measure is absolutely continuous w.r.t. the second and the log-likelihood ratio is
integrable; for probability measures a non-integrable log-likelihood ratio has integral `+∞`
(its negative part is always integrable), so this is the paper's definition. Coordinates as in
`condHellingerSum`. -/
noncomputable def condKLSum {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1))) (n : ℕ) :
    (Π i : Iic n, X i) → ℝ≥0∞ :=
  fun x => ∑ k : Fin n,
    klDiv (κ k (frestrictLe₂ (π := X) k.2.le x)) (η k (frestrictLe₂ (π := X) k.2.le x))

end HellingerSubadd


