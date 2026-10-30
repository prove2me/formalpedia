-- Prove2me | Definitions.Def_FoundationsRL_DECLower_condKLSum
-- name    : FoundationsRL_DECLower_condKLSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:14:22.691803+00:00
-- url     : https://prove2.me/theorems/b8e6aff1-68f9-4ed1-ae0d-d6935ac3d1b9
-- title:
--   Sum of conditional KL divergences $\sum_{i}D_{\mathrm{KL}}(P_i(\cdot\mid x_{1:i-1})\,\|\,Q_i(\cdot\mid x_{1:i-1}))$
-- statement:
--   For two families of kernels $(\kappa_k)$, $(\eta_k)$ as in the sequential-process law and a trajectory $x=(x_0,\dots,x_n)$, define
--
--   $$
--   \sum_{i=1}^n D_{\mathrm{KL}}\bigl(\kappa_{i-1}(\cdot\mid x_{0:i-1})\,\big\|\,\eta_{i-1}(\cdot\mid x_{0:i-1})\bigr),
--   $$
--
--   the sum of the conditional KL divergences along the trajectory.
--
--   It is the integrand of the right-hand side of the chain rule (6.35).
--
--   **Formalization Note** KL divergence is Mathlib's, valued in $[0,\infty]$, equal to $+\infty$ off absolute continuity, as on p. 96. This is a local copy of the same object drafted in the mission on Foster, Kakade, Qian & Rakhlin (2021), which is not yet published.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 22, (6.35), p. 107; KL divergence, §6.2, p. 96

import Mathlib

open MeasureTheory ProbabilityTheory InformationTheory Finset Preorder
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **Sum of conditional KL divergences along a trajectory**
`x ↦ Σ_{i=1}^n D_KL(P_i(· | x_{1:i−1}) ∥ Q_i(· | x_{1:i−1}))`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 22, (6.35), p. 107 (the integrand of the right-hand side); KL divergence, §6.2, p. 96.

For a trajectory `x = (x_0, …, x_n)` the `k`-th summand (`k = 0, …, n − 1`, the paper's `i = k + 1`)
is `D_KL(κ k (x_0, …, x_k) ∥ η k (x_0, …, x_k))`.

**Formalization Note.** KL divergence is Mathlib's `InformationTheory.klDiv : ℝ≥0∞`, equal to `∞`
unless the first measure is absolutely continuous with respect to the second and the
log-likelihood ratio is integrable; for probability measures this is p. 96's definition. -/
noncomputable def condKLSum {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1))) (n : ℕ) :
    (Π i : Iic n, X i) → ℝ≥0∞ :=
  fun x => ∑ k : Fin n,
    klDiv (κ k (frestrictLe₂ (π := X) k.2.le x)) (η k (frestrictLe₂ (π := X) k.2.le x))

end FoundationsRL.DECLower


