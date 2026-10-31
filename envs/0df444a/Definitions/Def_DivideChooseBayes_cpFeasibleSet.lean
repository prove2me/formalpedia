-- Prove2me | Definitions.Def_DivideChooseBayes_cpFeasibleSet
-- name    : DivideChooseBayes_cpFeasibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:26.197275+00:00
-- url     : https://prove2.me/theorems/a18dfee7-6901-4b97-997f-a76c853e4eb5
-- title:
--   Feasible set of the program $\mathcal C_P$
-- statement:
--   For divider values $g^D$, prior means $\mu$, standard deviations $\sigma$ and $P$, the feasible set of $\mathcal C_P$ consists of the $q\in\mathbb R^n$ with
--
--   1. $-1\le q_i\le 1$ for all $i$;
--   2. $\sum_i g^D_i q_i\ge 0$;
--   3. $\sum_i \mu_i q_i\le \Phi^{-1}(P)\sqrt{\sum_i \sigma_i^2 q_i^2}$.
--
--   The third constraint says that, under normal priors, the chooser picks pile 1 with probability at most $P$.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Algorithm 1, line 5, p.9

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_normalQuantile

namespace DivideChooseBayes

/-- **The feasible set of the program `C_P`.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Algorithm 1, line 5, p.9: subject to `−1 ≤ qᵢ ≤ 1` for all `1 ≤ i ≤ n`,
`∑ᵢ gᴰᵢ qᵢ ≥ 0`, and `∑ᵢ µᵢ qᵢ ≤ Φ⁻¹(P) √(∑ᵢ σᵢ² qᵢ²)`.

`m` are the prior means `µᵢ` and `σ` the standard deviations.

**Formalization Note.** `Φ⁻¹` is the published `KallMayerSLP.NormalCC.normalQuantile`,
`Φ⁻¹(P) = inf {x | P ≤ Φ(x)}` with `Φ = cdf (gaussianReal 0 1)`; for `0 < P < 1` it is the inverse of
the continuous, strictly increasing `Φ`. It is only used at `0 < P ≤ 1/2`. -/
noncomputable def cpFeasibleSet {ι : Type*} [Fintype ι] (gD m σ : ι → ℝ) (P : ℝ) : Set (ι → ℝ) :=
  {q | (∀ i, -1 ≤ q i ∧ q i ≤ 1) ∧ 0 ≤ ∑ i, gD i * q i ∧
      ∑ i, m i * q i ≤ KallMayerSLP.NormalCC.normalQuantile P * Real.sqrt (∑ i, σ i ^ 2 * q i ^ 2)}

end DivideChooseBayes


