-- Prove2me | Definitions.Def_CPDETrial_tauBar
-- name    : CPDETrial_tauBar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:49:47.60928+00:00
-- url     : https://prove2.me/theorems/8c596e2a-c5f6-40f7-8d98-f7aeb9b25579
-- title:
--   Lookahead horizon $\bar\tau$ of Lemma EC.1 (corrected)
-- statement:
--   The corrected horizon
--
--   $$
--   \bar\tau=\left\lceil \frac{\max_j \Sigma^0_{j,j}}{4\,(\min_j c_j)^2}\right\rceil .
--   $$
--
--   The paper prints $\bar\tau=\lceil\sqrt{(2\min_j\lambda_j/\pi)\max_j\Sigma^0_{j,j}/\min_j c_j}\rceil$ (Lemma EC.1 and (EC.11)); with that value the upper bound of Lemma EC.1 fails. Example: $M=2$, $\mu^0=0$, $\Sigma^0=0.01 I$, $\Lambda=I$, $c=(10^{-4},10^{-4})$; the printed $\bar\tau$ is $8$ and $\nu^{cKG_{1:8}}_1\approx107.6$, while sampling arm 1 exactly 75 times already gives $\nu^*_1\ge186.2$. Beyond the corrected $\bar\tau$ an extra sample costs more than its expected gain, which is what Lemma EC.1 needs.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. ec3, Lemma EC.1, and p. ec5, eq. (EC.11) (corrected)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The lookahead horizon `τ̄` of Lemma EC.1 — corrected.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), Lemma EC.1 (p. ec3) and eq. (EC.11) (p. ec5) print
`τ̄ = ⌈√((2 min_j{λ_j}/π) · max_j{Σ⁰_{j,j}}/min_j{c_j})⌉`. With that value the upper bound
`ν* ≤ ν^{cKG_{1:τ̄}}` of Lemma EC.1 is false (counterexample: `M = 2`, `µ⁰ = 0`, `Σ⁰ = 0.01·I`,
`Λ = I`, `c = (10⁻⁴, 10⁻⁴)`: the printed `τ̄` is `8` and `ν^{cKG_{1:8}}_1 ≈ 107.6`, while the
deterministic stopping time `T ≡ 75` already gives `ν*_1 ≥ 186.2`).

`tauBar Sig0 c = ⌈max_j Σ⁰_{j,j} / (4 (min_j c_j)²)⌉`, the corrected horizon.

**Formalization Note.** `⨆`/`⨅` over `Fin M` are the finite max/min for `M ≥ 1`; `⌈·⌉₊` is the
natural-number ceiling (the argument is positive for `Σ⁰` positive definite and `c > 0`). -/
noncomputable def tauBar {M : ℕ} (Sig0 : Matrix (Fin M) (Fin M) ℝ) (c : Fin M → ℝ) : ℕ :=
  ⌈(⨆ j, Sig0 j j) / (4 * (⨅ j, c j) ^ 2)⌉₊

end CPDETrial


