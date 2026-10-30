-- Prove2me | Definitions.Def_CPDETrial_SigT
-- name    : CPDETrial_SigT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:52:05.543979+00:00
-- url     : https://prove2.me/theorems/99367e24-5798-4d36-8188-a4f6f826fd5d
-- title:
--   Posterior covariance $\Sigma^T$ along the realized trial
-- statement:
--   $\Sigma^t(\omega)$ is the posterior covariance of eq. (8) after the first $t$ patients, computed from $\Sigma^0$ along the realized allocations $u^s(\omega)$, $s<t$.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 6 (§1.3) and p. 9, eq. (8)

import Mathlib
import Definitions.Def_CPDETrial_postCov
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The posterior covariance `Σ^T` along the realized trial.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §1.3 (p. 6) and eq. (8) (p. 9).

`SigT Sig0 lam u t ω` is `Σ^t(ω)`: the recursion (8) run from `Σ⁰` along the realized
allocations `u^s(ω)`, `s < t`. -/
noncomputable def SigT {M : ℕ} {Ω : Type*} (Sig0 : Matrix (Fin M) (Fin M) ℝ)
    (lam : Fin M → ℝ≥0) (u : ℕ → Ω → Fin M) (t : ℕ) (ω : Ω) : Matrix (Fin M) (Fin M) ℝ :=
  postCov Sig0 lam (fun s => u s ω) t

end CPDETrial


