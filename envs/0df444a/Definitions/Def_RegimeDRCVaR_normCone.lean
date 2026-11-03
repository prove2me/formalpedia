-- Prove2me | Definitions.Def_RegimeDRCVaR_normCone
-- name    : RegimeDRCVaR_normCone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:44.952635+00:00
-- url     : https://prove2.me/theorems/8a4e2c6f-6c5d-4842-a99a-64b3215b40a8
-- title:
--   The $\ell_m$ norm cone $\{(p;u)\mid\|p\|_m\le u\}$
-- statement:
--   The **$\ell_m$ norm cone** is
--   $$
--   \bar K=\{(p;u)\in\mathbb R^{I+1} \mid \|p\|_m\le u\}.
--   $$
--   In the proof of Theorem 1 the inner minimization (EC.6) is a conic problem over this cone, and its dual cone is the norm cone of the conjugate norm.
--
--   **Formalization Note** $\mathbb R^{I+1}$ is $\mathbb R^I\times\mathbb R$.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, p.ec3 after (EC.6)

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM

open scoped ENNReal

namespace RegimeDRCVaR

/-- **The ℓm norm cone** `K̄ = {(p; u) ∈ ℝ^{I+1} | ‖p‖_m ≤ u}`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, proof of Theorem 1, p.ec3, after (EC.6)).

**Formalization Note** `ℝ^{I+1}` is `(Fin I → ℝ) × ℝ`. -/
def normCone {I : ℕ} (m : ℝ≥0∞) : Set ((Fin I → ℝ) × ℝ) :=
  {z | normM m z.1 ≤ z.2}

end RegimeDRCVaR


