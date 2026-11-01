-- Prove2me | Definitions.Def_PetzFisher_scoreOperator
-- name    : PetzFisher_scoreOperator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:10.859994+00:00
-- url     : https://prove2.me/theorems/a02892d4-327d-4139-aa4d-a7aada73b695
-- title:
--   Quantum score operator $L^f_i(\theta)=(\mathbb J^f_{\rho(\theta)})^{-1}(\partial_{\theta_i}\rho(\theta))$
-- statement:
--   Let $\theta\mapsto\rho(\theta)$, $\theta\in\mathbb R^k$, be a differentiable family of invertible density matrices and $f$ a function as in the definition of $\mathbb J^f_D$. The quantum score operators (logarithmic derivatives) are
--
--   $$
--   L^f_i(\theta):=\big(\mathbb J^f_{\rho(\theta)}\big)^{-1}\big(\partial_{\theta_i}\rho(\theta)\big),\qquad 1\le i\le k. \tag{25}
--   $$
--
--   For $f(x)=(x+1)/2$ this is the symmetric logarithmic derivative. The Fisher information matrix (26) is the Gram matrix of the score operators in the inner product defined by $\mathbb J^f_{\rho(\theta)}$.
--
--   **Formalization Note** $(\mathbb J^f_D)^{-1}$ is the published `inverseMetric f D`, i.e. $B\mapsto\sum_{u,v}(v f(u/v))^{-1}P_uBP_v$ over the distinct eigenvalues of $D$, which is the mapping $(1/f)(\mathbb L_D\mathbb R_D^{-1})\mathbb R_D^{-1}$ of p.8. The printed index range $1\le i\le m$ in (25) is a slip for $1\le i\le k$.
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, §2, eq. (25), p.14

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P31
import Definitions.Def_PetzFisher_partialDeriv

namespace PetzFisher

/-- The quantum score operator (logarithmic derivative) `L^f_i(θ) := (𝕁^f_{ρ(θ)})^{-1}(∂_{θ_i} ρ(θ))`
(Petz–Ghinea, *Introduction to quantum Fisher information*, arXiv:1008.2417v1, §2, eq. (25), p.14:
"The quantum score operators (or logarithmic derivatives) are defined as
`L^f_i(θ) := (𝕁^f_{ρ(θ)})^{-1}(∂_{θ_i} ρ(θ))` (1 ≤ i ≤ m)"; the printed range `1 ≤ i ≤ m` is a slip
for `1 ≤ i ≤ k`, the dimension of the parameter).

**Formalization Note.** `(𝕁^f_D)^{-1}` is the published `Bridge50.P31.inverseMetric f D`, i.e.
`B ↦ Σ_{u,v} (v f(u/v))^{-1} P_u B P_v` over the distinct eigenvalues of `D`, which is the mapping
`(1/f)(𝕃_D ℝ_D^{-1}) ℝ_D^{-1}` of p.8. The parameter `θ` ranges over `ℝᵏ = Fin k → ℝ`, and
`∂_{θ_i} ρ(θ)` is the entrywise `PetzFisher.partialDeriv`. -/
noncomputable def scoreOperator {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (f : ℝ → ℝ)
    (ρ : (Fin k → ℝ) → Matrix I I ℂ) (θ : Fin k → ℝ) (i : Fin k) : Matrix I I ℂ :=
  QAlgorithms.Papers.Independent.Bridge50.P31.inverseMetric f (ρ θ) (partialDeriv ρ θ i)

end PetzFisher


