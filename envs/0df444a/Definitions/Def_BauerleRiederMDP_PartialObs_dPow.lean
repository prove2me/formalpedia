-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_dPow
-- name    : BauerleRiederMDP_PartialObs_dPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:51.321373+00:00
-- url     : https://prove2.me/theorems/0a2457b6-54cb-4563-a44d-15c9f45f40b7
-- title:
--   The sequence $(d_n)$ of the power-utility recursion (6.3)
-- statement:
--   For $0<\gamma<1$ define functions $d_n$ on $\mathbb P(E_Y)$ by
--   $$
--   d_0\equiv\frac1\gamma,\qquad d_n(\rho)=\sup_{\alpha\in\tilde A}\int\!\!\int d_{n-1}\big(\Phi(\rho,z)\big)\big(1+\alpha\cdot z\big)^\gamma\,Q^R(dz\mid y)\,\rho(dy).\tag{6.3}
--   $$
--   Theorem 6.1.2 expresses the value functions of the power-utility terminal wealth problem through $d_n$.
--
--   **Formalization Note** Values in $[0,\infty]$; the supremum is the true one. That $d_n$ is finite is part of Theorem 6.1.2.
-- source:
--   Bäuerle & Rieder (2011), Theorem 6.1.2 a), eq. (6.3), p.178 (PDF 191)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Atilde
import Definitions.Def_BauerleRiederMDP_PartialObs_powObj

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The sequence `(d_n)` of the power-utility case**, recursion (6.3).
Bäuerle & Rieder (2011), Theorem 6.1.2 a), eq. (6.3), p.178 (PDF 191):
`d_0 ≡ 1/γ`,
`d_n(ρ) = sup_{α ∈ Ã} ∫ ∫ d_{n−1}(Φ(ρ, z)) (1 + α · z)^γ Q^R(dz|y) ρ(dy)`.

**Formalization Note.** Values in `ℝ≥0∞` (all terms are nonnegative), so the supremum is the
true one, `+∞` if unbounded; that `d_n` is finite is part of the content of Theorem 6.1.2. -/
noncomputable def dPow {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) (γ : ℝ) :
    ℕ → ProbabilityMeasure EY → ℝ≥0∞
  | 0, _ => ENNReal.ofReal (1 / γ)
  | n + 1, ρ => ⨆ α ∈ Atilde M, powObj M γ (dPow M γ n) ρ α

end BauerleRiederMDP.PartialObs


