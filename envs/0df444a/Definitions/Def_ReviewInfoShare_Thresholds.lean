-- Prove2me | Definitions.Def_ReviewInfoShare_Thresholds
-- name    : ReviewInfoShare_Thresholds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:38:46.203191+00:00
-- url     : https://prove2.me/theorems/61929746-b7ea-4380-8d35-08d9f961b204
-- title:
--   Thresholds $\Phi_q$, $(\Phi^0_i,\Psi^0_i)$, $(\Phi^\infty_i,\Psi^\infty_i)$, $\bar\Phi_q$ of (10), (13), (14), (18)
-- statement:
--   The thresholds of the paper. Write $D=\pi(\underline q)-\pi(\bar q)$. Then
--   $$
--   \Phi_q=\frac{2D}{\sigma_\theta^2(\bar q^2-\underline q^2)},\qquad
--   \Phi^0_i=\frac{2D}{\sigma_\theta^2\bigl(\bar q^2-\tfrac43\underline q^2\bigr)},\qquad
--   \Psi^0_i=\frac13\underline q^2,
--   $$
--   $$
--   \Phi^\infty_i=\frac{2D}{\sigma_\theta^2\bigl(\bar q^2-\tfrac43\underline q^2-\tfrac13\sigma_p^2\bigr)},\qquad
--   \Psi^\infty_i=\frac13(\underline q^2+\sigma_p^2),\qquad
--   \bar\Phi_q=\frac{2(\pi_u(\underline q)-\pi_u(\bar q))}{\sigma_\theta^2(\bar q^2-\underline q^2)} .
--   $$
--   They are the printed values of (10), (13), (14) and (18), and they describe the quality decision and the sharing decision in the two boundary regimes.
--
--   **Formalization Note** The denominators of $\Phi^0_i$ and $\Phi^\infty_i$ are positive exactly when $\bar q^2-\underline q^2$ exceeds $\Psi^0_i$ and $\Psi^\infty_i$ respectively. The threshold statements use $\Phi^0_i$, $\Phi^\infty_i$ only together with that condition, and (15) only where neither denominator is zero, so Lean's division by zero is never reached in a meaningful clause.
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, (10), p.17; (13), p.19; (14), p.20; (18), p.22

import Mathlib
import Definitions.Def_ReviewInfoShare_Model

namespace ReviewInfoShare

namespace Params

/-- The quality threshold `Φ_q = 2(π(q̲) − π(q̄))/(σ_θ²(q̄² − q̲²))`, SSRN 3886954, (10), p.17. -/
noncomputable def phiQ (P : Params) : ℝ :=
  2 * (P.pi .low - P.pi .high) / (P.σθ ^ 2 * (P.qH ^ 2 - P.qL ^ 2))

/-- The sharing threshold `Φ⁰ᵢ = 2(π(q̲) − π(q̄))/(σ_θ²(q̄² − (4/3)q̲²))` at `γ = 0`,
SSRN 3886954, (13), p.19.

**Formalization Note.** The denominator is positive exactly when `q̄² − q̲² > Ψ⁰ᵢ`; the threshold
statements use `Φ⁰ᵢ` only under that condition, and (15) only where the denominator is not zero. -/
noncomputable def phiI0 (P : Params) : ℝ :=
  2 * (P.pi .low - P.pi .high) / (P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2))

/-- The quality-gap threshold `Ψ⁰ᵢ = q̲²/3` at `γ = 0`, SSRN 3886954, (13), p.19. -/
noncomputable def psiI0 (P : Params) : ℝ := P.qL ^ 2 / 3

/-- The sharing threshold `Φ^∞ᵢ = 2(π(q̲) − π(q̄))/(σ_θ²(q̄² − (4/3)q̲² − (1/3)σ_p²))` at `γ = ∞`,
SSRN 3886954, (14), p.20.

**Formalization Note.** The denominator is positive exactly when `q̄² − q̲² > Ψ^∞ᵢ`; the threshold
statements use `Φ^∞ᵢ` only under that condition, and (15) only where the denominator is not zero. -/
noncomputable def phiIInf (P : Params) : ℝ :=
  2 * (P.pi .low - P.pi .high) / (P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2 - 1 / 3 * P.σp ^ 2))

/-- The quality-gap threshold `Ψ^∞ᵢ = (q̲² + σ_p²)/3` at `γ = ∞`, SSRN 3886954, (14), p.20. -/
noncomputable def psiIInf (P : Params) : ℝ := (P.qL ^ 2 + P.σp ^ 2) / 3

/-- The commission quality threshold `Φ̄_q = 2(π_u(q̲) − π_u(q̄))/(σ_θ²(q̄² − q̲²))`,
SSRN 3886954, (18), p.22. -/
noncomputable def phiBarQ (P : Params) (u : ℝ) : ℝ :=
  2 * (P.piU u .low - P.piU u .high) / (P.σθ ^ 2 * (P.qH ^ 2 - P.qL ^ 2))

end Params

end ReviewInfoShare


