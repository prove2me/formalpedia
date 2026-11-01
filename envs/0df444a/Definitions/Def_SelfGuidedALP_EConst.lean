-- Prove2me | Definitions.Def_SelfGuidedALP_EConst
-- name    : SelfGuidedALP_EConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:58.471999+00:00
-- url     : https://prove2.me/theorems/388cfe5a-856e-4e1b-a53b-6d1ffb606635
-- title:
--   The constant $E_{(N,H)}$
-- statement:
--   For positive integers $N,H$ and $\delta\in(0,1]$,
--   $$
--   E_{(N,H)}:=\frac{2\|B^{*,\perp}_N/\rho\|_{2,\rho}}{(1-\gamma)\,\underline\rho\,\sqrt H}\Bigl(\Omega+2\sqrt{2\ln(1/\delta)}\Bigr),
--   $$
--   with $\underline\rho$ a positive lower bound of $\rho$ on $\Theta$.
--
--   This is the error and the guiding-constraint violation of the goal theorem, and it decreases at rate $1/\sqrt H$.
--
--   **Formalization Note** The norm is the square-root norm of $\mathcal B$. The second argument of the definition is the element $B^{*,\perp}_N$ itself, supplied by the theorem.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.19

import Mathlib
import Definitions.Def_SelfGuidedALP_Omega
import Definitions.Def_SelfGuidedALP_Bspace

namespace SelfGuidedALP

/-- The constant `E_(N,H) := 2‖B^{*,⊥}_N/ρ‖_{2,ρ} / ((1−γ) ρ̲ √H) · (Ω + 2√(2 ln(1/δ)))`, with the
square-root norm, `Bp` standing for `B^{*,⊥}_N`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.19). -/
noncomputable def EConst {d m : ℕ} (M : MDP d m) (R : RBClass d) (L ρlow δ : ℝ) (H : ℕ)
    (Bp : Bspace R) : ℝ :=
  2 * ‖Bp‖ / ((1 - M.γ) * ρlow * Real.sqrt H) *
    (Omega M R L + 2 * Real.sqrt (2 * Real.log (1 / δ)))

end SelfGuidedALP


