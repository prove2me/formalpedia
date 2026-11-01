-- Prove2me | Definitions.Def_SelfGuidedALP_Omega
-- name    : SelfGuidedALP_Omega
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:55.03017+00:00
-- url     : https://prove2.me/theorems/c7449024-932b-441a-8579-194aabb974ad
-- title:
--   The constant $\Omega$
-- statement:
--   The constant in all the paper's error bounds is
--   $$
--   \Omega:=5(D_s+1)\,L\,\sqrt{\mathbb E_\rho[\|\theta\|_2^2]},
--   $$
--   where $D_s$ is the state-space radius, $L$ the Lipschitz constant of $\varphi$, and $\mathbb E_\rho$ the expectation under the sampling distribution.
--
--   **Formalization Note** Under Assumption 2 the second moment is finite, so the integral is the true expectation.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.11

import Mathlib
import Definitions.Def_SelfGuidedALP_Ds
import Definitions.Def_SelfGuidedALP_samplingMeasure

open MeasureTheory

namespace SelfGuidedALP

/-- The constant `Ω := 5(D_s + 1) L √(E_ρ[‖θ‖₂²])`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.11).

**Formalization Note.** Under `Assumption2` the second moment is finite, so the Bochner integral is
the true expectation. -/
noncomputable def Omega {d m : ℕ} (M : MDP d m) (R : RBClass d) (L : ℝ) : ℝ :=
  5 * (Ds M + 1) * L * Real.sqrt (∫ θ, ‖θ‖ ^ 2 ∂(samplingMeasure R))

end SelfGuidedALP


