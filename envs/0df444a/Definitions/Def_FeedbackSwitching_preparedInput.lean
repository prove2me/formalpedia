-- Prove2me | Definitions.Def_FeedbackSwitching_preparedInput
-- name    : FeedbackSwitching_preparedInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:06.002214+00:00
-- url     : https://prove2.me/theorems/d4335d33-187b-4c62-9138-202dd4db9e36
-- title:
--   Inputs of one block of Algorithm 1 prepared by PrepareBlock with the parameters (28)
-- statement:
--   For weights $w$, an LP solution $((Q_s)_s,\rho)$ with anchor $w$, a tournament and $\kappa=2^{-m}$, the block of Proposition 3 is run with the sampling law $p$, refresh law $x$ and estimation matrices $\Psi_s$ of PrepareBlock$(w,\kappa)$, the parameters $M,\eta$ of Eq. (28), and the tournament scores (21) for each $P_\tau$.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Proposition 3, p.25 (PDF p.27); Algorithm 3; Eq. (28)

import Mathlib
import Definitions.Def_FeedbackSwitching_blockRun
import Definitions.Def_FeedbackSwitching_tScore
import Definitions.Def_FeedbackSwitching_prepareBlock
import Definitions.Def_FeedbackSwitching_eq28Params

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

**Inputs of one block of Algorithm 1** (Proposition 3, p.25 = PDF p.27): the inputs of one iteration of Algorithm 1 for the weights `w`, prepared by PrepareBlock from
the LP solution `z` with the base rate `κ = 2^{−m}` and the parameters (28) of the horizon `T`;
scores are the tournament scores (21) of `A` for `P_τ`. -/
noncomputable def preparedInput {K : ℕ} (T m : ℕ) (A : Fin K → Fin K → Prop) (w : Fin K → ℝ)
    (z : (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ)) : BlockInput K :=
  { p := prepP (baseRate m) w z.2, x := prepX (baseRate m) w z.2,
    Ψ := prepareBlock (baseRate m) w z, m := m, M := eq28M K T, η := eq28Eta K T m,
    d := fun τ _ ℓ s j =>
      tScore A (holdingP (prepP (baseRate m) w z.2) (prepX (baseRate m) w z.2) τ) ℓ s j }

end FeedbackSwitching


