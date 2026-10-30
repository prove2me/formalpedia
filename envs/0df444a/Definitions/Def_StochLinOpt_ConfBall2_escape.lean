-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_escape
-- name    : StochLinOpt_ConfBall2_escape
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:52:00.419832+00:00
-- url     : https://prove2.me/theorems/779dabf2-e57f-40b8-acee-212ded49a831
-- title:
--   Escape indicator $E_t$
-- statement:
--   Along a run, the **escape indicator** at round $t$ is
--
--   $$E_t=\mathbf 1\{Z_\tau\le\beta_\tau\ \text{for all}\ 1\le\tau\le t\}=\mathbf 1\{\mu\in B^2_\tau\ \text{for all}\ \tau\le t\}.$$
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, §5.2, p. 9

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_errZ
import Definitions.Def_StochLinOpt_ConfBall2_beta
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The escape indicator `E_t`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, §5.2, p. 9: "Et = I{Zτ ≤ βτ for all τ ≤ t} =
I{µ ∈ Bτ for all τ ≤ t}").

`escape b x ℓ μ δ t = 1` if `Z_τ ≤ β_τ` for every `1 ≤ τ ≤ t`, and `0` otherwise.

**Formalization Note** Pathwise; rounds are 1-based (`τ ∈ Finset.Icc 1 t`). -/
noncomputable def escape {n : ℕ} (b : Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (μ : Fin n → ℝ) (δ : ℝ) (t : ℕ) : ℝ := by
  classical
  exact if ∀ τ ∈ Finset.Icc 1 t, errZ b x ℓ μ τ ≤ beta n δ τ then 1 else 0

end StochLinOpt.ConfBall2


