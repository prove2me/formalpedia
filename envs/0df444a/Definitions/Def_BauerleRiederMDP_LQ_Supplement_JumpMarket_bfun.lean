-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_bfun
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_bfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:12:01.930102+00:00
-- url     : https://prove2.me/theorems/401c4a51-8335-5658-b851-a6c5f5b0e1b6
-- title:
--   The bounding function $b(t, x) = e^{\gamma (T-t)}(1 + x)$
-- statement:
--   **The bounding function $b(t, x) = e^{\gamma (T-t)}(1 + x)$** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Proposition 9.3.2 a), p.284, PDF 294), $\gamma  \ge  0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket

namespace BauerleRiederMDP.LQ.Supplement

/-- **The bounding function `b(t, x) = e^{γ(T−t)}(1 + x)`** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), Proposition 9.3.2 a), p.284, PDF 294), `γ ≥ 0`. -/
noncomputable def JumpMarket.bfun {d : ℕ} (Mk : JumpMarket d) (γ : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (γ * (Mk.T - p.1)) * (1 + p.2)

end BauerleRiederMDP.LQ.Supplement


