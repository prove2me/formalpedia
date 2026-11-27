-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Eset
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_Eset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:11:34.460107+00:00
-- url     : https://prove2.me/theorems/1a03fb2e-83c3-5fe8-8982-8c1d3bc8303e
-- title:
--   The state space $E = [0, T] \times  \mathbb R _+$
-- statement:
--   **The state space $E = [0, T] \times  \mathbb R _+$** of the discrete-time model of §9.3 (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.282, PDF 292), as a subset of $\mathbb R  \times  \mathbb R $; it contains $x = 0$ and $t = T$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket

namespace BauerleRiederMDP.LQ.Supplement

/-- **The state space `E = [0, T] × ℝ_+`** of the discrete-time model of §9.3 (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), p.282, PDF 292), as a subset of
`ℝ × ℝ`; it contains `x = 0` and `t = T`. -/
def JumpMarket.Eset {d : ℕ} (Mk : JumpMarket d) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc 0 Mk.T ∧ 0 ≤ p.2}

end BauerleRiederMDP.LQ.Supplement


