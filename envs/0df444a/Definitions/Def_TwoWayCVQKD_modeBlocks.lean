-- Prove2me | Definitions.Def_TwoWayCVQKD_modeBlocks
-- name    : TwoWayCVQKD_modeBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:37.810798+00:00
-- url     : https://prove2.me/theorems/16844dab-91da-4293-b8fb-cba57e56004e
-- title:
--   Covariance matrix written as $2\times 2$ mode blocks
-- statement:
--   The quadratures of $n$ bosonic modes are ordered as $(\hat Q_1,\hat P_1,\dots,\hat Q_n,\hat P_n)$. A real matrix indexed by quadratures of $n$ and $m$ modes is written here as an $n\times m$ array of $2\times 2$ blocks $M_{kl}$, the block $M_{kl}$ collecting the entries between mode $k$ and mode $l$.
--
--   This is the notation of the block displays of the paper, such as the EPR covariance matrix (4) and Eve's covariance matrices (17) and (48).
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (1), p.6, and the block displays (4), (17), (18), (47), (48)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (1), p.6, and the block
displays (4), (17), (18), (47), (48): a matrix over interleaved quadratures
`(Q̂₁, P̂₁, …, Q̂ₙ, P̂ₙ)` assembled from its `2 × 2` mode blocks.

**Formalization Note** `modeBlocks M (k, a) (l, b)` is entry `(a, b)` of the block `M k l`, with
`a, b = 0` for `Q̂` and `1` for `P̂`. -/
def modeBlocks {n m : ℕ} (M : Fin n → Fin m → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (QuadratureIndex n) (QuadratureIndex m) ℝ :=
  fun i j => M i.1 j.1 i.2 j.2

end TwoWayCVQKD


