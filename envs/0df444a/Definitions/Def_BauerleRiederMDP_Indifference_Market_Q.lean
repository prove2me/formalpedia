-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market_Q
-- name    : BauerleRiederMDP_Indifference_Market_Q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:52.077007+00:00
-- url     : https://prove2.me/theorems/25ab27ff-933a-4ca7-a3fa-70dcc080e329
-- title:
--   The measure $\mathbb Q$ of Remark 4.9.3
-- statement:
--   With the risk neutral probability $q:=(1-d)/(u-d)$, the measure $\mathbb Q$ on $\Omega$ is given by
--   $$
--   \mathbb Q(\{\omega_k\})=q_k:=q\,\frac{p_k}{p_1+p_2}\quad(k=1,2),\qquad
--   \mathbb Q(\{\omega_k\})=q_k:=(1-q)\,\frac{p_k}{p_3+p_4}\quad(k=3,4).
--   $$
--   Under $\mathbb Q$ the traded asset has the risk neutral law, while the conditional law of the non-traded asset given the traded one stays that of $\mathbb P$. Remark 4.9.3 shows that it is the minimal entropy martingale measure.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, p.136 (q) and Remark 4.9.3, p.137

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market

open MeasureTheory

namespace BauerleRiederMDP.Indifference

namespace Market

/-- The risk neutral probability `q := (1 - d)/(u - d)` (Bäuerle & Rieder, Markov Decision Processes
with Applications to Finance (2011), §4.9, p.136, PDF 150). -/
noncomputable def q (M : Market) : ℝ := (1 - M.d) / (M.u - M.d)

/-- The weights `q_k` of Remark 4.9.3 (p.137, PDF 151): `q_k := q p_k/(p₁ + p₂)` for `k = 1, 2` and
`q_k := (1 - q) p_k/(p₃ + p₄)` for `k = 3, 4`. -/
noncomputable def qWeight (M : Market) : Fin 4 → ℝ :=
  ![M.q * (M.p 0 / (M.p 0 + M.p 1)), M.q * (M.p 1 / (M.p 0 + M.p 1)),
    (1 - M.q) * (M.p 2 / (M.p 2 + M.p 3)), (1 - M.q) * (M.p 3 / (M.p 2 + M.p 3))]

/-- The measure `ℚ` on `Ω` of Remark 4.9.3 (p.137, PDF 151), with `ℚ({ω_k}) = q_k`. -/
noncomputable def Q (M : Market) : Measure (Fin 4) :=
  ∑ k, ENNReal.ofReal (M.qWeight k) • Measure.dirac k

end Market

end BauerleRiederMDP.Indifference


