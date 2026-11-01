-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_arrivalProcess
-- name    : ProcessingNetworks_MArP_arrivalProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:34.01821+00:00
-- url     : https://prove2.me/theorems/7f507405-19b9-47f5-ba59-daf4b81ff2ff
-- title:
--   The Markovian arrival process $E(t)$ (Definition E.1, eq. (E.2))
-- statement:
--   The $I$-dimensional stochastic process
--   $$
--   E(t)=\sum_{k=1}^r\delta^kA_k(t),\qquad t\ge 0,
--   $$
--   is a **Markov arrival process (MArP)** with batch space $\Delta$, ARMC data $(\mathcal S,p,\Lambda)$ and arrivals data $(\beta,q)$. Its $i$-th component counts the class $i$ arrivals up to time $t$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition E.1, eq. (E.2), p.305 (PDF p.321)

import Mathlib
import Definitions.Def_ProcessingNetworks_MArP_batchCount

open MeasureTheory

namespace ProcessingNetworks.MArP

/-- The `I`-dimensional arrival process `E(t) = ∑_{k=1}^r δᵏ A_k(t)`, `t ≥ 0`, eq. (E.2), which is a
Markov arrival process (MArP) with batch space `Δ`, ARMC data `(S, p, Λ)` and arrivals data `(β, q)`
(Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2, Definition E.1, p.305,
PDF p.321). -/
noncomputable def arrivalProcess {I d r : ℕ} {D : MArPData I d r} {Ω : Type*} [MeasureSpace Ω]
    (P : MArPPrimitives D Ω) (t : ℝ) (ω : Ω) (i : Fin I) : ℕ :=
  ∑ k, D.δ k i * batchCount P k t ω

end ProcessingNetworks.MArP


