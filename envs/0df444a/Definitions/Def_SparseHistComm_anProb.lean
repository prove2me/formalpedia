-- Prove2me | Definitions.Def_SparseHistComm_anProb
-- name    : SparseHistComm_anProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:58.647058+00:00
-- url     : https://prove2.me/theorems/d6354cd5-4757-47e5-8743-9abfbb90f3b0
-- title:
--   Analysis probability $P(E)$
-- statement:
--   The **probability** of an event $E(R, X, M)$ under the analysis prior of Section IV is $P(E) = \int_\Omega P(E \mid R = r)\, d\mu(r)$.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8, (17)

import Mathlib
import Definitions.Def_SparseHistComm_condProb
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- The **analysis probability** `P(E)` of an event `E(R, X, M)` under the prior of Section IV
(Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), p.8, (17)): the integral over the public randomness of its conditional analysis
probability. -/
noncomputable def anProb {n d : ℕ} (P : Protocol n d) (k : ℕ)
    (E : P.Ω → (Fin n → Finset (Fin d)) → (Fin n → List Bool) → Prop) : ℝ≥0∞ :=
  ∫⁻ r, condProb P k r (E r) ∂P.μ

end SparseHistComm


