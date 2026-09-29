-- Prove2me | Definitions.Def_FoundationsML_MultiClass_GroupNormLp
-- name    : FoundationsML_MultiClass_GroupNormLp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:31:38.707129+00:00
-- url     : https://prove2.me/theorems/88a0accc-18bd-4318-9fa0-c4fb7648c33a
-- title:
--   L_{H,p} group norm of a weight-vector tuple
-- statement:
--   **p. 219, PDF p. 236.** $\|W\|_{H,p} = (\sum_{l=1}^k \|w_l\|_H^p)^{1/p}$ for
--   $W=(w_1,\dots,w_k)$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 219 (PDF p. 236)

import Mathlib

namespace FoundationsML.MultiClass

/-- The `L_{H,p}` group norm of a tuple of Hilbert-space weight vectors
`W = (w_1,…,w_k)` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 219, PDF p. 236): `‖W‖_{H,p} = (∑_{l=1}^k ‖w_l‖_H^p)^{1/p}`. -/
noncomputable def GroupNormLp {Hb : Type*} [NormedAddCommGroup Hb] {k : ℕ}
    (p : ℝ) (W : Fin k → Hb) : ℝ :=
  (∑ l, ‖W l‖ ^ p) ^ (1 / p)

end FoundationsML.MultiClass


