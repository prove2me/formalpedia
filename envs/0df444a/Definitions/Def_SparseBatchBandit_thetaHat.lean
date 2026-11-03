-- Prove2me | Definitions.Def_SparseBatchBandit_thetaHat
-- name    : SparseBatchBandit_thetaHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:32:46.489746+00:00
-- url     : https://prove2.me/theorems/a57f66db-cd20-4566-828f-950b250b233a
-- title:
--   LBGL estimate $\hat\theta_m$
-- statement:
--   The estimate $\hat\theta_m$ of LBGL, $0\le m\le M$, with $\hat\theta_0=0$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_estimates

namespace SparseBatchBandit

/-- The LBGL estimate `θ̂_m`, `0 ≤ m ≤ M`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16). -/
noncomputable def thetaHat {T K d : ℕ} [NeZero K] (s₀ M : ℕ) (sel : LassoSelector T s₀ M d)
    (c : Fin T → Fin K → Fin d → ℝ) (e : Fin T → ℝ) (θstar : Fin d → ℝ) (m : ℕ) : Fin d → ℝ :=
  estimates s₀ M sel c e θstar M m

end SparseBatchBandit


