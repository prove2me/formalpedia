-- Prove2me | Definitions.Def_SparseBatchBandit_action
-- name    : SparseBatchBandit_action
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:33:48.286487+00:00
-- url     : https://prove2.me/theorems/96fb1ec2-8fae-4dd9-ab2f-d1a7114ae8b4
-- title:
--   LBGL action $a_t$
-- statement:
--   The action $a_t$ taken by LBGL at round $t$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_thetaHat

namespace SparseBatchBandit

/-- The action `a_t` of LBGL at round `t`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16). -/
noncomputable def action {T K d : ℕ} [NeZero K] (s₀ M : ℕ) (sel : LassoSelector T s₀ M d)
    (c : Fin T → Fin K → Fin d → ℝ) (e : Fin T → ℝ) (θstar : Fin d → ℝ) (t : Fin T) : Fin K :=
  playedArm s₀ M c (thetaHat s₀ M sel c e θstar) t

end SparseBatchBandit


