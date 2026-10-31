-- Prove2me | Definitions.Def_MissionAbort_hist
-- name    : MissionAbort_hist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:09.82731+00:00
-- url     : https://prove2.me/theorems/58d7c4f8-bb9c-4745-85b5-d459c3ca1dae
-- title:
--   The history $Y_{1:n}$
-- statement:
--   The history $Y_{1:n}(\omega)=(Y_1(\omega),\dots,Y_n(\omega))$ of the signals.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3.3, p.10

import Mathlib

namespace MissionAbort

/-- The history `Y_{1:n}(ω)` (Sun, Hu & Ye, arXiv:2505.03225v1, §3.3, p.10). Its entry `i : Fin n` is
the signal `Y_{i+1}`. -/
def hist {K : ℕ} {Ω : Type*} (Y : ℕ → Ω → Fin (K + 1)) (n : ℕ) (ω : Ω) : Fin n → Fin (K + 1) :=
  fun i => Y (i.val + 1) ω

end MissionAbort


