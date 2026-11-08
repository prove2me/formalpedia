-- Prove2me | Definitions.Def_TightClock_clockWelfare
-- name    : TightClock_clockWelfare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:04:31.279433+00:00
-- url     : https://prove2.me/theorems/e7548ed8-acd2-4d5b-8017-7756463125c6
-- title:
--   Welfare $\mathrm{SW}_\pi(v;\omega)$ of a clock run
-- statement:
--   For a clock with fixed seed and a profile $v$, the welfare is
--
--   $$\mathrm{SW}_\pi(v)=\sum_{i\in W_\pi(v)}v_i,$$
--
--   where $W_\pi(v)$ is the terminal winner set. A run that never stops has welfare $0$, as on p.14: a non-terminating deviation receives no service and makes no payment.
--
--   **Formalization Note** Payments are not modeled, since the paper evaluates clocks only through welfare.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.14 (PDF p.17)

import Mathlib
import Definitions.Def_TightClock_StopsWith

set_option autoImplicit false

namespace TightClock

open Classical in
/-- The welfare `SW_π(v; ω) = ∑_{i ∈ W_π(v; ω)} vᵢ` of a deterministic clock (the seed is fixed), and `0`
if the run never stops: "A non-terminating deviation receives no service and makes no payment."
Afshinmehr et al., manuscript (STOC 2027 submission), §3, p.14 (PDF 17).

**Formalization Note** Payments are not modeled: "We evaluate clocks only through welfare" (p.14). -/
noncomputable def clockWelfare {n : ℕ} (σ : Strategy n) (v : Fin n → ℝ) : ℝ :=
  if h : ∃ S, StopsWith σ v S then ∑ i ∈ h.choose, v i else 0

end TightClock


