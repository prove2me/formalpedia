-- Prove2me | Definitions.Def_TightClock_clockValue
-- name    : TightClock_clockValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:12:18.746033+00:00
-- url     : https://prove2.me/theorems/fc7d6690-5313-4d2e-8e45-73d2ae2e265b
-- title:
--   Expected welfare of a randomized clock
-- statement:
--   The expected welfare of a randomized clock $\pi$ under the prior $D$ is
--
--   $$\mathbb E_{X\sim D,\omega}[\mathrm{SW}_\pi(X;\omega)],$$
--
--   with the seed independent of the values.
--
--   **Formalization Note** The seed is integrated at each fixed support profile, and then the finite prior is summed. The integrand is measurable by the definition of a randomized clock, and bounded by the first best.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.14 (PDF p.17)

import Mathlib
import Definitions.Def_TightClock_RandomizedClock
import Definitions.Def_TightClock_priorExpect

set_option autoImplicit false

open MeasureTheory

namespace TightClock

/-- The expected welfare `E_{X∼D, ω}[SW_π(X; ω)]` of a randomized clock, under the i.i.d. prior `D`.
Afshinmehr et al., manuscript (STOC 2027 submission), §3, p.14 (PDF 17).

**Formalization Note** Integrability holds for support profiles: the `measurable` field of
`RandomizedClock` plus the bound by the first best. -/
noncomputable def clockValue {n : ℕ} {F : Finset (Finset (Fin n))} (π : RandomizedClock F)
    (D : FinitePrior) : ℝ :=
  priorExpect D (fun v => ∫ ω, clockWelfare (π.σ ω) v ∂π.P)

end TightClock


