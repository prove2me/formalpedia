-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_triggeredCount
-- name    : ProcessingNetworks_MArP_triggeredCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:49.176514+00:00
-- url     : https://prove2.me/theorems/93384e8a-60b2-4fff-a9d7-6fce2168e40c
-- title:
--   The triggered batch count $J_k(s,\tilde s,t)$
-- statement:
--   The number of batch arrivals with configuration $\delta^k$ that are triggered by ARMC transitions from $s$ to $\tilde s$ up to time $t$ is
--   $$
--   J_k(s,\tilde s,t)=\sum_{n=1}^{J(s,\tilde s,t)}1_{\{\zeta(n,s,\tilde s)=k\}} .
--   $$
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Section E.1, p.305 (PDF p.321)

import Mathlib
import Definitions.Def_ProcessingNetworks_MArP_MArPPrimitives
import Definitions.Def_ProcessingNetworks_MArP_jumpCount

open MeasureTheory

namespace ProcessingNetworks.MArP

/-- The number `J_k(s, s̃, t) = ∑_{n=1}^{J(s, s̃, t)} 1{ζ(n, s, s̃) = k}` of batch arrivals with
configuration `δᵏ` triggered by ARMC transitions from `s` to `s̃` up to time `t` (Dai & Harrison,
Processing Networks, pre-publication draft 2020-4-2, Section E.1, p.305, PDF p.321).

**Formalization Note.** The sum runs over `n = 0, …, J - 1` because `ζ n` is the book's
`ζ(n + 1, ·, ·)`. The jump times are `σ_n = jumpTime (exitRate Λ) embedded clock n`. -/
noncomputable def triggeredCount {I d r : ℕ} {D : MArPData I d r} {Ω : Type*} [MeasureSpace Ω]
    (P : MArPPrimitives D Ω) (k : Fin r) (s s' : Fin d) (t : ℝ) (ω : Ω) : ℕ :=
  ∑ n ∈ Finset.range
      (jumpCount P.embedded
        (ProcessingNetworks.Stability.jumpTime (exitRate D.Λ) P.embedded P.clock) s s' t ω),
    if P.ζ n s s' ω = k.succ then 1 else 0

end ProcessingNetworks.MArP


