-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_signedMean
-- name    : ProcessingNetworks_MArP_signedMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:20.050665+00:00
-- url     : https://prove2.me/theorems/740baa03-275c-4c17-b718-33accd261b7e
-- title:
--   The extended-real mean $\pi(f)=\pi(f^+)-\pi(f^-)$ (Section C.6)
-- statement:
--   For a distribution $\pi$ on a countable set and a function $f:\mathcal S\to\mathbb R$, with $f^+=\max(f,0)$ and $f^-=\max(-f,0)$, put
--   $$
--   \pi(f)=\pi(f^+)-\pi(f^-)\in[-\infty,\infty].
--   $$
--
--   This is the limit in the strong law of large numbers for a discrete-time Markov chain.
--
--   **Formalization Note** The book defines $\pi(f)$ only when at least one of $\pi(f^+)$, $\pi(f^-)$ is finite. The value is an element of `EReal`, in which $\top-\top=\bot$, so every use carries that finiteness hypothesis.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Section C.6, p.280 (PDF p.296)

import Mathlib
import Definitions.Def_ProcessingNetworks_MArP_nonnegMean

namespace ProcessingNetworks.MArP

/-- The `π`-mean of a general function, `π(f) = π(f⁺) - π(f⁻)` (Dai & Harrison, Processing Networks,
pre-publication draft 2020-4-2, p.280, PDF p.296), an element of `[-∞, ∞]`.

**Formalization Note.** The book defines `π(f)` only when at least one of `π(f⁺)`, `π(f⁻)` is finite.
`EReal` subtraction gives `⊤ - ⊤ = ⊥`, so every use of this definition must carry that hypothesis, as
Theorem C.21 does. -/
noncomputable def signedMean {S : Type*} (π : PMF S) (f : S → ℝ) : EReal :=
  (nonnegMean π f : EReal) - (nonnegMean π (fun i => -f i) : EReal)

end ProcessingNetworks.MArP


