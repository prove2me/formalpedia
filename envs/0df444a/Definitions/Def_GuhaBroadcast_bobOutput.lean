-- Prove2me | Definitions.Def_GuhaBroadcast_bobOutput
-- name    : GuhaBroadcast_bobOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:28.590448+00:00
-- url     : https://prove2.me/theorems/ed5a3e22-b6a2-4358-9705-990aebcb91f8
-- title:
--   Bob's received state $\hat\rho^{B^n}_{m,k}$
-- statement:
--   Alice sends the codeword $x^n(m,k)$, an arbitrary (possibly entangled) state of $n$ modes, through $n$ uses of the beam splitter
--
--   $$
--   \hat b=\sqrt\eta\,\hat a+\sqrt{1-\eta}\,\hat e,\qquad \hat c=\sqrt{1-\eta}\,\hat a-\sqrt\eta\,\hat e,
--   $$
--
--   with the environment modes $\hat e$ in vacuum ((6)–(7)). **Bob's received state** $\hat\rho^{B^n}_{m,k}=\operatorname{Tr}_{C^n}\hat\rho^{B^nC^n}_{m,k}$ is the partial trace of the joint output over Charlie's modes.
--
--   **Formalization Note** The channel is the published `broadcast n eta` and the partial trace is `bobMarginal`, from the bundle `QAlgorithms.Papers.Independent.Next46.P32`.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section II, p.1; Section III, eqs. (6)-(7), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section II, p.1, and Section III, Eqs. (6)–(7), p.2 (PDF pages; the paper prints no page
numbers): Bob's received n-use state `ρ̂_{m,k}^{Bⁿ} = Tr_{Cⁿ} ρ̂_{m,k}^{BⁿCⁿ}` when Alice sends the
codeword `x^n(m,k)` of the code `C` through n uses of the beam splitter `b̂ = √η â + √(1−η) ê`,
`ĉ = √(1−η) â − √η ê` with the environment `ê` in vacuum.

**Formalization Note.** The channel is the published `broadcast n eta` (memoryless n-fold beam splitter
with vacuum environment) and the partial trace over Charlie is `bobMarginal`, both from
`QAlgorithms.Papers.Independent.Next46.P32`. The codeword is the encoder's arbitrary n-mode state, so
entangled inputs are allowed. -/
noncomputable def bobOutput {n MB MC : ℕ} {O : Type} [Fintype O] (eta : ℝ)
    (C : BroadcastCode n MB MC O) (m : Fin MB) (k : Fin MC) : FockKernel n :=
  bobMarginal (broadcast n eta (C.encoder m k).coefficients)

end GuhaBroadcast


