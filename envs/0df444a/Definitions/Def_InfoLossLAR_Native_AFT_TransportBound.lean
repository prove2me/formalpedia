-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_TransportBound
-- name    : InfoLossLAR_Native_AFT_TransportBound
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:19:33.247456+00:00
-- url     : https://prove2.me/theorems/c2fb42a5-83fa-4d64-8cf1-43bed1cc2456
-- title:
--   Event probabilities and eventwise statistical distance
-- statement:
--   For probability laws $p,q$ on a finite set $X$, write $p(S)=\sum_{x\in S}p(x)$. The eventwise distance bound with parameter $\varepsilon$ is $$\forall S\subseteq X,\qquad |p(S)-q(S)|\le\varepsilon.$$ This is the statistical distance convention used for the sampler output.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/TransportBound.lean; migrated source SHA256 2116aa591b31ab4071e60b608afe8d63b694b4b30361374aff3ae4a709aef24d; byte-range skeleton from Lean AST, with original retained definitions and proofs.

import Definitions.Def_InfoLossLAR_Native_AFT_FiniteProbability
import Mathlib


/-!
# Eventwise total variation bounds and the endpoint/carry reduction

On finite spaces, `TVBound p q error` is precisely the assertion that the
maximum absolute difference on an event is at most `error`, the convention
used in reference V7. No probability estimate is assumed by the definition.
-/

namespace AFT
namespace FiniteDist

open scoped BigOperators
open scoped Classical

variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]

/-- Probability of an event. -/
noncomputable def event (p : FiniteDist α) (s : Finset α) : ℝ :=
  ∑ a ∈ s, p.weight a

/-- Statistical distance at most `error`, in its eventwise definition. -/
def TVBound (p q : FiniteDist α) (error : ℝ) : Prop :=
  ∀ s : Finset α, |p.event s - q.event s| ≤ error





















end FiniteDist
end AFT


