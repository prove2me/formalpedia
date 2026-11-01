-- Prove2me | Definitions.Def_WiretapFeedback_eveMarginal
-- name    : WiretapFeedback_eveMarginal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:55.899527+00:00
-- url     : https://prove2.me/theorems/483e5210-25aa-43cc-a637-b33b1aba36af
-- title:
--   Eavesdropper's marginal channel $W_2(z|x)$
-- statement:
--   For a wiretap channel $W:\mathcal X\to\mathcal Y\times\mathcal Z$, the eavesdropper's marginal channel is
--   $$
--   W_2(z|x)=\sum_y W(y,z|x).
--   $$
--   It is the factor $W_2$ in the decomposition $W(y,z|x)=W_2(z|x)W_1(y|z,x)$ used in the proof of Theorem 1.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, proof of Theorem 1, p.3

import Mathlib
import Definitions.Def_WildeQIT_Channel

namespace WiretapFeedback

/-- The eavesdropper's marginal channel `W₂(z|x) = Σ_y W(y, z|x)` of a wiretap channel
`W : X → Y × Z` (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, proof of Theorem 1, p. 3, where
`W(y, z|x) = W₂(z|x) W₁(y|z, x)`). -/
noncomputable def eveMarginal {X Y Z : Type} [Fintype Y] [Fintype Z]
    (W : WildeQIT.Channel X (Y × Z)) : WildeQIT.Channel X Z :=
  fun x => (W x).snd

end WiretapFeedback


