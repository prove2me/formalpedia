-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market_entropy
-- name    : BauerleRiederMDP_Indifference_Market_entropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:58.623776+00:00
-- url     : https://prove2.me/theorems/e684b796-1100-4e7e-a6ba-159bb91bb126
-- title:
--   The entropy objective $\mathbb E_{Q'}[\log dQ'/d\mathbb P]$
-- statement:
--   For a measure $Q'$ on $\Omega$, this is the objective of Remark 4.9.3,
--   $$
--   \mathbb E_{Q'}\Bigl[\log\frac{dQ'}{d\mathbb P}\Bigr],
--   $$
--   the relative entropy of $Q'$ with respect to $\mathbb P$.
--
--   **Formalization Note** It is used for $\mathbb P$-equivalent $Q'$, whose density is positive and finite at each of the four points, where every function is integrable.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 4.9.3, p.137

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market

open MeasureTheory

namespace BauerleRiederMDP.Indifference

namespace Market

/-- The objective `𝔼_{Q'}[log dQ'/dℙ]` of Remark 4.9.3 (Bäuerle & Rieder, Markov Decision Processes
with Applications to Finance (2011), Remark 4.9.3, p.137, PDF 151).

**Formalization Note.** The objective is used for `ℙ`-equivalent `Q'`, for which the density is
positive and finite at every point of the four-point space, where every function is integrable. -/
noncomputable def entropy (M : Market) (Q' : Measure (Fin 4)) : ℝ :=
  ∫ ω, Real.log (Q'.rnDeriv M.P ω).toReal ∂Q'

end Market

end BauerleRiederMDP.Indifference


