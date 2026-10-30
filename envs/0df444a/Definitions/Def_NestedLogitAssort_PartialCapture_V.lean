-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_V
-- name    : NestedLogitAssort_PartialCapture_V
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:38:12.362347+00:00
-- url     : https://prove2.me/theorems/ac69f19e-eaf7-40a1-9632-a07374c597bb
-- title:
--   Total preference weight $V_i(S_i)$
-- statement:
--   For a nest $i$ and an assortment $S\subseteq N$, the total preference weight of the options available in nest $i$ is
--
--   $$
--   V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}.
--   $$
--
--   It is the denominator of the within-nest choice probabilities and, raised to the power $\gamma_i$, the attractiveness of nest $i$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, p. 7

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_Instance

namespace NestedLogitAssort.PartialCapture

/-- **Total preference weight `V_i(S_i)` of an assortment in a nest.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 1, p. 7 (unnumbered):
`V_i(S_i) = v_{i0} + ∑_{j ∈ S_i} v_{ij}`. -/
def V {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (S : Finset (Fin n)) : ℝ :=
  I.w0 i + ∑ j ∈ S, I.v i j

end NestedLogitAssort.PartialCapture


