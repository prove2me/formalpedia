-- Prove2me | Definitions.Def_NestedLogitAssort_DeltaGrid_V
-- name    : NestedLogitAssort_DeltaGrid_V
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:01:09.564338+00:00
-- url     : https://prove2.me/theorems/f34555ad-8937-4464-a5fd-e1c50c8a616f
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
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 1, p. 7

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Instance

namespace NestedLogitAssort.DeltaGrid

/-- **Total preference weight `V_i(S_i)` of an assortment in a nest.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 1, p. 7 (unnumbered):
`V_i(S_i) = v_{i0} + ∑_{j ∈ S_i} v_{ij}`. -/
def V {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (S : Finset (Fin n)) : ℝ :=
  I.w0 i + ∑ j ∈ S, I.v i j

end NestedLogitAssort.DeltaGrid


