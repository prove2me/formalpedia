-- Prove2me | Definitions.Def_NestedLogitAssort_General_V
-- name    : NestedLogitAssort_General_V
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:38:34.172828+00:00
-- url     : https://prove2.me/theorems/f80127ae-6a07-4cf4-acd9-33b1f3a988e5
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
import Definitions.Def_NestedLogitAssort_General_Instance

namespace NestedLogitAssort.General

/-- **Total preference weight `V_i(S_i)` of an assortment in a nest.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 1, p. 7 (unnumbered):
`V_i(S_i) = v_{i0} + ∑_{j ∈ S_i} v_{ij}`. -/
def V {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (S : Finset (Fin n)) : ℝ :=
  I.w0 i + ∑ j ∈ S, I.v i j

end NestedLogitAssort.General


