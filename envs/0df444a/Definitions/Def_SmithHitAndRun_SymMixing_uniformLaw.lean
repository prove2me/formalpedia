-- Prove2me | Definitions.Def_SmithHitAndRun_SymMixing_uniformLaw
-- name    : SmithHitAndRun_SymMixing_uniformLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:58:47.251168+00:00
-- url     : https://prove2.me/theorems/0ae0fe9a-bcf7-4275-91e8-974840c582b9
-- title:
--   Uniform law associated with finite nonzero content
-- statement:
--   Let $S$ be a measurable state space with finite, nonzero content measure $V$. The **uniform law** on $S$ is the probability measure
--   $$
--   \lambda(A)=\frac{V(A)}{V(S)}
--   $$
--   for every measurable $A\subseteq S$. This is Smith's normalization of the $k$-dimensional content of a region; it is also meaningful for counting content when $k=0$.
--
--   This common law is the stationary candidate and the limit in the chapter's convergence theorems. **Formalization Note** The type itself is $S$, so $V(S)$ is `V Set.univ`; finiteness and nonzero total content are assumptions of the theorems that use the definition.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1300, Lemma 1 (definition of λ)

import Mathlib.Probability.Kernel.Invariance

open MeasureTheory

namespace SmithHitAndRun.SymMixing

/-- The uniform law associated with finite nonzero content `V` on the state space. -/
noncomputable def uniformLaw {α : Type*} [MeasurableSpace α] (V : Measure α) : Measure α :=
  (V Set.univ)⁻¹ • V

end SmithHitAndRun.SymMixing


