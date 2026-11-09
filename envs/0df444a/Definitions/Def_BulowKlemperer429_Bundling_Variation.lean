-- Prove2me | Definitions.Def_BulowKlemperer429_Bundling_Variation
-- name    : BulowKlemperer429_Bundling_Variation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:22.702631+00:00
-- url     : https://prove2.me/theorems/112de942-9264-4b9a-8daa-a34745e49dc1
-- title:
--   Independent-copy variation and the right derivative
-- statement:
--   For a real observable $h$ on a probability space with law $\mu$, write
--   $$G_\mu(h)=\tfrac12\int |h(x)-h(y)|\,d(\mu\otimes\mu)(x,y).$$
--   The two arguments are independent copies. For a function $g$ on the nonnegative half-line, write $g'_+(x)$ for the derivative from strictly larger arguments, including at $x=0$.
--
--   These notions support the scalar and product comparisons. The variation definition uses a real Bochner integral, and is used only when $h$ is integrable. Right derivatives use a real extension of $g$, but depend only on values strictly to the right of $x$. Their existence is a conclusion under the shape assumptions in the relevant lemmas, never a new hypothesis.
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 7, §3.1, G; Lemmas 3.1–3.2 p. 8 (PDF p. 9) (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
open MeasureTheory
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

/-- Half the expected absolute difference of independent copies. Used with integrable h. -/
noncomputable def variation {α : Type} [MeasurableSpace α]
    (μ : Measure α) (h : α → ℝ) : ℝ :=
  (∫ z, |h z.1 - h z.2| ∂(μ.prod μ)) / 2

/-- Right derivative on the half-line, including its boundary point zero. -/
noncomputable def rightDeriv (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin g (Set.Ioi x) x

end BulowKlemperer429.Bundling


