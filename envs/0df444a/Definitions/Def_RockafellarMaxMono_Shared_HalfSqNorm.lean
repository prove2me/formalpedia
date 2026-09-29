-- Prove2me | Definitions.Def_RockafellarMaxMono_Shared_HalfSqNorm
-- name    : RockafellarMaxMono_Shared_HalfSqNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:01:17.079339+00:00
-- url     : https://prove2.me/theorems/6464b1e6-6d7c-4cf8-be07-6bf7d6cd74b6
-- title:
--   The function $j(x) = \tfrac12\|x\|^2$
-- statement:
--   Let $V$ be a real normed space. The function $j : V \to \mathbb{R}$ is
--
--   $$
--   j(x) = \tfrac{1}{2}\|x\|^2 ,
--   $$
--
--   regarded as a finite-valued function into $(-\infty,+\infty]$. It is continuous and convex, and in Rockafellar's proof of Theorem A it is added to $f$ so that the conjugate $(f+j)^*$ becomes finite and continuous on $E^*$.
--
--   It serves chunk 01-maximal-monotone (p. 213, §3, proof of Theorem A) and chunk 02-cyclic-characterization (p. 213, §3, reused in the proof of Theorem B): in both, $j$ is added to $f$ so that the conjugate $(f+j)^*$ becomes finite and continuous on $E^*$.
--
--   **Formalization Note** The Lean name is `halfSqNorm`; its values are real numbers cast to `EReal`. The sum $f + j$ is written pointwise as `fun y => f y + halfSqNorm y`.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 213, §3, definition of j

import Mathlib

namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 213: the continuous convex function `j(x) = (1/2)‖x‖²`,
regarded as a (finite-valued) function `V → (−∞, +∞]`. -/
noncomputable def halfSqNorm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) :
    EReal :=
  ((‖x‖ ^ 2 / 2 : ℝ) : EReal)

end RockafellarMaxMono.Shared


