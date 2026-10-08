-- Prove2me | Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn
-- name    : MonotoneCompStatics_Monotonicity_argmaxOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:36.210732+00:00
-- url     : https://prove2.me/theorems/328a9be1-15af-4c8f-a2fc-a6c355a374d2
-- title:
--   Maximizers over a constraint set
-- statement:
--   Let $X$ be a choice set, let $S\subseteq X$, and let $g:X\to\mathbb R$ be an objective. The set of maximizers of $g$ over $S$ is
--
--   $$\operatorname{argmax}_{x\in S}g(x)=\{x\in S: g(y)\le g(x)\text{ for every }y\in S\}.$$
--
--   This set can be empty, including when the maximum is not attained. It is the optimization correspondence used throughout the monotonicity theorem.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 162 (PDF 7), proof of Theorem 4; p. 163 (PDF 8), paragraph after Corollary 2

import Mathlib

namespace MonotoneCompStatics.Monotonicity

def argmaxOn {X : Type*} (g : X → ℝ) (S : Set X) : Set X :=
  {x | x ∈ S ∧ ∀ y ∈ S, g y ≤ g x}

end MonotoneCompStatics.Monotonicity


