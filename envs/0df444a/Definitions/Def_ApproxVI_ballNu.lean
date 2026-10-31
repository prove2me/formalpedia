-- Prove2me | Definitions.Def_ApproxVI_ballNu
-- name    : ApproxVI_ballNu
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:08.886358+00:00
-- url     : https://prove2.me/theorems/fa2edfd2-ebc0-4ebd-96d1-463fcb943573
-- title:
--   The closed weighted ball $B^\epsilon=\{y : \|y\|_\nu\le\epsilon\}$
-- statement:
--   For weights $\nu$ and a radius $\epsilon$, the closed ball of the weighted max-norm centred at the origin is
--
--   $$
--   B^\epsilon=\{y\in\mathbb R^d:\ \|y\|_\nu\le\epsilon\}.
--   $$
--
--   It models the set of admissible approximation errors once the errors are bounded by $\epsilon$; the perturbed Bellman operator adds it to $Tx$.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Lemma 1, p.14

import Mathlib
import Definitions.Def_ApproxVI_wNorm

namespace ApproxVI

/-- The closed `‖·‖_ν`-ball `B^ε := {y | ‖y‖_ν ≤ ε}` of Ramaswamy & Bhatnagar, *Analyzing
Approximate Value Iteration Algorithms*, arXiv:1709.04673v5, Lemma 1, p.14. -/
def ballNu {d : ℕ} (ν : Fin d → ℝ) (ε : ℝ) : Set (Fin d → ℝ) :=
  {y | wNorm ν y ≤ ε}

end ApproxVI


