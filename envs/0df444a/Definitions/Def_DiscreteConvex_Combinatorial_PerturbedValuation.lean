-- Prove2me | Definitions.Def_DiscreteConvex_Combinatorial_PerturbedValuation
-- name    : DiscreteConvex_Combinatorial_PerturbedValuation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:25:51.851664+00:00
-- url     : https://prove2.me/theorems/243a45b4-95c7-4898-ac33-b67a08b6304d
-- title:
--   Linear perturbation of a valuation (Eq. 2.76)
-- statement:
--   The perturbation of $\omega$ by a linear functional $p : V \to \mathbb R$ is $$\omega[-p](J) = \omega(J) - \sum_{j \in J} p(j),$$ Eq. (2.76). This is the same perturbation notation the book reuses throughout for M-convex functions in later chapters.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.72, Eq. (2.76).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.72, Eq. (2.76)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.72, Eq. (2.76): the perturbation
`ω[-p](J) = ω(J) - Σ_{j∈J} p(j)` used throughout the book (recurring for M-convex functions
in later chapters), specialised here to the valuated-matroid setting of
`DiscreteConvex.Combinatorial`.
-/

namespace DiscreteConvex.Combinatorial

/-- The perturbation `ω[-p]` of `ω` by a linear functional `p : V → ℝ` (Eq. (2.76)):
`ω[-p](J) = ω(J) - Σ_{j ∈ J} p(j)`. -/
def PerturbedValuation {V : Type*} (ω : Finset V → ℝ) (p : V → ℝ) : Finset V → ℝ :=
  fun J => ω J - ∑ v ∈ J, p v

end DiscreteConvex.Combinatorial


