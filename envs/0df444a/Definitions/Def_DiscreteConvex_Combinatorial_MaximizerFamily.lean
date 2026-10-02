-- Prove2me | Definitions.Def_DiscreteConvex_Combinatorial_MaximizerFamily
-- name    : DiscreteConvex_Combinatorial_MaximizerFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:25:53.53837+00:00
-- url     : https://prove2.me/theorems/397a9167-a27d-418c-b509-9b10a3e2257c
-- title:
--   Maximizers of a function within a base family
-- statement:
--   Given a family $\mathcal B$ and a function $\omega$, the family of $\omega$-maximizers within $\mathcal B$ is $$\{J \in \mathcal B : \omega(J') \le \omega(J) \text{ for all } J' \in \mathcal B\}.$$
--
--   (Supporting notion for Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.72, Theorem 2.32.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.72 (supporting Theorem 2.32)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.72: "the maximizers of `ω[-p]` form the base
family of a matroid" — the family of `ω`-maximizing members of a fixed family `𝓑`, used in
the statement of Theorem 2.32 in `DiscreteConvex.Combinatorial`.
-/

namespace DiscreteConvex.Combinatorial

/-- The subfamily of `𝓑` on which `ω` attains its maximum over `𝓑`. -/
noncomputable def MaximizerFamily {V : Type*} [DecidableEq V] (𝓑 : Finset (Finset V))
    (ω : Finset V → ℝ) : Finset (Finset V) :=
  𝓑.filter (fun J => ∀ J' ∈ 𝓑, ω J' ≤ ω J)

end DiscreteConvex.Combinatorial


