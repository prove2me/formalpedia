-- Prove2me | Definitions.Def_WeightedCongestionBR_genGolden
-- name    : WeightedCongestionBR_genGolden
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:36.250851+00:00
-- url     : https://prove2.me/theorems/49d39357-a257-4c95-9647-80f3057f7002
-- title:
--   Generalized golden ratio $\Phi_{d,\rho}$
-- statement:
--   For a positive integer $d$ and $\rho\ge 1$, the generalized golden ratio $\Phi_{d,\rho}$ is the unique positive root of
--
--   $$
--   \rho\,(x+1)^d = x^{d+1}.
--   $$
--
--   For $d=\rho=1$ it is the golden ratio $\phi\approx 1.618$, and $\Phi_{d,1}=\Phi_d$ is the constant of the Price of Anarchy of weighted congestion games. The paper shows that $\Phi_{d,\rho}^{d+1}$ is exactly the Price of Anarchy of $\rho$-approximate equilibria.
--
--   **Formalization Note** Defined as the supremum of the set of positive roots; for $d\ge 1$, $\rho\ge1$ this set is a single point (supporting item `genGolden_spec`). Other arguments give an unused junk value.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §2, p.6

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The **generalized golden ratio** `Φ_{d,ρ}` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §2, p.6): for `ρ ≥ 1` and a positive integer
`d`, the unique positive root of `ρ(x + 1)^d = x^{d+1}`. For `d = ρ = 1` it is the golden ratio.

**Formalization Note** Defined as the supremum of the set of positive roots. For `d ≥ 1`, `ρ ≥ 1`
that set is a singleton (`genGolden_spec`), so the supremum is the root; for other arguments the
value is a junk value that no statement of the mission uses. -/
noncomputable def genGolden (d : ℕ) (ρ : ℝ) : ℝ :=
  sSup {x : ℝ | 0 < x ∧ ρ * (x + 1) ^ d = x ^ (d + 1)}

end WeightedCongestionBR


