-- Prove2me | Definitions.Def_GibbsCongestion_potential
-- name    : GibbsCongestion_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:10.439436+00:00
-- url     : https://prove2.me/theorems/80ae1a25-5d25-4f83-a4d8-b736b3bb023e
-- title:
--   Rosenthal's potential $\Phi(s)$
-- statement:
--   For a congestion game with cost functions $c_e$ on the resources $e\in E$, **Rosenthal's potential** of a strategy profile $s$ is
--   $$\Phi(s)=\sum_{e\in E}\sum_{k=1}^{\ell_e(s)}c_e(k),$$
--   where $\ell_e(s)$ is the load of $e$. It is an exact potential of the game: a unilateral deviation changes $\Phi$ by the deviator's change in cost. It defines the Gibbs distribution and the logit dynamics.
--
--   **Formalization Note** Costs are real valued ($c:E\to\mathbb N\to\mathbb R$); the value $c_e(0)$ never enters. Resources on no strategy have load $0$ and contribute $0$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, display (3), p.7

import Mathlib
import Definitions.Def_GibbsCongestion_resourceLoad

namespace GibbsCongestion

/-- **Rosenthal's potential** (3): `Φ(s) = ∑_{e ∈ E} ∑_{k=1}^{ℓ_e(s)} c_e(k)`
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, display (3), p.7).

**Formalization Note** The cost of resource `e` at load `k` is `c e k : ℝ` (the paper's
`c_e : ℤ≥0 → ℚ`); `c e 0` never enters. The outer sum runs over all resources; a resource on no
strategy has load `0` and contributes `0`. -/
noncomputable def potential {E : Type*} [Fintype E] [DecidableEq E] {P : Finset (Finset E)} {n : ℕ} (c : E → ℕ → ℝ)
    (s : Fin n → P) : ℝ :=
  ∑ e, ∑ k ∈ Finset.Icc 1 (resourceLoad s e), c e k

end GibbsCongestion


