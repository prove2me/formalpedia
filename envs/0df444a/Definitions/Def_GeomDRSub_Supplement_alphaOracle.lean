-- Prove2me | Definitions.Def_GeomDRSub_Supplement_alphaOracle
-- name    : GeomDRSub_Supplement_alphaOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:44:22.934952+00:00
-- url     : https://prove2.me/theorems/328b95c2-500e-4baf-a9bb-0a7147b22045
-- title:
--   The offline oracle coefficient $\alpha_{\mathrm{oracle}}(\zeta)$
-- statement:
--   $$\alpha_{\mathrm{oracle}}(\zeta)=\sup\{a\in[0,1]: a\text{ is achievable (Definition 6.1)}\}.$$
--
--   It is the best expected approximation coefficient that a randomized algorithm can guarantee, uniformly over dimensions, for nonnegative $C^1$ DR-submodular maximization over down-closed sets containing $\zeta\mathbf 1$, using polynomially many exact value–gradient queries and exact projections.
--
--   **Formalization Note** The set contains $0$ and is bounded by $1$, so the supremum is a real number in $[0,1]$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 6.1, p.33

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_OfflineAchievable

namespace GeomDRSub.Supplement

/-- **The offline oracle coefficient `αoracle(ζ)` (Definition 6.1).** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, p.33: "Define
`αoracle(ζ)` as the supremum of the achievable coefficients."

**Formalization Note.** The set of achievable `a ∈ [0,1]` contains `0` (return `0 ∈ K` without any
call) and is bounded above by `1`, so `sSup` is the supremum. -/
noncomputable def alphaOracle (ζ : ℝ) : ℝ :=
  sSup {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧ OfflineAchievable ζ a}

end GeomDRSub.Supplement


