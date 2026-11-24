-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_uniformRemainder
-- name    : GenEmpLik_Coverage_Supplement_uniformRemainder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:08:58.635492+00:00
-- url     : https://prove2.me/theorems/86be2ee8-9c30-4370-99de-3c00b2e96db1
-- title:
--   Uniform expansion remainder in (10) and Theorem 9
-- statement:
--   For a real sample $z=(z_0,\ldots,z_{n-1})$ of size $n\ge1$, let $R_{n,\rho}(z)$ be the supremum of its weighted mean over the empirical $f$-divergence ball, and let $\bar z_n$ and $s_n^2$ be its mean and variance with divisor $n$. Define
--   $$\varepsilon_{n,\rho}(z)=R_{n,\rho}(z)-\bar z_n-\sqrt{\rho s_n^2/n}.$$
--   This is the actual error in the uniform expansions, rather than a freely chosen error sequence.
--
--   **Formalization Note** The robust mean and the empirical moments are published definitions. Only positive sample sizes are used for the mathematical identity; the total expression at zero has no role in an asymptotic limit.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 7 (10); 22, Theorem 9

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar

namespace GenEmpLik.Coverage.Supplement

/-- The actual remainder in (10), p. 7 and Theorem 9, p. 22.
At n = 0 the total expression is unused; every limit ignores this index. -/
noncomputable def uniformRemainder {n : ℕ} (f : ℝ → EReal) (ρ : ℝ)
    (z : Fin n → ℝ) : ℝ :=
  GenEmpLik.Expansion.robustMean f ρ z - VarianceRegularization.Expansion.empMean z -
    Real.sqrt (ρ / (n : ℝ) * VarianceRegularization.Expansion.empVar z)

end GenEmpLik.Coverage.Supplement


