-- Prove2me | Definitions.Def_KallMayerSLP_ProbConstr_RealizationTableau_measure
-- name    : KallMayerSLP_ProbConstr_RealizationTableau_measure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:02.722002+00:00
-- url     : https://prove2.me/theorems/eb039fbd-2fce-4881-b359-01d48672c0b9
-- title:
--   The distribution $\sum_i p_i\,\delta_{\hat\xi^i}$ of a realization tableau
-- statement:
--   The distribution of $\xi$ described by the realization tableau $(p_i;\hat\xi^i)_{i=1}^N$ is the discrete measure
--   $$
--   \mathbb P_\xi=\sum_{i=1}^N p_i\,\delta_{\hat\xi^i}
--   $$
--   on $\mathbb R^r$, so that $\mathbb P_\xi(A)=\sum_{i:\hat\xi^i\in A}p_i$ for every set $A$. With it, $G(x)=\sum_{i:\,x\in K_i}p_i$.
--
--   **Formalization Note** A finite sum of Dirac measures with weights `ENNReal.ofReal p_i`; since $p_i>0$ and $\sum_i p_i=1$ it is a probability measure.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.2, (2.15), p.98 (PDF 108)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_RealizationTableau

open MeasureTheory

namespace KallMayerSLP.ProbConstr

/-- The distribution `ℙ_ξ = Σ_{i=1}^N p_i · dirac(ξ̂^i)` on `ℝ^r` described by the realization
tableau (2.15).

Kall & Mayer 2005, Chapter 2, §2.2, (2.15), p.98 (PDF 108).

**Formalization Note.** A finite sum of Dirac measures with weights `ENNReal.ofReal p_i`
(`p_i > 0`, so `ofReal` is exact). With `Σ p_i = 1` it is a probability measure. -/
noncomputable def RealizationTableau.measure {N r : ℕ} (τ : RealizationTableau N r) :
    Measure (Fin r → ℝ) :=
  ∑ i, ENNReal.ofReal (τ.p i) • Measure.dirac (τ.xi i)

end KallMayerSLP.ProbConstr


