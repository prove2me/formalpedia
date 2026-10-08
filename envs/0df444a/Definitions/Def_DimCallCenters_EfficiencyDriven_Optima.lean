-- Prove2me | Definitions.Def_DimCallCenters_EfficiencyDriven_Optima
-- name    : DimCallCenters_EfficiencyDriven_Optima
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:41:56.351864+00:00
-- url     : https://prove2.me/theorems/16ee9d89-6231-4b48-9bfe-1368c6432c7e
-- title:
--   Integer and continuous minimizers
-- statement:
--   This module names the three minimizer properties used by Section 3. For each $\lambda>0$, $N^*_\lambda$ minimizes $C(N,\lambda)$ over stable integer counts $N>\lambda/\mu$; $x^*_\lambda$ minimizes $C_\lambda(x)$ over $x>0$; and $z^*_\lambda$ minimizes a specified surrogate $\widehat F_\lambda(x)+\widehat\pi_\lambda(x)\widehat G_\lambda(x)$ over $x>0$.
--
--   $$
--   C(N^*_\lambda,\lambda)\le C(N,\lambda),\quad
--   C_\lambda(x^*_\lambda)\le C_\lambda(x),\quad
--   \widehat C_\lambda(z^*_\lambda)\le\widehat C_\lambda(x)
--   $$
--
--   for every admissible competitor in its respective domain. These predicates preserve the report's feasible sets and permit ties in the integer problem.
--
--   **Formalization Note** The minimizers are functions of $\lambda$ satisfying these properties at every positive arrival rate.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), pp. 11-12, Eqs. (7)-(9)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_cost
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate

namespace DimCallCenters.EfficiencyDriven

/-- An integer minimizer in Eq. (7), for every positive arrival rate. -/
def IsDiscreteOpt (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ) (Nstar : ℝ → ℕ) : Prop :=
  ∀ lam, 0 < lam →
    lam / M.μ < (Nstar lam : ℝ) ∧
    ∀ N : ℕ, lam / M.μ < (N : ℝ) →
      DimCallCenters.Rationalized.cost M F (Nstar lam) lam ≤ DimCallCenters.Rationalized.cost M F N lam

/-- A continuous minimizer in Eq. (8), for every positive arrival rate. -/
def IsContinuousOpt (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ lam, 0 < lam →
    0 < x lam ∧ ∀ u, 0 < u → DimCallCenters.Rationalized.Clam M F lam (x lam) ≤ DimCallCenters.Rationalized.Clam M F lam u

/-- A minimizer of the approximation in Eq. (9), for every positive rate. -/
def IsSurrogateOpt (Fh pih Gh : ℝ → ℝ → ℝ) (z : ℝ → ℝ) : Prop :=
  ∀ lam, 0 < lam →
    0 < z lam ∧
    ∀ u, 0 < u →
      DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam) ≤
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) u

end DimCallCenters.EfficiencyDriven


