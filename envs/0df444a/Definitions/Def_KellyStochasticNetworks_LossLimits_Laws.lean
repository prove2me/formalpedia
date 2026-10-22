-- Prove2me | Definitions.Def_KellyStochasticNetworks_LossLimits_Laws
-- name    : KellyStochasticNetworks_LossLimits_Laws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:46:57.669762+00:00
-- url     : https://prove2.me/theorems/e704c183-ba8e-4ab7-b5f8-9be58484ef33
-- title:
--   Exact occupancy laws and centered fluctuations
-- statement:
--   Let $A\in\mathbb N^{J\times R}$, let $C\in\mathbb N^J$, and let $\nu\in\mathbb R^R$. Use the published feasible states $S(C)=\{n\in\mathbb N^R:An\le C\}$ and weights $w_\nu(n)=\prod_r\nu_r^{n_r}/n_r!$. Define
--   $$Z(A,\nu,C)=\sum_{n\in S(C)}w_\nu(n),\qquad \pi_{A,\nu,C}=\sum_{n\in S(C)}\frac{w_\nu(n)}{Z(A,\nu,C)}\,\delta_n.$$
--   For network data $\nu(N),C(N)$, let $x(N)=x(A,\nu(N),C(N))$ be the continuous center defined by the blocking conditions. The fluctuation law is the image of $\pi_{A,\nu(N),C(N)}$ under
--   $$n\longmapsto u(N)=\frac{n-x(N)}{\sqrt N}.$$
--   For a multi-index $k\in\mathbb N^R$, the joint monomial is $u^k=\prod_r u_r^{k_r}$.
--
--   This definition constructs the exact law being scaled and the test functions used for mixed moments. The normalization theorem supplies positivity and summability of $Z$ under positive rates.
--
--   **Formalization Note** States range over the entire countable type $\mathbb N^R$, with mass zero outside $S(C)$. Real coefficients are converted to nonnegative extended reals for measures; on positive data no clipping occurs. At $N=0$ the scaling map is zero by Lean's division convention; limits use $N\to\infty$. At invalid signed rates or a zero partition sum the formula has Lean's totalized value and is not asserted to be a probability law.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 53 (PDF p. 61), Eq. (3.3) and §3.5.2 (printed p. 63 / PDF p. 71); DOI 10.1017/cbo9781139565363.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyStochasticNetworks_LossLimits_Optimization

open MeasureTheory

namespace KellyStochasticNetworks.LossLimits

/-- The exact partition sum in (3.3); the state space remains countable. -/
noncomputable def partition {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) : ℝ :=
  ∑' n : KellyStochasticNetworks.lossStates A C,
    KellyStochasticNetworks.lossWeight ν (n : Fin R → ℕ)

/-- The distribution in (3.3), embedded in the countable occupancy space.
Normalization is a theorem, not a field or assumption of this definition. -/
noncomputable def occupancyLaw {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) : Measure (Fin R → ℕ) :=
  Measure.sum (fun n : KellyStochasticNetworks.lossStates A C =>
    ENNReal.ofReal (KellyStochasticNetworks.lossWeight ν (n : Fin R → ℕ) / partition A ν C) •
      Measure.dirac (n : Fin R → ℕ))

/-- Push forward the actual occupancy distribution by the prescribed centering and scaling. -/
noncomputable def fluctuationLaw {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ) (N : ℕ) : Measure (Fin R → ℝ) :=
  (occupancyLaw A (νN N) (CN N)).map
    (fun n r => ((n r : ℝ) - mode A (νN N) (fun j => (CN N j : ℝ)) r) / Real.sqrt N)

/-- Joint monomials, for convergence of every mixed moment. -/
noncomputable def monomial {R : ℕ} (k : Fin R → ℕ) (u : Fin R → ℝ) : ℝ :=
  ∏ r, u r ^ k r

end KellyStochasticNetworks.LossLimits


