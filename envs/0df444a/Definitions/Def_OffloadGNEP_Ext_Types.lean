-- Prove2me | Definitions.Def_OffloadGNEP_Ext_Types
-- name    : OffloadGNEP_Ext_Types
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:25.81153+00:00
-- url     : https://prove2.me/theorems/d71f94f5-a810-48db-a8a6-e2a43722b487
-- title:
--   Offloading tiers, model parameters, and Assumption A
-- statement:
--   The model has three processing tiers: the mobile device, a shared cloudlet, and a remote cloud. For each of the $N$ users it records traffic ratios $\alpha_u,\beta_u,\gamma_u,\delta_u$, local and transmission power coefficients, and a power budget. It also records the number $n$ of cloudlet servers, the offloadable fraction $\chi$, and the utilization cap $U_{\max}$.
--
--   Assumption A requires $U_{\max},\alpha_u,\delta_u\in(0,1)$ for every user. The standing conditions are $n>0$ and $0<\chi\le1$. The pairing of two strategy profiles is the ordinary coordinatewise Euclidean pairing over all users and tiers.
--
--   These objects fix the data and the scalar product used by the model and its variational inequalities. The paper makes no corresponding sign assumption on $\beta_u$ or $\gamma_u$ in Section 5.
--
--   **Formalization Note** Users are indexed by `Fin N`, with zero-based indices; this also permits $N=0$. The server count is a natural number and the pairing is written as a finite sum.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), pp. 7–11, tier set, parameters, Assumption A

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

namespace OffloadGNEP.Ext

/-- Parameters of the offloading model, in the notation of p. 10. -/
structure Params (N : ℕ) where
  alpha : Fin N → ℝ
  beta : Fin N → ℝ
  gamma : Fin N → ℝ
  delta : Fin N → ℝ
  Pm : Fin N → ℝ
  Pt : Fin N → ℝ
  Pmax : Fin N → ℝ
  n : ℕ
  chi : ℝ
  Umax : ℝ

/-- Assumption A, p. 11. -/
def Params.AssumptionA {N : ℕ} (P : Params N) : Prop :=
  0 < P.Umax ∧ P.Umax < 1 ∧
    ∀ u, 0 < P.alpha u ∧ P.alpha u < 1 ∧ 0 < P.delta u ∧ P.delta u < 1

/-- The standing positive server count and offloadable fraction (pp. 7, 9). -/
def Params.Standing {N : ℕ} (P : Params N) : Prop :=
  0 < P.n ∧ 0 < P.chi ∧ P.chi ≤ 1

end OffloadGNEP.Ext


