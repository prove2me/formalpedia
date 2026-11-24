-- Prove2me | Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_InfiniteD
-- name    : SingleMachineSched_AlphaJSched_Supplement_InfiniteD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:07:40.860471+00:00
-- url     : https://prove2.me/theorems/76e1e221-22fd-4c28-beb1-c935a6bdce98
-- title:
--   The infinite-horizon time-indexed region and its real mean-busy-time map
-- statement:
--   For jobs $j$ with integral processing requirements $p_j$ and releases $r_j$, let $y_{j\tau}$ be their fractional processing in unit slot $\tau\ge0$. Infinite-horizon feasibility requires nonnegative entries, zero entries before release, unit machine capacity in each slot, and total processing $p_j$ for each job:
--   $$y\ge0,\quad y_{j\tau}=0\ (\tau<r_j),\quad \sum_jy_{j\tau}\le1,\quad \sum_{\tau\ge0}y_{j\tau}=p_j.$$
--   The mean-busy-time map is
--   $$\mathcal M(y)_j=\frac1{p_j}\sum_{\tau\ge0}y_{j\tau}(\tau+\tfrac12).$$
--   This is the infinite-horizon analogue of the time-indexed relaxation. The existing published predicate FeasibleR supplies $P_R$, which the page describes equivalently in its $h$-form.
--
--   **Formalization Note** Feasibility uses HasSum, without a finite horizon or finite support. The real map is used only when every first-moment series is Summable. A divergent real tsum defaults to zero and does not represent the displayed moment; DISPROOF.md records the needed domain correction. Processing times are positive in the theorem, and jobs are indexed by Fin n.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, p. 174 (PDF 10), §2.3 and Theorem 2.7(ii)

import Mathlib
import Definitions.Def_SingleMachineSched_Shared_RelaxationR

namespace SingleMachineSched.AlphaJSched.Supplement

/-- Infinite-horizon time-indexed feasibility (§2.3, p. 174). Coordinates before release
are zero extensions of variables which do not occur on the page. No finite support is imposed. -/
def FeasibleDinf {n : ℕ} (p r : Fin n → ℕ) (y : Fin n → ℕ → ℝ) : Prop :=
  (∀ j τ, 0 ≤ y j τ) ∧
  (∀ j τ, τ < r j → y j τ = 0) ∧
  (∀ τ, ∑ j, y j τ ≤ 1) ∧
  (∀ j, HasSum (fun τ => y j τ) (p j : ℝ))

/-- The displayed real-valued mean-busy-time map of Theorem 2.7(ii).
Only used on vectors with summable first moments; a divergent real `tsum` is not a moment. -/
noncomputable def mMap {n : ℕ} (p : Fin n → ℕ) (y : Fin n → ℕ → ℝ) : Fin n → ℝ :=
  fun j => (1 / (p j : ℝ)) * ∑' τ : ℕ, y j τ * ((τ : ℝ) + 1 / 2)

end SingleMachineSched.AlphaJSched.Supplement


