-- Prove2me | Definitions.Def_KellyLossNetworks_Primal_Problem
-- name    : KellyLossNetworks_Primal_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:51:23.246516+00:00
-- url     : https://prove2.me/theorems/8629ce53-9403-4b9b-bb15-54c01cf272d4
-- title:
--   The primal problem, complementary slackness, and conditions on B
-- statement:
--   For a network with links $j$, routes $r$, incidence numbers $A_{jr}\in\mathbb N$, offered traffic $\nu_r$, and capacities $C_j$, the **primal objective** and its feasible set are
--
--   $$F(x)=\sum_r(x_r\log\nu_r-x_r\log x_r+x_r),\qquad x_r\ge0,\quad \sum_r A_{jr}x_r\le C_j.$$
--
--   The **Lagrangian** adds multipliers $y_j$ and nonnegative slacks $z_j$ to the capacity constraints. Its maximizing route flow is $\bar x_r(y)=\nu_r\exp(-\sum_jy_jA_{jr})$. Complementary feasibility means $y\ge0$, $A\bar x(y)\le C$, and $\sum_jy_j(C_j-(A\bar x(y))_j)=0$.
--
--   The **conditions on $B$** require $0\le B_j<1$ and $\sum_r A_{jr}\nu_r\prod_i(1-B_i)^{A_{ir}}=C_j$ when $B_j>0$, or at most $C_j$ when $B_j=0$. The change of variables is $B_j=1-e^{-y_j}$, with inverse $y_j=-\log(1-B_j)$. A dual optimum minimizes the published dual objective over $y\ge0$.
--
--   These definitions give a common model for the primal, dual, and blocking formulations.
--
--   **Formalization Note** The value $x\log x$ at $x=0$ is its continuous extension, zero. Links and routes are finite, and the general nonnegative integer matrix $A$ is used.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp. 327–328, §2.1, (2.1)–(2.7)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyLossNetworks.Primal

/-- Kelly, *Loss networks* (1991), p. 327, (2.1). The continuous primal objective.
Formalization Note: `x * Real.log x` is zero at `x = 0`, its continuous extension. -/
noncomputable def primalObjective {R : ℕ} (ν x : Fin R → ℝ) : ℝ :=
  ∑ r, (x r * Real.log (ν r) - x r * Real.log (x r) + x r)

/-- Kelly, *Loss networks* (1991), p. 327, (2.1). Nonnegative route flows respecting link capacities. -/
def primalFeasible {J R : ℕ} (A : Fin J → Fin R → ℕ) (C : Fin J → ℕ) :
    Set (Fin R → ℝ) :=
  {x | (∀ r, 0 ≤ x r) ∧ ∀ j, (∑ r, (A j r : ℝ) * x r) ≤ (C j : ℝ)}

/-- Kelly, *Loss networks* (1991), p. 327, the Lagrangian following (2.1). -/
noncomputable def lagrangian {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (x : Fin R → ℝ)
    (z y : Fin J → ℝ) : ℝ :=
  primalObjective ν x + ∑ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * x r - z j)

/-- Kelly, *Loss networks* (1991), p. 328, (2.2). -/
noncomputable def primalPoint {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (y : Fin J → ℝ) : Fin R → ℝ :=
  fun r => ν r * Real.exp (-(∑ j, y j * (A j r : ℝ)))

/-- Kelly, *Loss networks* (1991), p. 328, (2.4)–(2.5). -/
def complementary {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (y : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧
  (∀ j, (∑ r, (A j r : ℝ) * primalPoint A ν y r) ≤ (C j : ℝ)) ∧
  (∑ j, y j * ((C j : ℝ) - ∑ r, (A j r : ℝ) * primalPoint A ν y r)) = 0

/-- Kelly, *Loss networks* (1991), p. 328, (2.6). -/
noncomputable def blockingFromDual {J : ℕ} (y : Fin J → ℝ) : Fin J → ℝ :=
  fun j => 1 - Real.exp (-y j)

/-- Kelly, *Loss networks* (1991), p. 328, the inverse of (2.6) on `[0,1)`. -/
noncomputable def dualFromBlocking {J : ℕ} (B : Fin J → ℝ) : Fin J → ℝ :=
  fun j => -Real.log (1 - B j)

/-- Kelly, *Loss networks* (1991), p. 328, (2.7). The two cases are implications
because `B j ∈ [0,1)` makes them exhaustive. -/
def ConditionsOnB {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (B : Fin J → ℝ) : Prop :=
  (∀ j, B j ∈ Set.Ico (0 : ℝ) 1) ∧
  ∀ j, (0 < B j →
    (∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - B i) ^ (A i r)) = (C j : ℝ)) ∧
    (B j = 0 →
    (∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - B i) ^ (A i r)) ≤ (C j : ℝ))

/-- Kelly, *Loss networks* (1991), p. 328, (2.3), using the published dual objective. -/
def IsDualOpt {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (y : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧
  ∀ z : Fin J → ℝ, (∀ j, 0 ≤ z j) →
    KellyStochasticNetworks.dualObjective A ν C y ≤
      KellyStochasticNetworks.dualObjective A ν C z

end KellyLossNetworks.Primal


