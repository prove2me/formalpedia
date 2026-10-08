-- Prove2me | Definitions.Def_KellyLossNetworks_RevisedDual_Problem
-- name    : KellyLossNetworks_RevisedDual_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:53:33.220027+00:00
-- url     : https://prove2.me/theorems/8739378d-624a-4472-9e0b-1ae590329296
-- title:
--   The utilization function U (3.4), the revised dual problem (3.5) and its stationarity conditions (3.6) (§3.1)
-- statement:
--   Consider a loss network with $J$ links and a finite set $\mathcal R$ of routes: link $j$ has $C_j$ circuits, a call on route $r$ uses $A_{jr}\in\mathbb Z_+$ circuits of link $j$, and calls on route $r$ arrive as a Poisson stream of rate $\nu_r$. Let $E(\nu,C)$ be Erlang's formula,
--   $$E(\nu,C)=\frac{\nu^C}{C!}\Big[\sum_{n=0}^{C}\frac{\nu^n}{n!}\Big]^{-1}.$$
--
--   1. The **utilization function** $U(y,C)$ is defined by the implicit relation
--   $$U\big(-\log(1-E(\nu,C)),\,C\big)=\nu\,\big(1-E(\nu,C)\big),\qquad \nu\ge 0. \tag{3.4}$$
--   That is, $U(y,C)=\nu(1-E(\nu,C))$ for the $\nu\ge0$ with $-\log(1-E(\nu,C))=y$. It is the mean number of busy circuits on a single Erlang link whose blocking probability is $1-e^{-y}$.
--   2. The **revised dual problem** is
--   $$\text{minimize}\quad \sum_r \nu_r \exp\Big(-\sum_j y_jA_{jr}\Big)+\sum_j\int_0^{y_j}U(z,C_j)\,dz\qquad\text{subject to } y\ge0. \tag{3.5}$$
--   A vector $y$ is an **optimum** of (3.5) if $y\ge0$ and its objective value is at most that of every $z\ge0$.
--   3. The **stationarity conditions** of (3.5) are
--   $$\sum_r A_{jr}\,\nu_r\exp\Big(-\sum_i y_iA_{ir}\Big)=U(y_j,C_j),\qquad j=1,\dots,J. \tag{3.6}$$
--
--   The revised dual differs from the dual problem (2.3) only in its last term: $\sum_j y_jC_j$ is replaced by $\sum_j\int_0^{y_j}U(z,C_j)\,dz$. Its optimum is the bridge between the dual problem and the Erlang fixed point (Theorem 3.7).
--
--   **Formalization Note** Erlang's formula is the published `KellyStochasticNetworks.erlang`. Routes are indexed by $\{0,\dots,R-1\}$ and the incidence matrix has natural-number entries. $U$ is defined by choice: $U(y,C)=\nu(1-E(\nu,C))$ for some $\nu\ge0$ with $-\log(1-E(\nu,C))=y$, and $0$ if there is none. For $C\ge1$ and $y\ge0$ exactly one such $\nu$ exists, so this is the paper's function; that it satisfies (3.4) is a theorem of the mission, not part of the definition. Values of $U$ at $y<0$ or $C=0$ are placeholders and every statement keeps away from them. The integral is the interval integral from $0$ to $y_j$.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 338, §3.1, (3.4), (3.5), (3.6); Erlang's formula (1.1), p. 319

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace KellyLossNetworks.RevisedDual

open Classical in
/-- **The utilization function** `U(y, C)` of Kelly, *Loss networks*, defined by the implicit
relation (3.4)
`U(−log(1 − E(ν, C)), C) = ν(1 − E(ν, C))`,
where `E(ν, C)` is Erlang's formula (1.1) (the published `KellyStochasticNetworks.erlang`).

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, (3.4).

**Formalization Note.** `U y C` is `ν * (1 - E(ν, C))` for a (chosen) `ν ≥ 0` with
`-Real.log (1 - E(ν, C)) = y`, and `0` when no such `ν` exists. For `C ≥ 1` and `y ≥ 0` the
paper observes that exactly one such `ν` exists, so the choice is immaterial and `U` is the
paper's function on `ℝ₊ × {C ≥ 1}`; that (3.4) holds is a theorem of the mission
(`utilization_wellDefined`), not part of this definition. Outside `y ≥ 0, C ≥ 1` the value is
a junk value (at `C = 0`, `E(ν, 0) = 1` and `Real.log 0 = 0`), and no statement of the mission
uses `U` there. -/
noncomputable def U (y : ℝ) (C : ℕ) : ℝ :=
  if h : ∃ ν : ℝ, 0 ≤ ν ∧ -Real.log (1 - KellyStochasticNetworks.erlang ν C) = y then
    h.choose * (1 - KellyStochasticNetworks.erlang h.choose C)
  else 0

/-- **The objective of the revised dual problem** (3.5):
`Σ_r ν_r exp(−Σ_j y_j A_jr) + Σ_j ∫_0^{y_j} U(z, C_j) dz`.
The first term is the first term of the dual objective (2.3) (the published
`KellyStochasticNetworks.dualObjective`); the second replaces `Σ_j y_j C_j`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, (3.5).

**Formalization Note.** Routes are `Fin R`, links `Fin J`; the incidence matrix `A` has
natural-number entries (the general case `A_jr ∈ ℤ₊` of §1.2). The integral is the interval
integral `∫ z in 0..y_j`; on the feasible set `y ≥ 0` of (3.5) it only evaluates `U` on
`[0, y_j]`. -/
noncomputable def revisedDualObjective {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (y : Fin J → ℝ) : ℝ :=
  (∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ))) + ∑ j, ∫ z in (0 : ℝ)..(y j), U z (C j)

/-- `y` is an **optimum of the revised dual problem** (3.5): `y ≥ 0` and the objective at `y` is
at most its value at every `z ≥ 0`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, (3.5) ("Minimize … subject to y ≥ 0"). -/
def IsRevisedDualOptimum {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (y : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧
    ∀ z : Fin J → ℝ, (∀ j, 0 ≤ z j) → revisedDualObjective A ν C y ≤ revisedDualObjective A ν C z

/-- **The stationarity conditions** (3.6):
`Σ_r A_jr ν_r exp(−Σ_i y_i A_ir) = U(y_j, C_j)` for `j = 1, …, J`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, (3.6). -/
def StationarityConditions {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (y : Fin J → ℝ) : Prop :=
  ∀ j, (∑ r, (A j r : ℝ) * ν r * Real.exp (-∑ i, y i * (A i r : ℝ))) = U (y j) (C j)

end KellyLossNetworks.RevisedDual


