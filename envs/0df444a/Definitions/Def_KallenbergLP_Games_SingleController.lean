-- Prove2me | Definitions.Def_KallenbergLP_Games_SingleController
-- name    : KallenbergLP_Games_SingleController
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:41:03.751123+00:00
-- url     : https://prove2.me/theorems/20e3a1bc-ea1b-4c97-bbb3-3d5ffecef558
-- title:
--   §6.2 — Assumptions 6.2.1–6.2.2, TMG-superharmonic vectors (Def 6.2.1), the linear programs (6.2.1)/(6.2.2), and x(π), z(π)
-- statement:
--   This file fixes the objects of Section 6.2 for a stochastic game $(E,A,B,p,r)$.
--
--   1. **Assumption 6.2.1 (contraction).** There exist a vector $\mu \gg 0$ and a scalar $\alpha \in [0,1)$ such that
--   $$\sum_j p_{iabj}\mu_j \le \alpha\,\mu_i, \qquad a \in A(i),\ b \in B(i),\ i \in E.$$
--   2. **Notation (p. 190).** For decision rules $\pi$, $\rho$: $r_{ia}(\rho) = \sum_b r_{iab}\rho_{ib}$, $p_{iaj}(\rho) = \sum_b p_{iabj}\rho_{ib}$, $r_{ib}(\pi) = \sum_a r_{iab}\pi_{ia}$.
--   3. **Definition 6.2.1.** $y \in \mathbb R^N$ is *TMG-superharmonic* if there is a stationary policy $\rho^\infty$ of player II with
--   $$y_i \ge r_{ia}(\rho) + \sum_j p_{iaj}(\rho)\,y_j, \qquad a \in A(i),\ i \in E.$$
--   4. **Assumption 6.2.2 (single controller).** The transition probabilities $p_{iabj}$, $j \in E$, do not depend on $b$; they are then written $p_{iaj}$, and $P(\pi)_{ij} = \sum_a p_{iaj}\pi_{ia}$.
--   5. **The linear program (6.2.1)**, for given numbers $\beta_j$:
--   $$\min\Big\{\sum_j \beta_j y_j \ \Big|\ \sum_j(\delta_{ij}-p_{iaj})y_j - \sum_b r_{iab}\rho_{ib} \ge 0,\ a\in A(i),\ i\in E;\ \ \sum_b\rho_{ib}=1,\ i\in E;\ \ \rho_{ib}\ge 0,\ b\in B(i),\ i \in E\Big\}.$$
--   6. **The dual linear program (6.2.2):**
--   $$\max\Big\{\sum_i z_i \ \Big|\ \sum_i\sum_a(\delta_{ij}-p_{iaj})x_{ia} = \beta_j,\ j\in E;\ \ -\sum_a r_{iab}x_{ia} + z_i \le 0,\ b\in B(i),\ i\in E;\ \ x_{ia}\ge 0,\ a\in A(i),\ i\in E\Big\}.$$
--   An optimal solution is a feasible point attaining the minimum (resp. maximum) of the objective over the feasible set.
--   7. **Policies from $x$ and frequencies from $\pi$.** $\pi_{ia} := x_{ia}/\sum_a x_{ia}$; for a stationary policy $\pi^\infty$ of player I,
--   $$x_{ia}(\pi) := [\beta^{T}(I-P(\pi))^{-1}]_i\,\pi_{ia}, \qquad z_i(\pi) := \min_{b\in B(i)} r_{ib}(\pi)\cdot\sum_a x_{ia}(\pi).$$
--
--   These are the objects of Theorems 6.2.2–6.2.4.
--
--   **Formalization Note** The LP variables $\rho_{ib}$ exist only for $b \in B(i)$ and $x_{ia}$ only for $a \in A(i)$; in Lean they are functions on all of `Fin N × β` (resp. `Fin N × α`) with the extra constraint that they vanish outside the action sets, which is the same LP. The common value $p_{iaj}$ of Assumption 6.2.2 is taken as $p_{iab_0j}$ for a fixed $b_0 \in B(i)$ (`ctrlP`); under Assumption 6.2.2 this is $p_{iabj}$ for every $b \in B(i)$. Since $\beta$ is a type variable name in Lean, the weight vector is written `β'`. $(I-P(\pi))^{-1}$ is Mathlib's matrix inverse, which is the true inverse whenever $I - P(\pi)$ is invertible (as it is under Assumption 6.2.1); $\pi_{ia} = x_{ia}/\sum_a x_{ia}$ is $0$ when the denominator is $0$, a case the theorems exclude or prove impossible.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 190 (notation r_ia(ρ), p_iaj(ρ), r_ib(π)); p. 192, Assumption 6.2.1; p. 193, Definition 6.2.1; p. 194, Assumption 6.2.2; p. 195, (6.2.1), (6.2.2); p. 198, x_ia(π), z_i(π)

import Definitions.Def_KallenbergLP_Games_StochasticGame

namespace KallenbergLP.Games

variable {N : ℕ} {α β : Type} [Fintype α] [Fintype β]

/-- Assumption 6.2.1 (p. 192): there exist a vector `μ ≫ 0` and a scalar `α ∈ [0, 1)` such that
`∑_j p_{iabj} μ_j ≤ α μ_i` for all `a ∈ A(i)`, `b ∈ B(i)`, `i ∈ E`. -/
def Assumption621 (G : Game N α β) : Prop :=
  ∃ (μ : Fin N → ℝ) (c : ℝ), (∀ i, 0 < μ i) ∧ 0 ≤ c ∧ c < 1 ∧
    ∀ i, ∀ a ∈ G.A i, ∀ b ∈ G.B i, ∑ j, G.p i a b j * μ j ≤ c * μ i

/-- `r_{ia}(ρ) := ∑_b r_{iab} ρ_{ib}` (p. 190). -/
def rho_r (G : Game N α β) (ρ : Fin N → β → ℝ) (i : Fin N) (a : α) : ℝ :=
  ∑ b : β, G.r i a b * ρ i b

/-- `p_{iaj}(ρ) := ∑_b p_{iabj} ρ_{ib}` (p. 190). -/
def rho_p (G : Game N α β) (ρ : Fin N → β → ℝ) (i : Fin N) (a : α) (j : Fin N) : ℝ :=
  ∑ b : β, G.p i a b j * ρ i b

/-- Definition 6.2.1 (p. 193): `y` is TMG-superharmonic if there is a stationary policy `ρ^∞`
for player II with `y_i ≥ r_{ia}(ρ) + ∑_j p_{iaj}(ρ) y_j` for all `a ∈ A(i)`, `i ∈ E`. -/
def TMGSuperharmonic (G : Game N α β) (y : Fin N → ℝ) : Prop :=
  ∃ ρ : Fin N → β → ℝ, IsDecisionRule2 G ρ ∧
    ∀ i, ∀ a ∈ G.A i, rho_r G ρ i a + ∑ j, rho_p G ρ i a j * y j ≤ y i

/-- Assumption 6.2.2 (p. 194): the transition probabilities `p_{iabj}`, `j ∈ E`, do not depend
on `b`, for all `i ∈ E`, `a ∈ A(i)`. -/
def Assumption622 (G : Game N α β) : Prop :=
  ∀ i, ∀ a ∈ G.A i, ∀ b ∈ G.B i, ∀ b' ∈ G.B i, ∀ j, G.p i a b j = G.p i a b' j

/-- The transition probability `p_{iaj}` of the single-controller game (p. 194):
`p_{iabj}` for a fixed `b ∈ B(i)`. Under Assumption 6.2.2 it equals `p_{iabj}` for every
`b ∈ B(i)`. -/
noncomputable def ctrlP (G : Game N α β) (i : Fin N) (a : α) (j : Fin N) : ℝ :=
  G.p i a (G.B_nonempty i).choose j

/-- Feasibility for the linear program (6.2.1) (p. 195), in the variables `y_j` (`j ∈ E`) and
`ρ_{ib}` (`b ∈ B(i)`, `i ∈ E`; `ρ i b = 0` for `b ∉ B(i)` records that these are the only
variables):
`∑_j (δ_{ij} − p_{iaj}) y_j − ∑_b r_{iab} ρ_{ib} ≥ 0` for `a ∈ A(i)`, `i ∈ E`;
`∑_b ρ_{ib} = 1` for `i ∈ E`; `ρ_{ib} ≥ 0` for `b ∈ B(i)`, `i ∈ E`. -/
def LP621Feasible (G : Game N α β) (y : Fin N → ℝ) (ρ : Fin N → β → ℝ) : Prop :=
  (∀ i, ∀ a ∈ G.A i,
      0 ≤ ∑ j, ((if i = j then 1 else 0) - ctrlP G i a j) * y j - ∑ b ∈ G.B i, G.r i a b * ρ i b) ∧
    (∀ i, ∑ b ∈ G.B i, ρ i b = 1) ∧
    (∀ i, ∀ b ∈ G.B i, 0 ≤ ρ i b) ∧
    (∀ i b, b ∉ G.B i → ρ i b = 0)

/-- `(y, ρ)` is an optimal solution of (6.2.1): feasible, and minimizing `∑_j β_j y_j` over the
feasible set. -/
def LP621Optimal (G : Game N α β) (β' : Fin N → ℝ) (y : Fin N → ℝ) (ρ : Fin N → β → ℝ) : Prop :=
  LP621Feasible G y ρ ∧
    ∀ (y' : Fin N → ℝ) (ρ' : Fin N → β → ℝ), LP621Feasible G y' ρ' →
      ∑ j, β' j * y j ≤ ∑ j, β' j * y' j

/-- Feasibility for the dual linear program (6.2.2) (p. 195), in the variables `x_{ia}`
(`a ∈ A(i)`, `i ∈ E`; `x i a = 0` for `a ∉ A(i)`) and `z_i` (`i ∈ E`):
`∑_i ∑_a (δ_{ij} − p_{iaj}) x_{ia} = β_j` for `j ∈ E`;
`−∑_a r_{iab} x_{ia} + z_i ≤ 0` for `b ∈ B(i)`, `i ∈ E`; `x_{ia} ≥ 0` for `a ∈ A(i)`, `i ∈ E`. -/
def LP622Feasible (G : Game N α β) (β' : Fin N → ℝ) (x : Fin N → α → ℝ) (z : Fin N → ℝ) :
    Prop :=
  (∀ j, ∑ i, ∑ a ∈ G.A i, ((if i = j then 1 else 0) - ctrlP G i a j) * x i a = β' j) ∧
    (∀ i, ∀ b ∈ G.B i, -(∑ a ∈ G.A i, G.r i a b * x i a) + z i ≤ 0) ∧
    (∀ i, ∀ a ∈ G.A i, 0 ≤ x i a) ∧
    (∀ i a, a ∉ G.A i → x i a = 0)

/-- `(x, z)` is an optimal solution of (6.2.2): feasible, and maximizing `∑_i z_i` over the
feasible set. -/
def LP622Optimal (G : Game N α β) (β' : Fin N → ℝ) (x : Fin N → α → ℝ) (z : Fin N → ℝ) : Prop :=
  LP622Feasible G β' x z ∧
    ∀ (x' : Fin N → α → ℝ) (z' : Fin N → ℝ), LP622Feasible G β' x' z' → ∑ i, z' i ≤ ∑ i, z i

/-- The decision rule read off a vector `x`: `π_{ia} := x_{ia} / ∑_a x_{ia}` (Theorems 6.2.3
and 6.2.4, pp. 195, 198). -/
noncomputable def piOfX (G : Game N α β) (x : Fin N → α → ℝ) (i : Fin N) (a : α) : ℝ :=
  x i a / ∑ a' ∈ G.A i, x i a'

/-- The transition matrix `P(π)` of the single-controller game: `P(π)_{ij} = ∑_a p_{iaj} π_{ia}`
(pp. 190, 194). -/
noncomputable def transMat (G : Game N α β) (π : Fin N → α → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ a ∈ G.A i, ctrlP G i a j * π i a

/-- `x_{ia}(π) := [β^T (I − P(π))^{-1}]_i · π_{ia}` (p. 198). -/
noncomputable def occ (G : Game N α β) (β' : Fin N → ℝ) (π : Fin N → α → ℝ) (i : Fin N) (a : α) :
    ℝ :=
  (Matrix.vecMul β' (1 - transMat G π)⁻¹) i * π i a

/-- `r_{ib}(π) := ∑_a r_{iab} π_{ia}` (p. 190). -/
def pi_r (G : Game N α β) (π : Fin N → α → ℝ) (i : Fin N) (b : β) : ℝ :=
  ∑ a : α, G.r i a b * π i a

/-- `z_i(π) := min_{b ∈ B(i)} r_{ib}(π) · ∑_a x_{ia}(π)` (p. 198). -/
noncomputable def zval (G : Game N α β) (β' : Fin N → ℝ) (π : Fin N → α → ℝ) (i : Fin N) : ℝ :=
  (G.B i).inf' (G.B_nonempty i)
    (fun b => pi_r G π i b * ∑ a ∈ G.A i, occ G β' π i a)

end KallenbergLP.Games


