-- Prove2me | Definitions.Def_BudgetedAuctionLearning_Robustness_Supplement_BudgetedGame
-- name    : BudgetedAuctionLearning_Robustness_Supplement_BudgetedGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:31:47.771205+00:00
-- url     : https://prove2.me/theorems/b229e8df-bcc2-43f1-b5cb-f763e5a0bd0b
-- title:
--   Finite budgeted game, single-pair Stackelberg value SE(ρ) and BSE value of program (2)
-- statement:
--   A **finite budgeted game** has an optimizer (leader) with actions $[n_O]$ and a learner (follower) with actions $[n_L]$, together with three real $n_O\times n_L$ matrices: the optimizer's utility $U_O$, the learner's utility $U_L$ and the optimizer's payment $P_O$. Entries are arbitrary real numbers. Mixed strategies are points $x\in\Delta([n_O])$ and $y\in\Delta([n_L])$ of the standard simplices; when the two players play $x$ and $y$ independently, the optimizer's expected utility is $x^\top U_O y$ and her expected payment is $x^\top P_O y$.
--
--   The learner has no budget. Her **best responses** to $x$ are
--   $$
--   \mathrm{BR}(x)=\operatorname*{arg\,max}_{y\in\Delta([n_L])}\ x^\top U_L y ,
--   $$
--   the set of all maximizers, ties included.
--
--   For an average budget $\rho\in\mathbb R$ of the optimizer, the **single-pair Stackelberg value** (Eq. (1)) is
--   $$
--   \mathrm{SE}(\rho)=\sup\bigl\{x^\top U_O y \;:\; x\in\Delta([n_O]),\ y\in\mathrm{BR}(x),\ x^\top P_O y\le\rho\bigr\},
--   $$
--   and the **value of the Budgeted Stackelberg Equilibrium** (Definition 2.1, program (2)) is
--   $$
--   \mathrm{BSE}(\rho)=\sup_{\nu}\ \mathbb E_{(A,B)\sim\nu}\bigl[A^\top U_O B\bigr]
--   \quad\text{s.t.}\quad \mathbb E_{(A,B)\sim\nu}\bigl[A^\top P_O B\bigr]\le\rho,\qquad B\in\mathrm{BR}(A)\ \ \forall (A,B)\in\operatorname{supp}(\nu),
--   $$
--   where $\nu$ ranges over all Borel probability measures on $\Delta([n_O])\times\Delta([n_L])$. The budget holds only in expectation over $\nu$, not for each pair separately; $\mathrm{SE}$ is program (2) restricted to a single pair.
--
--   These objects are the general-game benchmark of the paper's Section 2, used to compare a budgeted optimizer who randomizes over mixed-strategy pairs with one who commits to a single pair.
--
--   **Formalization Note** Both values are suprema in the extended reals $\overline{\mathbb R}$, so an infeasible budget gives $-\infty$ rather than a default $0$. The best response is the published `LearnVsOpt.BR` with learner cost vector $0$ and learner budget $0$, whose cost constraint reads $0\le 0$. The support is Mathlib's topological support of a measure on the product of the simplices with their subspace topologies; integrability of the two bounded continuous integrands is stated explicitly, although it always holds.
-- source:
--   Giannis Fikioris, Éva Tardos, Balasubramanian Sivan, Learning vs. Optimizing Bidders in Budgeted Auctions, STOC 2027 submission #310 (October 2026), §2 illustrative example, Eq. (1), Definition 2.1 and Eq. (2), printed pp. 5–6 (PDF pp. 6–7)

import Mathlib
import Definitions.Def_LearnVsOpt_BR

open scoped Matrix
open MeasureTheory

set_option autoImplicit false

namespace BudgetedAuctionLearning.Robustness.Supplement

/-- A finite two-player game with one optimizer budget (Fikioris, Tardos, Sivan, STOC 2027
submission #310, §2, printed pp. 5–6, PDF pp. 6–7): the optimizer (leader, rows) has `nO`
actions, the learner (follower, columns) has `nL` actions; `UO a b` is the optimizer's utility,
`UL a b` the learner's utility and `P a b` the optimizer's payment. Entries are arbitrary reals. -/
structure BudgetedGame (nO nL : ℕ) where
  /-- Optimizer utility `U_O`. -/
  UO : Matrix (Fin nO) (Fin nL) ℝ
  /-- Learner utility `U_L`. -/
  UL : Matrix (Fin nO) (Fin nL) ℝ
  /-- Optimizer payment `P_O`. -/
  P : Matrix (Fin nO) (Fin nL) ℝ

variable {nO nL : ℕ}

/-- Mixed strategies of the optimizer, `Δ([nO])`. -/
abbrev OptMixed (nO : ℕ) := stdSimplex ℝ (Fin nO)

/-- Mixed strategies of the learner, `Δ([nL])`. -/
abbrev LearnMixed (nL : ℕ) := stdSimplex ℝ (Fin nL)

/-- Expected optimizer utility `x⊤ U_O y` of the independent pair `(x, y)`. -/
def BudgetedGame.util (G : BudgetedGame nO nL) (x : Fin nO → ℝ) (y : Fin nL → ℝ) : ℝ :=
  x ⬝ᵥ (G.UO *ᵥ y)

/-- Expected optimizer payment `x⊤ P_O y` of the independent pair `(x, y)`. -/
def BudgetedGame.pay (G : BudgetedGame nO nL) (x : Fin nO → ℝ) (y : Fin nL → ℝ) : ℝ :=
  x ⬝ᵥ (G.P *ᵥ y)

/-- The learner's best responses to an optimizer mixed strategy `x`: every `y ∈ Δ([nL])`
maximizing `x⊤ U_L y'` over all `y' ∈ Δ([nL])` (ties kept). This is the published
`LearnVsOpt.BR` with learner cost vector `0` and learner budget `0`, so its cost constraint is
`0 ≤ 0` and the learner is unconstrained. -/
def BudgetedGame.BR (G : BudgetedGame nO nL) (x : Fin nO → ℝ) : Set (Fin nL → ℝ) :=
  LearnVsOpt.BR 0 (x ᵥ* G.UL) 0

/-- The feasible single pairs of Eq. (1): mixed `x, y` with `y ∈ BR(x)` and `x⊤ P_O y ≤ ρ`. -/
def BudgetedGame.SEFeasible (G : BudgetedGame nO nL) (ρ : ℝ) :
    Set ((Fin nO → ℝ) × (Fin nL → ℝ)) :=
  {p | p.1 ∈ stdSimplex ℝ (Fin nO) ∧ p.2 ∈ G.BR p.1 ∧ G.pay p.1 p.2 ≤ ρ}

/-- **Stackelberg value with budget** `SE(ρ)` (Eq. (1), printed p. 6): the supremum of
`x⊤ U_O y` over the feasible single pairs, i.e. program (2) restricted to one pair. Computed in
`EReal`, so an infeasible budget gives `⊥`. -/
noncomputable def BudgetedGame.SE (G : BudgetedGame nO nL) (ρ : ℝ) : EReal :=
  ⨆ p ∈ G.SEFeasible ρ, ((G.util p.1 p.2 : ℝ) : EReal)

/-- The feasible outer laws of program (2) (Definition 2.1, printed p. 6): Borel probability
measures `ν` on `Δ([nO]) × Δ([nL])` whose expected payment is at most `ρ` and every pair in whose
(topological) support has `B ∈ BR(A)`. The integrability clauses hold automatically for these
bounded continuous integrands; they are stated so that no Bochner-integral default value enters. -/
def BudgetedGame.BSEFeasible (G : BudgetedGame nO nL) (ρ : ℝ) :
    Set (Measure (OptMixed nO × LearnMixed nL)) :=
  {ν | IsProbabilityMeasure ν ∧
    Integrable (fun p : OptMixed nO × LearnMixed nL => G.util p.1.1 p.2.1) ν ∧
    Integrable (fun p : OptMixed nO × LearnMixed nL => G.pay p.1.1 p.2.1) ν ∧
    (∫ p, G.pay p.1.1 p.2.1 ∂ν) ≤ ρ ∧
    ∀ p ∈ ν.support, (p.2 : Fin nL → ℝ) ∈ G.BR (p.1 : Fin nO → ℝ)}

/-- **Value of the Budgeted Stackelberg Equilibrium** (program (2), printed p. 6): the supremum
of `E_{(A,B)∼ν}[A⊤ U_O B]` over the feasible outer laws `ν`, in `EReal` (`⊥` when infeasible). -/
noncomputable def BudgetedGame.BSE (G : BudgetedGame nO nL) (ρ : ℝ) : EReal :=
  ⨆ ν ∈ G.BSEFeasible ρ, ((∫ p, G.util p.1.1 p.2.1 ∂ν : ℝ) : EReal)

end BudgetedAuctionLearning.Robustness.Supplement


