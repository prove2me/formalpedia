-- Prove2me | Definitions.Def_MyersonBargaining_NashSolution_Bargaining
-- name    : MyersonBargaining_NashSolution_Bargaining
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:40.866296+00:00
-- url     : https://prove2.me/theorems/30ceb96b-8bc9-485e-8c6c-97c1e6eb1712
-- title:
--   Strict dominance, incentive-efficiency, conflict payoffs, individual rationality, and the weighted Nash product
-- statement:
--   An interim vector $x$ **strictly dominates** $y$ if $y_{i,a_i}<x_{i,a_i}$ for every player $i$ and type $a_i$. A mechanism is **incentive-efficient** if it is a Bayesian incentive-compatible choice mechanism and no other such mechanism produces an interim vector that strictly dominates its vector.
--
--   Fix a conflict outcome $c^*\in C$. The constant mechanism selects $c^*$ with probability one, regardless of the reports. Its conflict payoff vector, the **individually rational** part of the incentive-feasible set, and the **generalized Nash product** are
--
--   $$
--   t_{i,a_i}=\sum_\alpha P_i(\alpha\mid a_i)U_i(c^*,\alpha),\qquad
--   F^*_+=\{x\in F^*:x_{i,a_i}\ge t_{i,a_i}\ \forall i,a_i\},
--   $$
--
--   $$
--   N(x)=\prod_i\prod_{a_i\in A_i}(x_{i,a_i}-t_{i,a_i})^{R_i(a_i)}.
--   $$
--
--   A vector $x$ is an **incentive-feasible bargaining solution** if $x\in F^*_+$ and $N(y)\le N(x)$ for every $y\in F^*_+$. These definitions identify the optimization problem whose unique solution is asserted by Theorem 3.
--
--   **Formalization Note** The product is compared only on $F^*_+$, where its bases are nonnegative. The conflict payoff is defined by equation (16), independently of the constant mechanism; their equality is a separate milestone. Strict dominance (11) is on vectors: strict inequality at every coordinate of $\sum_i A_i$, which is nonempty, so no vector dominates itself.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), pp. 65, 67–69, Eqs. (11), (16)–(18), Section 4

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Model

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Equation (11): every player type gets a strictly larger interim payoff. -/
def StrictlyDominates (x y : (Σ i, A i) → ℝ) : Prop :=
  ∀ k, y k < x k

/-- Section 4: incentive-compatible and not strictly dominated by another such mechanism. -/
def IsIncentiveEfficient (G : Problem ι A C)
    (π : C → (∀ i, A i) → ℝ) : Prop :=
  IsChoiceMechanism π ∧ IsBIC G π ∧
    ¬ ∃ π' : C → (∀ i, A i) → ℝ,
      IsChoiceMechanism π' ∧ IsBIC G π' ∧ StrictlyDominates (V G π') (V G π)

/-- The mechanism which always selects the conflict choice `cstar`. -/
def constMech (cstar : C) : C → (∀ i, A i) → ℝ :=
  fun c _ => if c = cstar then 1 else 0

/-- Equation (16): interim utility at the conflict outcome. -/
noncomputable def conflictPayoff (G : Problem ι A C) (cstar : C) :
    (Σ i, A i) → ℝ :=
  fun k => ∑ α, cond G.P k.1 α k.2 * G.U k.1 cstar α

/-- Equation (17): incentive-feasible vectors at least as good as conflict for every type. -/
def FPlus (G : Problem ι A C) (cstar : C) : Set ((Σ i, A i) → ℝ) :=
  FStar G ∩ {y | ∀ k, conflictPayoff G cstar k ≤ y k}

/-- Equation (18): the generalized Nash product, weighted by marginal type probabilities. -/
noncomputable def nashProduct (G : Problem ι A C) (cstar : C)
    (x : (Σ i, A i) → ℝ) : ℝ :=
  ∏ i, ∏ a : A i,
    (x ⟨i, a⟩ - conflictPayoff G cstar ⟨i, a⟩) ^ (marginal G.P i a)

/-- Section 5: a maximizer of (18) over the set (17). -/
def IsBargainingSolution (G : Problem ι A C) (cstar : C)
    (x : (Σ i, A i) → ℝ) : Prop :=
  x ∈ FPlus G cstar ∧
    ∀ y ∈ FPlus G cstar, nashProduct G cstar y ≤ nashProduct G cstar x

end MyersonBargaining.NashSolution


