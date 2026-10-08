-- Prove2me | Definitions.Def_KallenbergLP_SemiMarkov_Discounted
-- name    : KallenbergLP_SemiMarkov_Discounted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:53:35.969054+00:00
-- url     : https://prove2.me/theorems/63d8fe91-d125-42e2-9bb5-9397c008ea46
-- title:
--   Discounted semi-Markov rewards, policies, value and superharmonicity
-- statement:
--   Fix a rate $\lambda>0$. The conditional holding-time transform is $L_{iaj}(\lambda)=\int_0^\infty e^{-\lambda t}\,dF_{iaj}(t)$; Assumption 7.2.1 requires $L_{iaj}(\lambda)<1$ for each available triple $(i,a,j)$. The expected one-epoch reward and discounted transition entry are
--
--   $$
--   r^*_{ia}=\sum_jp_{iaj}\int_0^\infty\left(r_{ia}+s_{ia}\int_0^t e^{-\lambda u}\,du\right)dF_{iaj}(t),\qquad p^*_{iaj}=p_{iaj}L_{iaj}(\lambda).
--   $$
--
--   A randomized policy selects an action using the previous states and chosen actions and the current state, without observing previous sojourn times. Its discounted value is the limit of finite-horizon expected returns from equation (7.2.1). The value vector $v^\lambda$ is the coordinatewise supremum over all such policies. A vector $w$ is DRD-superharmonic when $w_i\geq r^*_{ia}+\sum_jp^*_{iaj}w_j$ for every available $(i,a)$.
--
--   These definitions also specify the discounted state-action occupancy used in Lemma 7.2.1, pure stationary policies, and the dual linear program (7.2.11). They provide the shared interface for the chapter's three numbered results.
--
--   **Formalization Note** The recursive finite-horizon expectation integrates the original epoch reward, including its holding time. The occupation identity is not used to define policy value. Variables for unavailable actions in the dual are ignored, so they do not affect feasibility or objective value.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 212–217, Assumption 7.2.1, equations (7.2.1), (7.2.10), (7.2.11), Definitions 7.2.1–7.2.3, https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Model

namespace KallenbergLP.SemiMarkov

open MeasureTheory Filter

variable {S U : Type*} [Fintype S] [Nonempty S] [Fintype U] [DecidableEq S] [DecidableEq U]

/-- The integral of the continuous discount factor during a holding time. -/
noncomputable def holdingDiscount (rate t : ℝ) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) t, Real.exp (-(rate * u))

/-- The Laplace–Stieltjes transform of the conditional sojourn-time law. -/
noncomputable def laplace (M : Model S U) (rate : ℝ) (i : S) (a : U) (j : S) : ℝ :=
  ∫ t, Real.exp (-(rate * t)) ∂M.F i a j

/-- Section 7.2 fixes a strictly positive discount rate and Assumption 7.2.1. -/
structure Discounted (S U : Type*) [Fintype S] [Nonempty S] [Fintype U] where
  model : Model S U
  rate : ℝ
  rate_pos : 0 < rate
  laplace_lt_one : ∀ i a j, a ∈ model.actions i → laplace model rate i a j < 1

/-- The immediate lump reward plus the discounted reward rate in one epoch. -/
noncomputable def epochReturn (M : Discounted S U) (i : S) (a : U) (t : ℝ) : ℝ :=
  M.model.r i a + M.model.s i a * holdingDiscount M.rate t

/-- The book's `r*`, averaged over the next state and its conditional holding time. -/
noncomputable def rStar (M : Discounted S U) (i : S) (a : U) : ℝ :=
  ∑ j, M.model.p i a j * ∫ t, epochReturn M i a t ∂M.model.F i a j

/-- The book's `p*_{iaj}`. -/
noncomputable def pStar (M : Discounted S U) (i : S) (a : U) (j : S) : ℝ :=
  M.model.p i a j * laplace M.model M.rate i a j

/-- A randomized decision rule reads only previous state–action pairs and the current state.
In particular it does not observe previous holding times. -/
structure Policy (M : Discounted S U) where
  choose : List (S × U) → S → U → ℝ
  choose_nonneg : ∀ h i a, a ∈ M.model.actions i → 0 ≤ choose h i a
  choose_sum : ∀ h i, ∑ a ∈ M.model.actions i, choose h i a = 1

/-- Expected discounted reward through `n` decision epochs, conditional on the current
state and the observed discrete history. This recursively integrates the original epoch
reward against each conditional holding-time law; it does not use `rStar`. -/
noncomputable def finiteReward (M : Discounted S U) (R : Policy M) :
    ℕ → List (S × U) → S → ℝ
  | 0, _, _ => 0
  | n + 1, h, i =>
    ∑ a ∈ M.model.actions i, R.choose h i a *
      ∑ j, M.model.p i a j *
        ∫ t, (epochReturn M i a t + Real.exp (-(M.rate * t)) *
          finiteReward M R n (h ++ [(i, a)]) j) ∂M.model.F i a j

/-- Equation (7.2.1), computed as the limit of finite-horizon conditional expectations.
Assumption 7.2.1 makes this limit finite for every policy. -/
noncomputable def policyValue (M : Discounted S U) (R : Policy M) (i : S) : ℝ :=
  limUnder atTop (fun n => finiteReward M R n [] i)

/-- Definition 7.2.1: coordinatewise supremum over every history-dependent policy. -/
noncomputable def value (M : Discounted S U) (i : S) : ℝ :=
  sSup (Set.range (fun R : Policy M => policyValue M R i))

/-- Definition 7.2.2. -/
def Superharmonic (M : Discounted S U) (v : S → ℝ) : Prop :=
  ∀ i, ∀ a ∈ M.model.actions i,
    rStar M i a + ∑ j, pStar M i a j * v j ≤ v i

/-- Expected discounted occupancy of a state-action pair at the `n`-th future epoch.
Epoch `n=0` is the book's epoch 1. -/
noncomputable def discountedVisit (M : Discounted S U) (R : Policy M) :
    ℕ → List (S × U) → S → S → U → ℝ
  | 0, h, i, j, a => if i = j then R.choose h i a else 0
  | n + 1, h, i, j, a =>
    ∑ b ∈ M.model.actions i, R.choose h i b *
      ∑ k, pStar M i b k * discountedVisit M R n (h ++ [(i, b)]) k j a

/-- The pure stationary policy associated with a feasible action choice. -/
noncomputable def purePolicy (M : Discounted S U) (f : S → U)
    (hf : ∀ i, f i ∈ M.model.actions i) : Policy M where
  choose := fun _ i a => if a = f i then 1 else 0
  choose_nonneg := by intros; split <;> norm_num
  choose_sum := by
    intro h i
    classical
    simp [hf i]

/-- The dual feasibility constraints (7.2.11). Variables for unavailable actions are
ignored in every sum and condition, so the function representation is extensionally the
same as one variable for each available state-action pair. -/
def DualFeasible (M : Discounted S U) (β : S → ℝ) (x : S → U → ℝ) : Prop :=
  (∀ i, ∀ a ∈ M.model.actions i, 0 ≤ x i a) ∧
  (∀ j, ∑ i, ∑ a ∈ M.model.actions i,
    ((if i = j then (1 : ℝ) else 0) - pStar M i a j) * x i a = β j)

/-- The objective of (7.2.11). -/
noncomputable def dualObjective (M : Discounted S U) (x : S → U → ℝ) : ℝ :=
  ∑ i, ∑ a ∈ M.model.actions i, rStar M i a * x i a

/-- Optimality in the dual maximization program (7.2.11). -/
def DualOptimal (M : Discounted S U) (β : S → ℝ) (x : S → U → ℝ) : Prop :=
  DualFeasible M β x ∧
    ∀ y, DualFeasible M β y → dualObjective M y ≤ dualObjective M x

end KallenbergLP.SemiMarkov


