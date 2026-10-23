-- Prove2me | Definitions.Def_FiniteMemQL_Convergence_Model
-- name    : FiniteMemQL_Convergence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:27.055574+00:00
-- url     : https://prove2.me/theorems/6cd11fba-514e-4a05-a278-e71aaf0dfcf2
-- title:
--   §2, (2.4)–(2.6) — the partially observed model (T, O, c, β), the Bayes filter and the optimal value J*_β of the belief MDP
-- statement:
--   This module fixes the partially observed controlled Markov model of §2 and the belief MDP built from it.
--
--   The hidden state lives in a Borel space $\mathbb X$, observations in a finite set $\mathbb Y$ and actions in a finite set $\mathbb U$. The model consists of
--
--   1. a transition kernel $\mathcal T(dx'\mid x,u)$,
--   2. an observation channel $O(dy\mid x)$,
--   3. a measurable stage cost $c:\mathbb X\times\mathbb U\to\mathbb R$, which is bounded,
--   4. a discount factor $\beta\in(0,1)$.
--
--   For a (possibly unnormalised) state law $\mu$ the module defines the Bayes correction by an observation $y$, $\mu(dx)\,O(\{y\}\mid x)$, the prediction through an action $u$, $\int\mathcal T(\cdot\mid x,u)\,\mu(dx)$, and the normalisation $\mu/\mu(\mathbb X)$. Together they give the filter update of (2.4),
--   $$
--   F(z,u,y)=\frac{O(\{y\}\mid\cdot)\,\bigl(\textstyle\int\mathcal T(\cdot\mid x,u)\,z(dx)\bigr)}{P(y\mid z,u)},
--   $$
--   where $P(y\mid z,u)$ is the probability of the next observation $y$. The belief-MDP cost is $\tilde c(z,u)=\int c(x,u)\,z(dx)$ (2.6), and the optimal discounted value $J^*_\beta$ of the belief MDP is the limit of value iteration from $0$ for the operator
--   $$
--   (\mathbb T V)(z)=\min_{u\in\mathbb U}\Bigl(\tilde c(z,u)+\beta\sum_{y\in\mathbb Y}P(y\mid z,u)\,V\bigl(F(z,u,y)\bigr)\Bigr).
--   $$
--   Finally $\|c\|_\infty=\sup_{x,u}|c(x,u)|$.
--
--   These objects are the common substrate of every statement of the mission.
--
--   **Formalization Note** Boundedness of $c$ is not stated in the paper but is implicit in every bound through $\|c\|_\infty$; it is a field of the structure. Normalising a zero measure gives the zero measure. $J^*_\beta$ is defined as the value-iteration limit (`limUnder`); the fixed-point equations are stated as theorems.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, pp. 5–7, §2, (2.1)–(2.6)

import Mathlib

namespace FiniteMemQL.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The partially observed controlled Markov model of §2, p. 5 (arXiv:2103.12158v4): a hidden
state space `X` (a Borel set; encoded by `StandardBorelSpace X` in the statements), a finite
observation space `Y`, a finite action space `U`, a transition kernel `T(dx' | x, u)`, an
observation channel `O(dy | x)`, a stage-wise cost `c : X × U → ℝ` and a discount factor
`β ∈ (0, 1)`. The cost is measurable in `x` for each action and bounded: the paper never states
boundedness, but every bound it proves is in terms of `‖c‖∞`. -/
structure POMDP (X Y U : Type*) [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U] where
  /-- transition kernel `T(· | x, u)` -/
  T : Kernel (X × U) X
  /-- observation channel `O(· | x)` -/
  O : Kernel X Y
  /-- stage-wise cost `c(x, u)` -/
  c : X → U → ℝ
  /-- discount factor -/
  β : ℝ
  isMarkov_T : IsMarkovKernel T
  isMarkov_O : IsMarkovKernel O
  c_meas : ∀ u, Measurable (fun x => c x u)
  c_bdd : ∃ B : ℝ, ∀ x u, |c x u| ≤ B
  β_pos : 0 < β
  β_lt_one : β < 1

attribute [instance] POMDP.isMarkov_T POMDP.isMarkov_O

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

/-- Bayes correction of an unnormalised state law `μ` by the observation `y`:
`μ(dx) O({y} | x)`. -/
noncomputable def correct (M : POMDP X Y U) (μ : Measure X) (y : Y) : Measure X :=
  μ.withDensity (fun x => M.O x {y})

/-- Prediction of a state law `μ` through the action `u`: `∫ T(· | x, u) μ(dx)`. -/
noncomputable def predict (M : POMDP X Y U) (μ : Measure X) (u : U) : Measure X :=
  μ.bind (fun x => M.T (x, u))

/-- Normalisation `μ / μ(X)`. It returns the zero measure when `μ(X) = 0` (and when
`μ(X) = ∞`). -/
noncomputable def normalize (μ : Measure X) : Measure X := (μ Set.univ)⁻¹ • μ

/-- The belief-MDP filter update `F(z, u, y)` of (2.4): predict through `u`, correct by `y`,
normalise. -/
noncomputable def filterUpdate (M : POMDP X Y U) (z : Measure X) (u : U) (y : Y) : Measure X :=
  normalize (correct M (predict M z u) y)

/-- `P(Y' = y | z, u)`: the probability of the next observation `y` when the current state law is
`z` and the action `u` is applied. -/
noncomputable def obsProb (M : POMDP X Y U) (z : Measure X) (u : U) (y : Y) : ℝ :=
  (correct M (predict M z u) y Set.univ).toReal

/-- The belief-MDP cost `c̃(z, u) = ∫ c(x, u) z(dx)` of (2.6). -/
noncomputable def beliefCost (M : POMDP X Y U) (z : Measure X) (u : U) : ℝ :=
  ∫ x, M.c x u ∂z

/-- The discounted cost optimality operator of the belief MDP ((2.5)–(2.6), pp. 6–7) acting on
functions of the belief:
`(T V)(z) = min_u ( c̃(z, u) + β Σ_y P(y | z, u) V(F(z, u, y)) )`. -/
noncomputable def beliefBellman [Fintype Y] [Fintype U] (M : POMDP X Y U)
    (V : Measure X → ℝ) (z : Measure X) : ℝ :=
  ⨅ u : U, (beliefCost M z u + M.β * ∑ y : Y, obsProb M z u y * V (filterUpdate M z u y))

/-- The optimal discounted value `J*_β(z)` of the belief MDP, as the limit of value iteration
started from `0`. -/
noncomputable def Jstar [Fintype Y] [Fintype U] (M : POMDP X Y U) (z : Measure X) : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ => (beliefBellman M)^[n] 0 z)

/-- `‖c‖∞ = sup_{x,u} |c(x, u)|`. Finite because `c` is bounded (`POMDP.c_bdd`). -/
noncomputable def cNorm (M : POMDP X Y U) : ℝ := ⨆ p : X × U, |M.c p.1 p.2|

end FiniteMemQL.Convergence


