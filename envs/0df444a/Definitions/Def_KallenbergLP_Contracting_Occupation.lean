-- Prove2me | Definitions.Def_KallenbergLP_Contracting_Occupation
-- name    : KallenbergLP_Contracting_Occupation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:15:54.184626+00:00
-- url     : https://prove2.me/theorems/c518a32a-3286-48bf-ac12-a0d9fe80f44e
-- title:
--   Contraction, superharmonic vectors, and state-action frequency sets
-- statement:
--   The model is **contracting** when there are weights $\mu_i>0$ and a factor $0\le\alpha<1$ such that
--
--   $$\sum_j p_{iaj}\mu_j\le\alpha\mu_i\quad(i\in E,\ a\in A(i)).$$
--
--   A vector $w$ is **TMD-superharmonic** when $w_i\ge r_{ia}+\sum_jp_{iaj}w_j$ for every available action. The TMD-value coordinate is the supremum of total expected reward over all valid policies from that initial state.
--
--   For an initial distribution $\beta$, the feasible frequency set $P$ consists of all nonnegative vectors $x$ satisfying the flow equalities $\sum_a x_{ja}-\sum_{i,a}p_{iaj}x_{ia}=\beta_j$. The sets $K$, $K(M)$, $K(S)$, and $K(D)$ are generated respectively by general, Markov, stationary, and pure stationary policies using the same frequency formula. The stationary formula $x_{ia}(\pi)=[\beta^T(I-P(\pi))^{-1}]_i\pi_{ia}$ is also defined.
--
--   These objects support both the linear-programming correspondence and the comparison of policy classes.
--
--   **Formalization Note** The inverse action rule assigns an arbitrary pure action at a state with zero total occupation, as in equation (3.4.8). The real supremum and infinite sums are genuine under the contraction assumption in the theorems that use them.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 52, Definition 3.3.1; pp. 53–55, equations (3.3.7), (3.3.8), (3.3.11), (3.3.12), Notation 3.3.1; p. 64, Assumption 3.4.1; p. 73, equation (3.4.8)

import Mathlib
import Definitions.Def_KallenbergLP_Contracting_FiniteMDP

namespace KallenbergLP.Contracting

variable {E : Type} [Fintype E] {A : E → Type} [∀ i, Fintype (A i)]

/-- Assumption 3.4.1, retaining the specific weight and factor used in bounds. -/
structure Contraction (M : FiniteMDP E A) where
  weight : E → ℝ
  factor : ℝ
  weight_pos : ∀ i, 0 < weight i
  factor_nonneg : 0 ≤ factor
  factor_lt_one : factor < 1
  bound : ∀ i a, (∑ j, M.transition i a j * weight j) ≤ factor * weight i

/-- An initial distribution in §3.4 may vanish at some states. -/
def IsInitialDistribution (β : E → ℝ) : Prop :=
  (∀ i, 0 ≤ β i) ∧ (∑ i, β i) = 1

namespace FiniteMDP

variable (M : FiniteMDP E A)

/-- Definition 3.3.1. -/
def IsSuperharmonic (w : E → ℝ) : Prop :=
  ∀ i a, M.reward i a + ∑ j, M.transition i a j * w j ≤ w i

/-- TMD-value vector of §2.2. Contraction makes the set of attainable
values nonempty and bounded above; the corresponding theorem does not assume
these facts as extra premises. -/
noncomputable def value (i : E) : ℝ :=
  sSup {z : ℝ | ∃ π : Policy E A, IsPolicy π ∧ z = M.totalReward π i}

/-- The transition matrix of a stationary randomized rule. -/
def stationaryTransition (q : StationaryRule E A) : Matrix E E ℝ :=
  Matrix.of fun i j => ∑ a : A i, q i a * M.transition i a j

/-- The stationary expected reward vector. -/
def stationaryReward (q : StationaryRule E A) : E → ℝ :=
  fun i => ∑ a : A i, q i a * M.reward i a

/-- Formula (3.3.11), with the row-vector orientation of the book. -/
noncomputable def stationaryFrequency (β : E → ℝ) (q : StationaryRule E A) :
    StationaryRule E A := by
  classical
  exact fun i a => (∑ j : E, β j * ((1 - M.stationaryTransition q)⁻¹) j i) * q i a

/-- Formula (3.3.8) at positive state occupation. A zero-occupation state
receives an arbitrary pure action, as in (3.4.8). -/
noncomputable def ruleOfFrequency [∀ i, Nonempty (A i)]
    (x : StationaryRule E A) : StationaryRule E A := by
  classical
  exact fun i a =>
    if h : (∑ b : A i, x i b) ≠ 0 then x i a / (∑ b : A i, x i b)
    else if a = Classical.choice (inferInstance : Nonempty (A i)) then 1 else 0

/-- The feasible set of the dual program (3.3.7); §3.4 allows zero β entries. -/
def feasibleFrequency (β : E → ℝ) : Set (StationaryRule E A) :=
  {x | (∀ i a, 0 ≤ x i a) ∧
    ∀ j, (∑ a : A j, x j a) -
      (∑ i : E, ∑ a : A i, M.transition i a j * x i a) = β j}

/-- The unconstrained objective in (3.3.7). -/
def frequencyReward (x : StationaryRule E A) : ℝ :=
  ∑ i : E, ∑ a : A i, M.reward i a * x i a

/-- The four frequency sets in Notation 3.3.1, with transience automatic under
Assumption 3.4.1. `K` ranges over every history-dependent randomized policy. -/
noncomputable def K (β : E → ℝ) : Set (StationaryRule E A) :=
  {x | ∃ π : Policy E A, IsPolicy π ∧ x = M.frequency β π}

noncomputable def KM (β : E → ℝ) : Set (StationaryRule E A) :=
  {x | ∃ π : Policy E A, IsPolicy π ∧ IsMarkov π ∧ x = M.frequency β π}

noncomputable def KS (β : E → ℝ) : Set (StationaryRule E A) :=
  {x | ∃ q : StationaryRule E A, IsStationaryRule q ∧
    x = M.frequency β (stationaryPolicy q)}

noncomputable def KD (β : E → ℝ) : Set (StationaryRule E A) :=
  {x | ∃ f : PureRule E A, x = M.frequency β (purePolicy f)}

end FiniteMDP

end KallenbergLP.Contracting


