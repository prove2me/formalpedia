-- Prove2me | Definitions.Def_markov_entanglement_multi
-- name    : markov_entanglement_multi
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-08-07T05:22:30.486654+00:00
-- url     : https://prove2.me/theorems/41644990-9982-4e7f-92b7-7e3fd8a4477a
-- title:
--   Multi-agent separability, weighted distances, and entanglement measures
-- statement:
--   ## Statement
--
--   **Definitions.** For $N$ agents with local state-action spaces $S_i$, write the joint
--   space as $\prod_i S_i$. A joint transition is **separable** when
--   $$P \;=\; \sum_{j=1}^{K} x_j\, P^{(j)}_1 \otimes \cdots \otimes P^{(j)}_N, \qquad \textstyle\sum_j x_j = 1,$$
--   with each $P^{(j)}_i$ a transition matrix. Given a distribution $\mu$, the **$\mu$-norm** is
--   $\|x\|_\mu = \sum_i \mu_i |x_i|$, the **$\mu$-weighted total variation distance** replaces the
--   maximum over rows of the usual distance by a $\mu$-average, and the **$\mu$-weighted agent-wise
--   total variation distance** compares the joint transition marginalised onto agent $i$ with a
--   candidate local transition. The **measure of Markov entanglement** is the distance from $P$ to
--   the nearest separable transition,
--   $$\mathcal{E}(P) \;=\; \inf_{Q \text{ separable}} d(P, Q),$$
--   for a distance $d$ left abstract, and $\mathcal{E}_i$ is its agent-wise counterpart. Further
--   definitions cover product-form transitions, a shared global coordinate, the **measure of reward
--   entanglement** $e(r) = \inf_{r_1,\dots,r_N} \|r - \sum_i r_i\|_\mu$, and the span of the
--   transition matrices.
--
--   ## Notes
--
--   These are the objects the mission's theorems are stated against. Three design points are
--   worth flagging for anyone reusing them.
--
--   The measure of entanglement is **parameterised by the distance** $d$ rather than fixed to one
--   choice. The source defines it that way — "where $d(\cdot,\cdot)$ is some distance measure" — and
--   keeping it abstract means the total variation, agent-wise, and $\mu$-weighted variants are all
--   instances of one definition instead of three near-duplicates.
--
--   The generic pieces are **reused, not restated**: transition matrices, positive distributions,
--   stationarity, the Bellman fixed point and the plain total variation distance come from the
--   already-published two-agent definitions module, which states them over an arbitrary finite index
--   type. Only the genuinely $N$-agent layer is new here.
--
--   Reward entanglement is defined in exact parallel to Markov entanglement — a distance from an
--   object to the set of decomposable ones — so the two error terms in the cooperative bound have
--   the same shape.
--
--   Search terms: separable transition kernel, tensor product of stochastic matrices, agent-wise
--   total variation distance, occupancy-weighted norm, measure of entanglement, value decomposition.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Definitions 1, 4-8, 10, 11, 14 and Eq. (15)

import Definitions.Def_markov_entanglement

open scoped BigOperators

namespace MarkovEntanglement

/-! ## Multi-agent vocabulary

The two-agent file this imports already states `IsTransitionMatrix`,
`IsPositiveDist`, `IsStationary`, `IsBellmanQ` and `tvDist` over an arbitrary
finite index type, so they are reused verbatim here rather than restated. What
follows is the `N`-agent layer plus the weighted distances, kept generic in the
same spirit: agents carry their own state-action spaces `S i`, and the measure of
entanglement is parameterised by an abstract distance, exactly as the source
leaves `d(·,·)` abstract. -/

variable {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The joint state-action space of `N` agents: a choice of local state-action pair
for each agent. -/
abbrev Joint (S : Fin N → Type*) : Type _ := ∀ i, S i

/-- The `N`-fold tensor product of local transition matrices: agents move
independently, so the joint probability is the product of the local ones. -/
def tensorProdN (P : ∀ i, Matrix (S i) (S i) ℝ) : Matrix (Joint S) (Joint S) ℝ :=
  fun p q => ∏ i, P i (p i) (q i)

/-- A joint transition is **separable** when it is a finite affine combination of
tensor products of local transitions; otherwise the agents are **entangled**. -/
def IsSeparableN (P : Matrix (Joint S) (Joint S) ℝ) : Prop :=
  ∃ (K : ℕ) (x : Fin K → ℝ) (Pj : Fin K → ∀ i, Matrix (S i) (S i) ℝ),
    (∀ k i, IsTransitionMatrix (Pj k i)) ∧ (∑ k, x k = 1) ∧
      P = ∑ k, x k • tensorProdN (Pj k)

/-- The **`μ`-norm** of a vector: the `μ`-weighted average of its absolute values.
A norm when `μ` is strictly positive, a seminorm in general. -/
def muNorm {ι : Type*} [Fintype ι] (μ x : ι → ℝ) : ℝ := ∑ i, μ i * |x i|

/-- The **`μ`-weighted total variation distance** between transition matrices:
the total variation distance of corresponding rows, averaged with weights `μ`
instead of maximised. -/
noncomputable def muTVDist {ι : Type*} [Fintype ι] (μ : ι → ℝ) (P Q : Matrix ι ι ℝ) : ℝ :=
  ∑ i, μ i * ((1 / 2) * ∑ j, |P i j - Q i j|)

/-- The transition probability that agent `i` moves to local state-action `t`,
obtained by marginalising the joint transition over every other agent. -/
def marginalN (i : Fin N) (P : Matrix (Joint S) (Joint S) ℝ)
    (p : Joint S) (t : S i) : ℝ :=
  ∑ q : Joint S, if q i = t then P p q else 0

/-- The marginal of the occupancy measure `μ` onto agent `i`'s coordinate. -/
def marginalDist (i : Fin N) (μ : Joint S → ℝ) (s : S i) : ℝ :=
  ∑ q : Joint S, if q i = s then μ q else 0

/-- `Pi` is agent `i`'s **local (marginalised) transition** induced by the joint
transition `P` under the occupancy measure `μ`, the `N`-agent form of Eq. (2).
Both sides are scaled by the marginal of `μ`, so that no division by a marginal
that could vanish off its support is needed.  This is the right notion to use in
place of demanding that the joint marginal depend on the joint state only through
agent `i`'s coordinate, which would already force agent-wise separability. -/
def IsLocalTransitionN (i : Fin N) (P : Matrix (Joint S) (Joint S) ℝ)
    (μ : Joint S → ℝ) (Pi : Matrix (S i) (S i) ℝ) : Prop :=
  ∀ s t : S i, marginalDist i μ s * Pi s t
    = ∑ p : Joint S, (if p i = s then μ p else 0) * marginalN i P p t

/-- The **`μ`-weighted agent-wise total variation distance** for agent `i`:
how far the joint transition, marginalised onto agent `i`, sits from a candidate
local transition, averaged over joint state-action pairs with weights `μ`. -/
noncomputable def muAgentTVDistN (i : Fin N) (μ : Joint S → ℝ)
    (P : Matrix (Joint S) (Joint S) ℝ) (Pi : Matrix (S i) (S i) ℝ) : ℝ :=
  ∑ p : Joint S, μ p * ((1 / 2) * ∑ t : S i, |marginalN i P p t - Pi (p i) t|)

/-- The **measure of Markov entanglement** with respect to an arbitrary distance
`d`, following the source, which defines it as the distance from the joint
transition to the nearest separable one and leaves `d` abstract. Instantiate `d`
with the total variation distance, the agent-wise variant, or their `μ`-weighted
counterparts. -/
noncomputable def entanglementWith
    (d : Matrix (Joint S) (Joint S) ℝ → Matrix (Joint S) (Joint S) ℝ → ℝ)
    (P : Matrix (Joint S) (Joint S) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ Q : Matrix (Joint S) (Joint S) ℝ, IsSeparableN Q ∧ r = d P Q}

/-- The **agent-wise measure of Markov entanglement** for agent `i`: how far the
joint transition sits from being generated by a single local transition for `i`,
in `μ`-weighted agent-wise total variation distance. -/
noncomputable def entanglementN (i : Fin N) (μ : Joint S → ℝ)
    (P : Matrix (Joint S) (Joint S) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ Pi : Matrix (S i) (S i) ℝ,
    IsTransitionMatrix Pi ∧ r = muAgentTVDistN i μ P Pi}

/-- `Q` decomposes as a sum of local values: `Q(s,a) = Σ_i Q_i(s_i, a_i)`. -/
def IsValueDecomposition (Q : Joint S → ℝ) (Qi : ∀ i, S i → ℝ) : Prop :=
  ∀ p : Joint S, Q p = ∑ i, Qi i (p i)

/-! ## Weakly-coupled systems, shared global state, and reward entanglement -/

/-- A joint transition is **product-form**: the agents' local kernels are independent,
`P(s' | s) = ∏ i, P i (s' i | s i)`.  This is the transition half of a weakly-coupled
MDP; the coupling in such a model lives entirely in the action constraints. -/
def IsProductTransition (P : Matrix (Joint S) (Joint S) ℝ)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) : Prop :=
  P = tensorProdN Pl

/-- The joint state-action space of `N` agents together with a shared global
coordinate, used for systems where the agents also observe a common state. -/
abbrev JointZ (S : Fin N → Type*) (Z : Type*) : Type _ := (∀ i, S i) × Z

/-- Agent `i`'s marginal of a joint transition on a system with a shared global
coordinate: the probability of moving to local state-action `t` with global state `z`. -/
def marginalZ {Z : Type*} [Fintype Z] [DecidableEq Z] (i : Fin N)
    (P : Matrix (JointZ S Z) (JointZ S Z) ℝ) (p : JointZ S Z) (t : S i × Z) : ℝ :=
  ∑ q : JointZ S Z, if q.1 i = t.1 ∧ q.2 = t.2 then P p q else 0

/-- A reward on the joint space **decomposes** when it is a sum of local rewards. -/
def IsDecomposableReward (r : Joint S → ℝ) : Prop :=
  ∃ rl : ∀ i, S i → ℝ, ∀ p, r p = ∑ i, rl i (p i)

/-- The **measure of reward entanglement**: how far a joint reward is, in `μ`-norm,
from being a sum of local rewards.  Zero exactly when the reward decomposes, and the
direct analogue for rewards of the measure of Markov entanglement for transitions. -/
noncomputable def rewardEntanglement (μ : Joint S → ℝ) (r : Joint S → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ rl : ∀ i, S i → ℝ, c = muNorm μ (fun p => r p - ∑ i, rl i (p i))}

/-- The linear span of the transition matrices on a finite index type. -/
noncomputable def transitionSpan (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submodule ℝ (Matrix ι ι ℝ) :=
  Submodule.span ℝ {P : Matrix ι ι ℝ | IsTransitionMatrix P}

end MarkovEntanglement


