-- Prove2me | Definitions.Def_WeberGittins_Submodular_Model
-- name    : WeberGittins_Submodular_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:30.384613+00:00
-- url     : https://prove2.me/theorems/817e4737-821a-42fe-bebb-80275d551a0f
-- title:
--   Section 1 and Section 5, pp. 1024 and 1029–1030 — bounded nonnegative rewards, the restricted value $V(I)$, and the prevailing-charge stacks $\gamma_{jk}$
-- statement:
--   This module fixes three objects of Weber's paper on top of the published discounted $k$-armed Markov bandit (`GittinsIndex`): all bandits evolve on a measurable state space $S$ with transition kernel $P$ and mean reward $r:S\to\mathbb R$, and $\beta$ is the discount factor.
--
--   1. **Standing assumption** (Section 1, p. 1024): "rewards are nonnegative and uniformly bounded", that is, $r(y)\ge0$ for every state $y$ and there is a constant $C$ with $r(y)\le C$ for every $y$.
--   2. **The restricted value $V(I)$** (Section 5, pp. 1029–1030). Fix the initial states $x=(x_1,\dots,x_n)=x(0)$ of the $n$ bandits. For $I\subseteq\{1,\dots,n\}$, $P(I)$ is the restriction of the problem to the bandits in $I$: the $|I|$-armed bandit whose arms are the bandits of $I$, each started in its state $x_j$. $V(I)$ is its maximal expected total-discounted reward,
--   $$
--   V(I)=\sup_{\pi}\;\mathbb E_\pi\Big[\sum_{t=0}^\infty\beta^tR_{j(t)}(x_{j(t)}(t))\Big]\quad(I\ne\emptyset),\qquad V(\emptyset)=0,
--   $$
--   the supremum over all (history-dependent, randomized) policies $\pi$ of $P(I)$.
--   3. **Prevailing-charge stacks on a realisation** (proof of Theorem 4, p. 1030). A realisation $\omega$ assigns to each bandit $j$ the sequence of states $\omega_j(0)=x_j,\omega_j(1),\omega_j(2),\dots$ it passes through on its successive plays. With $\gamma(y)$ the fair charge (Gittins index in the ratio form (4)) of state $y$, the prevailing charge of bandit $j$ after $k$ plays is
--   $$
--   \gamma_{jk}(\omega)=\min_{0\le v\le k}\gamma\big(\omega_j(v)\big),
--   $$
--   so that $\gamma_{j0}\ge\gamma_{j1}\ge\cdots$.
--
--   These are the objects of Theorem 4 and of the two identities its proof combines.
--
--   **Formalization Note** Weber's bandits each have their own state space, reward and law; the published model has one kernel and one reward on one state space, which loses nothing (take the disjoint union). $r$ is the conditional mean of the random reward $R_j(x_j(t))$. The value of a policy is the published `markovBanditDiscountedValue`, $\sum_t\beta^t\,\mathbb E_\pi[r(x_{j(t)}(t))]$, equal to $\mathbb E_\pi[\sum_t\beta^t r(\cdot)]$ for bounded rewards. The arms of $P(I)$ are the bandits of $I$ listed in increasing order (`Finset.orderEmbOfFin`); any other order gives the same value. $V(\emptyset)=0$ is explicit, because $P(\emptyset)$ has no bandit. Under the standing assumptions every value lies in $[0,C/(1-\beta)]$, so the real supremum is a genuine supremum. The paper's symbol $S$ for the set of all bandits is written `Finset.univ : Finset (Fin n)`, since $S$ is the state space here. The fair charge $\gamma$ is the published `gittinsIndex`; Weber's index $G=\gamma/(1-\beta)$ does not appear in this mission.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1024, Section 1 (standing assumptions, eq. (1)); pp. 1029–1030, Section 5 (definition of P(I) and V(I)); p. 1030, proof of Theorem 4 (prevailing charges γ_jk)

import Definitions.Def_GittinsIndex
import Definitions.Def_WeberGittins_Suboptimality_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.Submodular

/-- Weber (1992), Section 5, pp. 1029–1030: `V(I)`, the maximal expected total-discounted reward
of `P(I)`, the restriction of the problem to the bandits in `I`, from the fixed initial states
`x(0) = x`. `P(I)` is the `|I|`-armed game whose arms are the bandits of `I` listed in increasing
order (`I.orderEmbOfFin`), each started in its state in `x`; `V(I)` is the supremum of
`markovBanditDiscountedValue` over all its policies. `P(∅)` has no bandit and `V(∅) = 0`. -/
noncomputable def restrictedValue {n : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (β : ℝ) (x : Fin n → S) (I : Finset (Fin n)) : ℝ :=
  if I = ∅ then 0 else
    ⨆ π : MarkovBanditPolicy I.card S,
      markovBanditDiscountedValue P r β π (fun m => x (I.orderEmbOfFin rfl m))

/-- Weber (1992), proof of Theorem 4, p. 1030: on a fixed realisation `ω` (bandit `j` passes
through the states `ω j 0 = x_j(0), ω j 1, ω j 2, …` on its successive plays), the prevailing
charge of bandit `j` after it has been played `k` times,
`γ_{jk} = min_{0 ≤ v ≤ k} γ_j(ω j v)`, with `γ = gittinsIndex P r β` the fair charge. -/
noncomputable def prevailingChargeStack {n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (β : ℝ) (ω : Fin n → ℕ → S)
    (j : Fin n) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ k)⟩
    fun v => gittinsIndex P r β (ω j v)

end WeberGittins.Submodular


