-- Prove2me | Definitions.Def_MNLBandit_LowerBound_BernoulliMAB
-- name    : MNLBandit_LowerBound_BernoulliMAB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:19.80512+00:00
-- url     : https://prove2.me/theorems/18a72157-1384-4525-8696-746c25714c1e
-- title:
--   §5.1, p. 15 — online algorithms for the Bernoulli bandit, the instance I_MAB (Definition 5.1) and its expected regret
-- statement:
--   The multi-armed bandit side of the reduction in the lower bound of Agrawal, Avadhanula, Goyal and Zeevi.
--
--   **Bernoulli bandit.** There are $N$ arms; pulling arm $i$ yields a reward $1$ with probability $\mu_i$ and $0$ otherwise. An *online algorithm* $\mathcal A$ chooses, after every history of pulled arms and observed rewards of the first $t$ rounds, a probability vector over arms, from which the arm $\mathcal A_{t+1}$ is drawn. The law of a view $((a_1,x_1),\dots,(a_T,x_T))$ is
--
--   $$
--   \mathbb P_\mu\big((a_t,x_t)_{t\le T}\big)=\prod_{t=1}^{T}\mathcal A_t(a_t\mid (a_s,x_s)_{s<t})\;\mu_{a_t}^{x_t}(1-\mu_{a_t})^{1-x_t}.
--   $$
--
--   For a time $t\ge1$, $\mathcal P_\mu(a_t=i)$ is the probability that the arm pulled at time $t$ is $i$.
--
--   **The instance $I_{\mathrm{MAB}}$ (Definition 5.1).** For a hidden arm $j\in\{1,\dots,N\}$ the means are $\mu_i=\alpha+\epsilon$ if $i=j$ and $\mu_i=\alpha$ otherwise, with
--
--   $$
--   \epsilon=\frac1{100}\sqrt{\frac{N\alpha}{T}}.
--   $$
--
--   The hidden arm is uniform on $\{1,\dots,N\}$, and the expected regret of $\mathcal A$ on $I_{\mathrm{MAB}}$ is
--
--   $$
--   \mathrm{Reg}_{\mathcal A}(T,\mu)=\frac1N\sum_{j=1}^{N}\mathbb E_{j}\Big[\sum_{t=1}^{T}(\mu_j-\mu_{\mathcal A_t})\Big],
--   $$
--
--   the expectation being over the hidden arm and over the rewards and the algorithm's randomization.
--
--   These are the objects of Lemma 5.1 (the regret of any algorithm on $I_{\mathrm{MAB}}$ is at least $\epsilon T/6$) and of the guessing lemma E.2.
--
--   **Formalization Note** Arms and rounds are 0-based. `armProb A μ s i` is the probability that the arm pulled after $s$ observed rounds, i.e. at the paper's time $t=s+1$, is $i$. The family `imabMeans α ϵ j` takes $\epsilon$ as an argument; `epsMAB N α T` is Definition 5.1's value. The history-prefix function `prefixOf` is imported from the `Setting` file of this mission.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 15, Definition 5.1, §5.1, Lemma 5.1; p. 57, Lemma E.2

import Mathlib
import Definitions.Def_MNLBandit_LowerBound_Setting

namespace MNLBandit.LowerBound

/-- The Bernoulli law with parameter `p` on `{0, 1}` (`false ↦ 1 − p`, `true ↦ p`). -/
noncomputable def bern (p : ℝ) : Bool → ℝ
  | true => p
  | false => 1 - p

/-- An online algorithm for the `N`-armed Bernoulli bandit (§5.1, p. 15), possibly randomized:
after the first `t` rounds (arms pulled and 0/1 rewards seen) it pulls arm `i` at round `t`
(0-based) with probability `A t h i`. -/
def MABAlg (N : ℕ) := (t : ℕ) → (Fin t → Fin N × Bool) → Fin N → ℝ

/-- The weights of an online algorithm form a probability vector over arms after every history. -/
def IsMABAlg {N : ℕ} (A : MABAlg N) : Prop :=
  ∀ t (h : Fin t → Fin N × Bool), (∀ i, 0 ≤ A t h i) ∧ ∑ i, A t h i = 1

/-- The law of the length-`T` view `h` (arms pulled and rewards seen) of the algorithm `A` on the
Bernoulli bandit with arm means `μ`. -/
noncomputable def mabLaw {N : ℕ} (A : MABAlg N) (μ : Fin N → ℝ) (T : ℕ)
    (h : Fin T → Fin N × Bool) : ℝ :=
  ∏ t : Fin T, A t (prefixOf h t) (h t).1 * bern (μ (h t).1) (h t).2

/-- The arm means of `I_MAB` (Definition 5.1, p. 15) when the hidden arm is `j`:
`μᵢ = α + ϵ` if `i = j` and `μᵢ = α` otherwise. -/
def imabMeans {N : ℕ} (α ϵ : ℝ) (j : Fin N) : Fin N → ℝ :=
  fun i => if i = j then α + ϵ else α

/-- `ϵ = (1/100) √(N α / T)` of Definition 5.1 (p. 15). -/
noncomputable def epsMAB (N : ℕ) (α : ℝ) (T : ℕ) : ℝ :=
  1 / 100 * Real.sqrt ((N : ℝ) * α / T)

/-- `𝒫_μ(a_{s+1} = i)`: the probability that the arm pulled at time `s + 1` (1-based; after `s`
observed rounds) is `i`, when the arm means are `μ`. -/
noncomputable def armProb {N : ℕ} (A : MABAlg N) (μ : Fin N → ℝ) (s : ℕ) (i : Fin N) : ℝ :=
  ∑ h : Fin s → Fin N × Bool, mabLaw A μ s h * A s h i

/-- The expected regret of `A` on the randomized instance `I_MAB` (Lemma 5.1, p. 15):
`𝔼[∑_{t=1}^T (μ_j − μ_{A_t})]`, the expectation over the hidden arm `j`, uniform on the `N` arms,
and over the rewards and the algorithm's randomization. -/
noncomputable def regretIMAB {N : ℕ} (A : MABAlg N) (α ϵ : ℝ) (T : ℕ) : ℝ :=
  (1 / (N : ℝ)) * ∑ j : Fin N, ∑ h : Fin T → Fin N × Bool,
    mabLaw A (imabMeans α ϵ j) T h * ∑ t : Fin T, (imabMeans α ϵ j j - imabMeans α ϵ j (h t).1)

end MNLBandit.LowerBound


