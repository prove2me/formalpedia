-- Prove2me | Definitions.Def_MNLBandit_LowerBound_Setting
-- name    : MNLBandit_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:14.026996+00:00
-- url     : https://prove2.me/theorems/b82df227-6e7d-4243-ba01-b4e69e0bf233
-- title:
--   §2, §5, App. E.1 — MNL choice probabilities (2.1), revenue (2.2), K-cardinality regret (2.6) for randomized policies, instances I_MNL and Î_MNL
-- statement:
--   This file fixes the MNL-Bandit model of Agrawal, Avadhanula, Goyal and Zeevi used in their lower bound (Theorem 2).
--
--   **Products and choices.** There are $n$ products. When the seller offers an assortment $S\subseteq\{1,\dots,n\}$, one customer chooses the no-purchase alternative $0$ or a product of $S$. Under the multinomial logit (MNL) model with no-purchase weight $v_0$ and attraction parameters $v_1,\dots,v_n$,
--
--   $$
--   p_i(S)=\frac{v_i}{v_0+\sum_{j\in S}v_j}\quad (i\in S\cup\{0\}),\qquad p_i(S)=0\ \text{otherwise.}
--   $$
--
--   **Instances.** An instance is a triple $(v_0,v,r)$ with revenues $r_i$. It is *valid* when $v_0>0$, $0\le v_i\le v_0$ for every $i$, and $r_i\in[0,1]$. The expected revenue of $S$ is
--
--   $$
--   R(S,v)=\frac{\sum_{i\in S}r_iv_i}{v_0+\sum_{j\in S}v_j},
--   $$
--
--   and $R(S^*,v)=\max\{R(S,v): |S|\le K\}$ is the best revenue among assortments of at most $K$ products (the family contains $\emptyset$, so the maximum exists).
--
--   **Policies.** A (behavioural) randomized policy $\pi$ assigns, after every history of offered assortments and observed choices of the first $t$ periods, a probability vector over assortments; the assortment of period $t+1$ is drawn from it. It respects the $K$-cardinality constraint if it puts positive probability only on assortments with $|S|\le K$. The law of a history $((S_1,c_1),\dots,(S_T,c_T))$ is
--
--   $$
--   \mathbb P_\pi\big((S_t,c_t)_{t\le T}\big)=\prod_{t=1}^{T}\pi_t(S_t\mid (S_s,c_s)_{s<t})\,p_{c_t}(S_t),
--   $$
--
--   and the regret over $T$ periods is
--
--   $$
--   \mathrm{Reg}_\pi(T,v)=T\,R(S^*,v)-\mathbb E_\pi\Big[\sum_{t=1}^{T}R(S_t,v)\Big].
--   $$
--
--   A deterministic policy is a map from the past choices $c_1,\dots,c_{t-1}$ to the assortment $S_t$; its choice law is $\prod_{t}p_{c_t}(S_t)$ with $S_t$ the policy's assortment on the prefix.
--
--   **Instances of the lower bound.** $I_{\mathrm{MNL}}$ (Definition 5.2) has $NK$ products, $v_0=K$, $r_i=1$, and $v_i=\alpha+\epsilon$ for the $K$ products of a hidden group $j$ ($\lceil i/K\rceil=j$) and $v_i=\alpha$ otherwise. $\hat I_{\mathrm{MNL}}$ (Definition E.1) has $N$ products, $v_0=1$, $v_i=1/2$ for $i\ge2$, $v_1\in\{1/2,\,1/2+\epsilon\}$, and revenues $r_1=1$, $r_2=(1+\epsilon)/(3+2\epsilon)$, $r_i=0.01$ for $i\ge3$.
--
--   These objects carry every statement of the mission: the goal (Theorem 2) is a lower bound on the averaged regret above over all policies that respect the cardinality constraint.
--
--   **Formalization Note** Products are 0-based (`Fin n`; the paper's product $i$ is index $i-1$) and a choice is `Option (Fin n)` with `none` the no-purchase alternative. Periods are 0-based. Histories have finite length, so every expectation is a finite sum. Behavioural randomization (a probability vector at every history) is equivalent, by Kuhn's theorem under perfect recall, to the paper's external randomization $U$ of (2.4). In `instMNL` the group of the 0-based product $i$ is `i / K` (natural division), which is the paper's $\lceil (i+1)/K\rceil$ shifted to 0-based groups. The parameter $\epsilon$ of both instances is an argument; the paper's values $\epsilon=\frac1{100}\sqrt{N\alpha/T}$ and $\epsilon=\sqrt{1/(32T)}$ are special cases. `instMNL` is not used by any statement of the mission; it records Definition 5.2 for solvers.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, pp. 5–7, (2.1)–(2.6); p. 14, Theorem 2; p. 16, Definition 5.2; p. 59, Definition E.1; p. 61, (E.9)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting

namespace MNLBandit.LowerBound

/-- The first `t` entries of a length-`T` sequence `h`, for a time index `t : Fin T`
(the history strictly before time `t`, 0-based). -/
def prefixOf {α : Type*} {T : ℕ} (h : Fin T → α) (t : Fin T) : Fin (t : ℕ) → α :=
  fun s => h (Fin.castLE t.isLt.le s)

/-- The MNL choice probabilities (2.1) of Agrawal–Avadhanula–Goyal–Zeevi (arXiv:1706.03880v2, p. 5)
with an explicit no-purchase weight `v₀`: when the assortment `S` is offered, the no-purchase
alternative (`none`, the paper's `0`) is chosen with probability `v₀ / (v₀ + ∑_{j ∈ S} v j)` and
product `i` (`some i`) with probability `v i / (v₀ + ∑_{j ∈ S} v j)` if `i ∈ S`, and `0` otherwise.
Products are 0-based: the paper's product `i + 1` is the index `i : Fin n`. -/
noncomputable def choiceProb {n : ℕ} (v₀ : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) :
    Option (Fin n) → ℝ
  | none => v₀ / (v₀ + ∑ j ∈ S, v j)
  | some i => if i ∈ S then v i / (v₀ + ∑ j ∈ S, v j) else 0

/-- An instance of the MNL-Bandit problem with `n` products: the no-purchase weight `v₀`, the
attraction parameters `v` and the revenues `r`. -/
structure Instance (n : ℕ) where
  v₀ : ℝ
  v : Fin n → ℝ
  r : Fin n → ℝ

/-- The standing assumptions of Theorem 2 (p. 14) and §2 (p. 5): `v₀ > 0`, `0 ≤ vᵢ ≤ v₀` for
every product, and revenues `rᵢ ∈ [0, 1]`. -/
def Instance.Valid {n : ℕ} (I : Instance n) : Prop :=
  0 < I.v₀ ∧ (∀ i, 0 ≤ I.v i ∧ I.v i ≤ I.v₀) ∧ ∀ i, I.r i ∈ Set.Icc (0 : ℝ) 1

/-- The expected revenue (2.2) of the assortment `S`:
`R(S, v) = ∑_{i ∈ S} rᵢ vᵢ / (v₀ + ∑_{j ∈ S} vⱼ)`, the published `mnlObjective`. -/
noncomputable def Instance.revenue {n : ℕ} (I : Instance n) (S : Finset (Fin n)) : ℝ :=
  ChoiceCDLP.MNL.mnlObjective I.v I.r I.v₀ S

/-- The `K`-cardinality constrained family `{S ⊆ {1, …, n} : |S| ≤ K}` (§5, p. 14). -/
def cardFamily (n K : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => S.card ≤ K)

theorem cardFamily_nonempty (n K : ℕ) : (cardFamily n K).Nonempty :=
  ⟨∅, by simp [cardFamily]⟩

/-- `R(S*, v)`, the maximum expected revenue over assortments of at most `K` products. -/
noncomputable def Instance.optRevenue {n : ℕ} (I : Instance n) (K : ℕ) : ℝ :=
  (cardFamily n K).sup' (cardFamily_nonempty n K) I.revenue

/-- One period of the seller's history: the offered assortment and the customer's choice. -/
abbrev Step (n : ℕ) := Finset (Fin n) × Option (Fin n)

/-- A behavioural (randomized) policy: after the history of the first `t` periods (offered
assortments and choices) it puts the weight `π t h S` on offering `S` at period `t` (0-based). -/
def BPolicy (n : ℕ) := (t : ℕ) → (Fin t → Step n) → Finset (Fin n) → ℝ

/-- The weights of a behavioural policy form a probability vector over assortments after every
history. -/
def IsBPolicy {n : ℕ} (π : BPolicy n) : Prop :=
  ∀ t (h : Fin t → Step n), (∀ S, 0 ≤ π t h S) ∧ ∑ S, π t h S = 1

/-- A behavioural policy that only ever offers assortments of at most `K` products. -/
def IsCardinalityK {n : ℕ} (K : ℕ) (π : BPolicy n) : Prop :=
  IsBPolicy π ∧ ∀ t (h : Fin t → Step n) S, 0 < π t h S → S.card ≤ K

/-- The law of the length-`T` history `h` (offered assortments and choices) under the policy `π`
on the instance `I`: at each period the assortment is drawn from the policy's weights given the
past, and the choice from the MNL probabilities (2.1) of the offered set, independently of the past
given that set. -/
noncomputable def bhistProb {n : ℕ} (I : Instance n) (π : BPolicy n) (T : ℕ)
    (h : Fin T → Step n) : ℝ :=
  ∏ t : Fin T, π t (prefixOf h t) (h t).1 * choiceProb I.v₀ I.v (h t).1 (h t).2

/-- The regret (2.6) over `T` periods under the `K`-cardinality constraint:
`T · R(S*, v) − 𝔼_π[∑_{t=1}^T R(S_t, v)]`. -/
noncomputable def regret {n : ℕ} (I : Instance n) (K : ℕ) (π : BPolicy n) (T : ℕ) : ℝ :=
  (T : ℝ) * I.optRevenue K -
    ∑ h : Fin T → Step n, bhistProb I π T h * ∑ t : Fin T, I.revenue (h t).1

/-- The law of the length-`T` choice sequence `c` under a deterministic policy `π` with MNL
parameters `v₀`, `v`: `∏_t p_{c_t}(S_t)` with `S_t = π t` applied to the choices before period `t`. -/
noncomputable def histProb {n : ℕ} (v₀ : ℝ) (v : Fin n → ℝ) (π : MNLBandit.UCB.Policy n) (T : ℕ)
    (c : Fin T → Option (Fin n)) : ℝ :=
  ∏ t : Fin T, choiceProb v₀ v (π t (prefixOf c t)) (c t)

/-- The instance `I_MNL` of Definition 5.2 (p. 16) for the hidden group `j`: `N K` products,
`v₀ = K`, product `i` (0-based) has `vᵢ = α + ϵ` if it lies in group `j` (`i / K = j`, the paper's
`⌈i/K⌉ = j` with 1-based indices) and `vᵢ = α` otherwise, and every revenue is `1`. -/
noncomputable def instMNL (N K : ℕ) (α ϵ : ℝ) (j : Fin N) : Instance (N * K) where
  v₀ := K
  v := fun i => if (i : ℕ) / K = (j : ℕ) then α + ϵ else α
  r := fun _ => 1

/-- The instance `Î_MNL` of Definition E.1 (p. 59), `N` products (0-based): `v₀ = 1`; product `0`
(the paper's product 1) has `v = 1/2 + ϵ` if `b = true` and `v = 1/2` if `b = false`; every other
product has `v = 1/2`. Revenues: `r = 1` for product `0`, `r = (1 + ϵ)/(3 + 2ϵ)` for product `1`
(the paper's product 2), and `r = 0.01` for the others. -/
noncomputable def instHat (N : ℕ) (ϵ : ℝ) (b : Bool) : Instance N where
  v₀ := 1
  v := fun i => if (i : ℕ) = 0 then (if b then 1 / 2 + ϵ else 1 / 2) else 1 / 2
  r := fun i => if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then (1 + ϵ) / (3 + 2 * ϵ) else 1 / 100

end MNLBandit.LowerBound


