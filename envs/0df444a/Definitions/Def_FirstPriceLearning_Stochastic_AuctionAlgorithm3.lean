-- Prove2me | Definitions.Def_FirstPriceLearning_Stochastic_AuctionAlgorithm3
-- name    : FirstPriceLearning_Stochastic_AuctionAlgorithm3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:53.166984+00:00
-- url     : https://prove2.me/theorems/b4008004-f951-413d-bd0b-41ca60d0d3a5
-- title:
--   §3.4 and Corollary 1, pp. 19–20 — Algorithm 3 applied to the quantized first-price auction, as a bidding policy
-- statement:
--   §3.4 casts first-price bidding as a partially ordered contextual bandit: contexts are values, actions are bids, and on the grids (6) with $M=K=\lceil\sqrt T\rceil$ the reward of bid $a$ under context $c$ is
--
--   $$
--   r_{t,c,a}=(c-a)\,\mathbb 1(m_t\le a).
--   $$
--
--   The feedback graph is the chain with an edge from $b$ to $b'$ iff $b<b'$ (a bid $b_t$ reveals $\mathbb 1(m_t\le b)$ for every $b\ge b_t$, hence all these rewards under all contexts), and the context order is $v_1\preceq_{\mathcal C}v_2\iff v_1\le v_2$. The **induced policy** clips the value $v_t$ to $\tilde v_t=\min\{x\in\mathcal C:x\ge v_t\}$ and bids the action that Algorithm 3, run with $\delta=1/(2T)$, picks for the context $\tilde v_t$.
--
--   This file defines that policy as a bidding policy of the original problem. Its internal randomness is one uniform $u_t\in[0,1]$ per round. In round $t$ it replays Algorithm 3 on the clipped past values and on the reward vectors computed from the past feedback,
--
--   $$
--   r_{s,c,a}=(c-a)\,\mathbb 1(y_s\le a),\qquad y_s=\max\{b_s,m_s\},
--   $$
--
--   which equal the true rewards for every $a\ge b_s$ (the only ones Algorithm 3 reads), and it bids the grid point of the action chosen for $\tilde v_t$.
--
--   **Formalization Note.** The paper's $M=K=T^{1/2}$ is not an integer: the grid size is $\lceil\sqrt T\rceil$ (written $\max(1,\lceil\sqrt T\rceil)$, equal for $T\ge1$). Context $i$ and action $j$ of `Fin M`, `Fin K` stand for $(i+1)/M$ and $(j+1)/K$. The clipped index is $\max(1,\lceil vM\rceil)-1$. Algorithm 3 runs on the quantized rewards in $[-1,1]$ exactly as printed; this file does not claim that they form an instance of Definition 2 (whose rewards lie in $[0,1]$).
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, pp. 19–20, §3.4, (6) and Corollary 1

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Policy
import Definitions.Def_FirstPriceLearning_Stochastic_Algorithm3

namespace FirstPriceLearning.Stochastic

open MeasureTheory

namespace AuctionAlg3

/-- The grid size `M = K = ⌈√T⌉` of Corollary 1 (the paper's `T^{1/2}`, rounded up), at least `1`
(it equals `⌈√T⌉` for every `T ≥ 1`). -/
noncomputable def gridSize (T : ℕ) : ℕ :=
  max 1 ⌈Real.sqrt T⌉₊

theorem gridSize_pos (T : ℕ) : 0 < gridSize T :=
  Nat.lt_of_lt_of_le Nat.one_pos (le_max_left _ _)

/-- The context `i : Fin M` stands for the value `(i + 1)/M ∈ 𝒞` of (6). -/
noncomputable def ctxVal (M : ℕ) (i : Fin M) : ℝ :=
  ((i : ℝ) + 1) / M

/-- The action `j : Fin K` stands for the bid `(j + 1)/K ∈ 𝒜` of (6). -/
noncomputable def actVal (K : ℕ) (j : Fin K) : ℝ :=
  ((j : ℝ) + 1) / K

/-- The index of the clipped value `ṽ = min {x ∈ 𝒞 : x ≥ v}` (p. 20): for `v ∈ [0, 1]` it is
`max(1, ⌈vM⌉) - 1`, so that `ctxVal M (clipIndex M hM v) = ṽ`. -/
noncomputable def clipIndex (M : ℕ) (hM : 0 < M) (v : ℝ) : Fin M :=
  ⟨min (M - 1) (max 1 ⌈v * M⌉₊ - 1), lt_of_le_of_lt (min_le_left _ _) (Nat.sub_lt hM Nat.one_pos)⟩

/-- The reward vector `r_{c,a} = (c - a) 𝟙(y ≤ a)` computed from the feedback `y = max {b, m}` of
a round. For every bid `a ≥ b` it equals the quantized reward `(c - a) 𝟙(m ≤ a)` of (p. 19), which
is all Algorithm 3 reads (the chain graph has `I_t = {a ≥ a_t}`). -/
noncomputable def rewardFromFeedback (M K : ℕ) (y : ℝ) : Fin M → Fin K → ℝ :=
  fun c a => (ctxVal M c - actVal K a) * (if y ≤ actVal K a then 1 else 0)

/-- The inputs of Algorithm 3 for the quantized auction of Corollary 1 (iid case): horizon `T`,
`δ = 1/(2T)`, `M = K = ⌈√T⌉`, the chain feedback graph (an edge from `b` to `b'` iff `b < b'`),
the context order `v₁ ⪯_𝒞 v₂ ⇔ v₁ ≤ v₂`, and its topological ordering `1/M, 2/M, …, 1`. -/
noncomputable def params (T : ℕ) : Alg3Params (gridSize T) (gridSize T) where
  T := T
  δ := 1 / (2 * T)
  E := fun j j' => j < j'
  leC := fun i i' => i ≤ i'
  ord := Equiv.refl _
  hK := gridSize_pos T

/-- Corollary 1's policy: Algorithm 3 run on the quantized first-price auction, as a bidding
policy of the original problem. Its internal randomness is one uniform `u_t ∈ [0, 1]` per round
(line (⋆)). At round `t` it replays Algorithm 3 on the clipped past values and on the reward
vectors computed from the past feedback `y_s = max {b_s, m_s}`, then plays the bid `(a_t + 1)/K`
of the action chosen for the clipped current value. -/
noncomputable def policy (T : ℕ) : Policy T where
  U := Fin T → unitInterval
  μU := Measure.pi fun _ => volume
  bid t u vs ys :=
    actVal (gridSize T)
      (Alg3.chooseAction (params T)
        (Alg3.state (params T)
          (fun s : Fin t.val => clipIndex (gridSize T) (gridSize_pos T) (vs (Fin.castSucc s)))
          (fun s => rewardFromFeedback (gridSize T) (gridSize T) (ys s))
          (fun s => u ⟨s.val, lt_trans s.isLt t.isLt⟩) t.val)
        (clipIndex (gridSize T) (gridSize_pos T) (vs (Fin.last t.val))) (u t))
  bid_mem t u vs ys := by
    refine ⟨by unfold actVal; positivity, ?_⟩
    unfold actVal
    rw [div_le_one (by exact_mod_cast gridSize_pos T)]
    set j := Alg3.chooseAction (params T) _ _ (u t)
    have := j.isLt
    exact_mod_cast this

end AuctionAlg3

end FirstPriceLearning.Stochastic


