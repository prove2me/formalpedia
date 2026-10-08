-- Prove2me | Definitions.Def_SuttonBartoRL_OffPolicy_BELearnabilityExample
-- name    : SuttonBartoRL_OffPolicy_BELearnabilityExample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:39:55.940934+00:00
-- url     : https://prove2.me/theorems/a08a0d56-29b1-4079-a29d-2b62f3106751
-- title:
--   The two Markov reward processes of Example 11.4
-- statement:
--   The two Markov reward processes of Example 11.4 (Sutton & Barto, p. 276), transcribed from the book's figure. Where two edges leave a state, each is taken with probability $\tfrac12$. Rewards lie in $\{-1,0,1\}$.
--
--   1. **Left MRP**, states $\mathsf A,\mathsf B$: $\mathsf A\to\mathsf B$ with reward $0$; $\mathsf B\to\mathsf A$ with reward $1$ and $\mathsf B\to\mathsf B$ with reward $-1$, each with probability $\tfrac12$. Features $\mathbf x(\mathsf A) = (1,0)^\top$, $\mathbf x(\mathsf B) = (0,1)^\top$.
--   2. **Right MRP**, states $\mathsf A,\mathsf B,\mathsf B'$: $\mathsf A\to\mathsf B$ and $\mathsf A\to\mathsf B'$, each with reward $0$ and probability $\tfrac12$; $\mathsf B\to\mathsf A$ with reward $1$; $\mathsf B'\to\mathsf B$ and $\mathsf B'\to\mathsf B'$, each with reward $-1$ and probability $\tfrac12$. The states $\mathsf B$ and $\mathsf B'$ look the same: $\mathbf x(\mathsf A) = (1,0)^\top$, $\mathbf x(\mathsf B) = \mathbf x(\mathsf B') = (0,1)^\top$. The state weighting is $\mu(s) = \tfrac13$ for all $s$.
--
--   Each MRP is an MDP with a single action, and its only policy chooses that action with probability one.
--
--   Both processes generate the same distribution of observable data (features and rewards), which is what makes them a counterexample to the learnability of the Bellman error. To state this, the item also defines the left MRP's stationary distribution $\mu_1(\mathsf A) = \tfrac13$, $\mu_1(\mathsf B) = \tfrac23$, and the **probability of an observed data prefix**: for an MRP started in $S_0\sim\mu$, the probability that
--   $$
--   \mathbf x(S_0) = o_0,\; R_1 = r_1,\; \mathbf x(S_1) = o_1,\; \dots,\; R_n = r_n,\; \mathbf x(S_n) = o_n ,
--   $$
--   computed by the forward recursion $\alpha_0(s) = \mu(s)\,\mathbb 1[\mathbf x(s) = o_0]$, $\alpha_k(s') = \mathbb 1[\mathbf x(s') = o_k]\sum_s \alpha_{k-1}(s)\,p(s', r_k\mid s)$, and $\sum_s \alpha_n(s)$.
--
--   **Formalization Note** States are `Fin 2` ($0=\mathsf A$, $1=\mathsf B$) and `Fin 3` ($0=\mathsf A$, $1=\mathsf B$, $2=\mathsf B'$); the single action is `Unit`. The figure was read on the page image (p. 276); the text's description ("A followed by a 0, then some number of apparent Bs, each followed by a −1 except the last, which is followed by a 1") agrees with it. The agent observes the feature vector of each state (all it can see of it) and each reward; the data distribution is that of the process started from its stationary distribution (the book's "equal time is spent in all three states"), described by its finite prefixes.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Example 11.4 (figure and text), p. 276

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_MDP

namespace SuttonBartoRL.OffPolicy

/-- The only policy of a Markov reward process (an MDP with the single action `()`, p. 274,
footnote 3): `π(() | s) = 1`. -/
def mrpPolicy (S : Type) : SuttonBartoRL.FiniteMDP.Policy S Unit where
  prob _ _ := 1
  nonneg _ _ := zero_le_one
  sum_one _ := by simp

/-- Example 11.4, p. 276, left MRP (transcribed from the figure; each two-edge state takes both
edges with probability 1/2). States `0 = A`, `1 = B`, rewards `{−1, 0, 1}`:
`A → B` with reward `0` (probability 1); `B → A` with reward `1` and `B → B` with reward `−1`,
each with probability 1/2. -/
noncomputable def beMRP1 : MDP (Fin 2) Unit where
  R := {-1, 0, 1}
  p s _ s' r :=
    if s = 0 ∧ s' = 1 ∧ r = 0 then 1
    else if s = 1 ∧ s' = 0 ∧ r = 1 then 1 / 2
    else if s = 1 ∧ s' = 1 ∧ r = -1 then 1 / 2
    else 0
  p_nonneg s _ s' r := by split_ifs <;> norm_num
  p_sum s _ := by
    fin_cases s
    · simp [Fin.sum_univ_two, Finset.filter_insert]
    · simp [Fin.sum_univ_two]
      norm_num

/-- Example 11.4, p. 276, right MRP (transcribed from the figure). States `0 = A`, `1 = B`,
`2 = B′`, rewards `{−1, 0, 1}`: `A → B` and `A → B′`, each with reward `0` and probability 1/2;
`B → A` with reward `1` (probability 1); `B′ → B` and `B′ → B′`, each with reward `−1` and
probability 1/2. -/
noncomputable def beMRP2 : MDP (Fin 3) Unit where
  R := {-1, 0, 1}
  p s _ s' r :=
    if s = 0 ∧ s' = 1 ∧ r = 0 then 1 / 2
    else if s = 0 ∧ s' = 2 ∧ r = 0 then 1 / 2
    else if s = 1 ∧ s' = 0 ∧ r = 1 then 1
    else if s = 2 ∧ s' = 1 ∧ r = -1 then 1 / 2
    else if s = 2 ∧ s' = 2 ∧ r = -1 then 1 / 2
    else 0
  p_nonneg s _ s' r := by split_ifs <;> norm_num
  p_sum s _ := by
    fin_cases s <;>
      simp [Fin.sum_univ_three, Finset.filter_insert, Finset.filter_singleton] <;>
      norm_num

/-- Example 11.4, p. 276: features of the left MRP. `w` has two components; `A` is valued by the
first and `B` by the second: `x(A) = (1, 0)`, `x(B) = (0, 1)`. -/
def beFeatures1 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 1]

/-- Example 11.4, p. 276: features of the right MRP. `B` and `B′` look the same and share the
second component: `x(A) = (1, 0)`, `x(B) = x(B′) = (0, 1)`. -/
def beFeatures2 : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, 0; 0, 1; 0, 1]

/-- Example 11.4, p. 276: "equal time is spent in all three states, so we can take µ(s) = 1/3". -/
noncomputable def beMu2 : Fin 3 → ℝ :=
  fun _ => 1 / 3

/-- Example 11.4, p. 276: the stationary distribution of the left MRP, `µ(A) = 1/3`, `µ(B) = 2/3`
(the book gives none for it; it is the long-run fraction of time in each state). -/
noncomputable def beMu1 : Fin 2 → ℝ :=
  ![1 / 3, 2 / 3]

open Classical in
/-- Example 11.4, p. 276, "the observable data distribution": for a Markov reward process `M` started
in `S_0 ∼ µ`, with observations `x(S_t)` (the feature vectors, all the agent sees of a state), the
probability that the observed data begin `x(S_0) = o₀, R_1 = r_1, x(S_1) = o_1, …, R_n = r_n,
x(S_n) = o_n`, where `l = [(r_1, o_1), …, (r_n, o_n)]`. Computed by the forward recursion
`α_0(s) = µ(s)𝟙[x(s) = o₀]`, `α_{k}(s') = 𝟙[x(s') = o_k] Σ_s α_{k−1}(s) p(s', r_k | s)`,
probability `Σ_s α_n(s)`. -/
noncomputable def obsProb {S : Type} [Fintype S] (M : MDP S Unit) (μ : S → ℝ)
    (x : S → Fin 2 → ℝ) (o₀ : Fin 2 → ℝ) (l : List (ℝ × (Fin 2 → ℝ))) : ℝ :=
  ∑ s, (l.foldl
    (fun (α : S → ℝ) (ro : ℝ × (Fin 2 → ℝ)) (s' : S) =>
      if x s' = ro.2 then ∑ s, α s * M.p s () s' ro.1 else 0)
    (fun s => if x s = o₀ then μ s else 0)) s

end SuttonBartoRL.OffPolicy


