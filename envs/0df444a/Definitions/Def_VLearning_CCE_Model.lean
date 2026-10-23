-- Prove2me | Definitions.Def_VLearning_CCE_Model
-- name    : VLearning_CCE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:54.908002+00:00
-- url     : https://prove2.me/theorems/6e8c1046-866b-42d9-9814-997882b2d775
-- title:
--   Algorithms 1, 3, 4, (10)–(11), pp. 7–22 — the V-learning run, its training law, the correlated output policy π̂ and the best-response values
-- statement:
--   Fix a Markov game, one bandit rule per player $j$ on $A_j$ arms, bonuses $\beta_{j,t}$, and a number $K$ of episodes.
--
--   **V-learning (Algorithm 1).** Each player $j$ keeps, for each step $h$ and state $s$, a visit counter $N_h(s)$, values $\tilde V_{j,h}(s)$ and $V_{j,h}(s)$ (both initialized to $H+1-h$), and a policy $\pi_{j,h}(\cdot\mid s)$ produced by its $(s,h)$-th bandit. In episode $k$, at step $h$ with state $s_h$ and joint action $\boldsymbol a_h$, with $t=N_h(s_h)+1$,
--   $$\tilde V_{j,h}(s_h)\leftarrow(1-\alpha_t)\tilde V_{j,h}(s_h)+\alpha_t\big(r_{j,h}(s_h,\boldsymbol a_h)+V_{j,h+1}(s_{h+1})+\beta_{j,t}\big),\qquad V_{j,h}(s_h)\leftarrow\min\{H+1-h,\tilde V_{j,h}(s_h)\},$$
--   and the $(s_h,h)$-th bandit of player $j$ receives the action $a_{j,h}$ and the loss $(H-r_{j,h}-V_{j,h+1}(s_{h+1}))/H$. The analysis-only pessimistic values (10)–(11) are $\underline{\tilde V}^k_{j,h}(s)=\sum_{i=1}^t\alpha^i_t[r_{j,h}(s,\boldsymbol a^{k^i}_h)+\underline V^{k^i}_{j,h+1}(s^{k^i}_{h+1})-\beta_{j,i}]$ and $\underline V^k_{j,h}(s)=\max\{0,\underline{\tilde V}^k_{j,h}(s)\}$. The state at the beginning of episode $k$ (counters, values, visit episodes $k^1<\dots<k^t$, bandit histories) is a function of the episodes played before $k$.
--
--   **Training law.** The probability of a sequence of $K$ episodes is the product of the transition probabilities (each episode starts at $s_1$) and of every player's policy probability of its own action; $\mathbb P(E)$ is the sum of these weights over the sequences in $E$.
--
--   **Output policy (Algorithms 3, 4; §5.1).** From step $h$ with index $k$ at state $s$, with $t=N^k_h(s)$: draw $i\in[t]$ with probability $\alpha^i_t$, set $k\leftarrow k^i$, and let every player act by $\pi^{k}_{h}(\cdot\mid s)$; the index $i$ is shared by all players. $V^{\hat\pi^k_h}_{j,h}(s)$ is player $j$'s expected reward from step $h$. At step 1, $k$ is uniform on $[K]$: $V^{\hat\pi}_{j,1}(s_1)=\frac1K\sum_k V^{\hat\pi^k_1}_{j,1}(s_1)$.
--
--   **Best response.** $V^{\dagger,\hat\pi^k_{-j,h}}_{j,h}(s)$ is the supremum, over deterministic policies of player $j$ that see the history of states and joint actions since step $h$, of player $j$'s expected reward when the others play $\hat\pi^k_{-j,h}$. At step 1 the deviation does not see $k$:
--   $$V^{\dagger,\hat\pi_{-j}}_{j,1}(s_1)=\sup_\mu \frac1K\sum_{k=1}^K V^{\mu\times\hat\pi^k_{-j,1}}_{j,1}(s_1).$$
--
--   Also defined: $\iota=\log(mHSAK/\delta)$, the bonus scale $H\xi(B,t,\iota)+\sqrt{H^3\iota/t}$, $n^k_h=N^k_h(s^k_h)$, and $\delta^k_h=\max_j(V^k_{j,h}-\underline V^k_{j,h})(s^k_h)$ with $\delta^k_{H+1}=0$.
--
--   **Formalization Note** Steps and episodes are 0-based. $\tilde V$ is initialized to $H+1-h$ (the page leaves it implicit; (9) at $t=0$ forces it). $\underline{\tilde V}$ is computed by the same incremental update from $0$, which equals the weighted sum (10). When $s$ has not been visited at step $h$ before episode $k$ ($t=0$), the output policy keeps $k$ and plays $\pi^k_h(\cdot\mid s)$, the uniform initial policy. The best-response supremum is over deterministic history-dependent policies (the best response is attained at deterministic policies, p. 5); under the standing assumptions and valid rules the family is bounded by $H$.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 5 (policies, (1), best response); p. 7, Algorithm 1, (2); p. 8, Algorithm 3, §3.2; p. 10, §5.1; p. 18, Algorithm 4, Π_h; p. 22, (10)–(11); pp. 22–23 (δ^k_h, n^k_h); p. 11, Theorem 6 (ι)

import Mathlib
import Definitions.Def_VLearning_CCE_MarkovGame
import Definitions.Def_VLearning_CCE_WeightedBandit

namespace VLearning.CCE

open Classical

/-- One episode of play: the state `s_h` and the joint action `a_h` of every (0-based) step. -/
abbrev Episode (G : Game) : Type := Fin G.H → Fin G.S × G.JointAct

/-- What V-learning (Algorithm 1, p. 7) maintains at the beginning of an episode, for a run of
`K` episodes (0-based `Fin K`; the paper's episode `k` is `k.val + 1`):
* `visits h s`: the episodes `k^1 < ⋯ < k^t` in which `s` was visited at step `h`, oldest first,
  so that `N_h(s) = t` is its length;
* `vTildeUp j h s`, `vUp j h s`: player `j`'s `Ṽ_h(s)` and `V_h(s)`;
* `vTildeLow j h s`, `vLow j h s`: the analysis-only pessimistic `Ṽ̲_h(s)`, `V̲_h(s)` of (10)–(11), p. 22;
* `hist j h s`: the feedback `(a_{j,h}, (H − r_{j,h} − V_{j,h+1}(s_{h+1}))/H)` fed so far to player
  `j`'s `(s, h)`-th adversarial bandit, oldest first. -/
structure RunState (G : Game) (K : ℕ) where
  visits : Fin G.H → Fin G.S → List (Fin K)
  vTildeUp : Fin G.m → Fin G.H → Fin G.S → ℝ
  vUp : Fin G.m → Fin G.H → Fin G.S → ℝ
  vTildeLow : Fin G.m → Fin G.H → Fin G.S → ℝ
  vLow : Fin G.m → Fin G.H → Fin G.S → ℝ
  hist : (j : Fin G.m) → Fin G.H → Fin G.S → List (Fin (G.A j) × ℝ)

namespace RunState

variable {G : Game} {K : ℕ}

/-- The visit counter `N_h(s)`. -/
def N (σ : RunState G K) (h : Fin G.H) (s : Fin G.S) : ℕ := (σ.visits h s).length

/-- Initialization (Algorithm 1, line 1): `N = 0`, `Ṽ_h(s) = V_h(s) = H + 1 − h` (in 0-based steps
`H − h`), `Ṽ̲ = V̲ = 0`, and empty bandit histories (so every policy is uniform). -/
def init (G : Game) (K : ℕ) : RunState G K where
  visits _ _ := []
  vTildeUp _ h _ := (G.H : ℝ) - h.val
  vUp _ h _ := (G.H : ℝ) - h.val
  vTildeLow _ _ _ := 0
  vLow _ _ _ := 0
  hist _ _ _ := []

/-- `V_{j,h+1}(s')`, with `V_{j,H+1} ≡ 0` at the last step. -/
def vUpNext (σ : RunState G K) (j : Fin G.m) (h : Fin G.H) (s' : Fin G.S) : ℝ :=
  if hh : h.val + 1 < G.H then σ.vUp j ⟨h.val + 1, hh⟩ s' else 0

/-- `V̲_{j,h+1}(s')`, with `V̲_{j,H+1} ≡ 0` at the last step. -/
def vLowNext (σ : RunState G K) (j : Fin G.m) (h : Fin G.H) (s' : Fin G.S) : ℝ :=
  if hh : h.val + 1 < G.H then σ.vLow j ⟨h.val + 1, hh⟩ s' else 0

/-- `V_{j,h+1}(s_{h+1})` along an episode `e` (`0` at the last step). -/
def vUpAfter (σ : RunState G K) (j : Fin G.m) (e : Episode G) (h : Fin G.H) : ℝ :=
  if hh : h.val + 1 < G.H then σ.vUp j ⟨h.val + 1, hh⟩ (e ⟨h.val + 1, hh⟩).1 else 0

/-- `V̲_{j,h+1}(s_{h+1})` along an episode `e` (`0` at the last step). -/
def vLowAfter (σ : RunState G K) (j : Fin G.m) (e : Episode G) (h : Fin G.H) : ℝ :=
  if hh : h.val + 1 < G.H then σ.vLow j ⟨h.val + 1, hh⟩ (e ⟨h.val + 1, hh⟩).1 else 0

/-- Player `j`'s policy `π_{j,h}(· | s) = ADV_BANDIT_UPDATE(history)` (Algorithm 1, line 9). -/
def policy (alg : ∀ j, BanditRule (G.A j)) (σ : RunState G K) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) : Fin (G.A j) → ℝ :=
  alg j (σ.hist j h s)

/-- `𝔻_{π_h}`: probability of the joint action `a` at `(s, h)` when every player follows its own
policy independently. -/
noncomputable def jointProb (alg : ∀ j, BanditRule (G.A j)) (σ : RunState G K) (h : Fin G.H)
    (s : Fin G.S) (a : G.JointAct) : ℝ :=
  ∏ j, σ.policy alg j h s (a j)

/-- `𝔻_{b × π_{−j,h}}`: probability of the joint action `a` at `(s, h)` when player `j` plays the
action `b` and the other players follow their policies. -/
noncomputable def devProb (alg : ∀ j, BanditRule (G.A j)) (σ : RunState G K) (j : Fin G.m)
    (b : Fin (G.A j)) (h : Fin G.H) (s : Fin G.S) (a : G.JointAct) : ℝ :=
  ∏ j', if j' = j then (if a j = b then 1 else 0) else σ.policy alg j' h s (a j')

/-- `(r_{j,h} + ℙ_h V_{j,h+1})(s, a)` for the value `V` held in the state `σ`. -/
noncomputable def qUp (σ : RunState G K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S)
    (a : G.JointAct) : ℝ :=
  G.r j h s a + ∑ s', G.P h s a s' * σ.vUpNext j h s'

end RunState

open RunState

/-- One episode of Algorithm 1 for every player, from the state `σ` at the beginning of
episode `k`, along the episode `e`. At the visited pair `(s_h, h)`, with `t = N_h(s_h) + 1`:
* `Ṽ ← (1 − α_t) Ṽ + α_t (r + V_{h+1}(s_{h+1}) + β_{j,t})`, `V ← min{H + 1 − h, Ṽ}` (lines 6–8, (2));
* `Ṽ̲ ← (1 − α_t) Ṽ̲ + α_t (r + V̲_{h+1}(s_{h+1}) − β_{j,t})`, `V̲ ← max{0, Ṽ̲}` (the recursive form of
  (10)–(11): starting from `0`, it equals the weighted sum (10));
* the bandit history receives `(a_{j,h}, (H − r − V_{h+1}(s_{h+1}))/H)` (line 9).
`V_{h+1}` is read from `σ`: step `h + 1` is updated after step `h` within the episode. -/
noncomputable def episodeUpdate (G : Game) (β : Fin G.m → ℕ → ℝ) {K : ℕ} (σ : RunState G K)
    (k : Fin K) (e : Episode G) : RunState G K :=
  let t : Fin G.H → Fin G.S → ℕ := fun h s => σ.N h s + 1
  let vt : Fin G.m → Fin G.H → Fin G.S → ℝ := fun j h s =>
    (1 - lr G.H (t h s)) * σ.vTildeUp j h s +
      lr G.H (t h s) * (G.r j h s (e h).2 + σ.vUpAfter j e h + β j (t h s))
  let vtl : Fin G.m → Fin G.H → Fin G.S → ℝ := fun j h s =>
    (1 - lr G.H (t h s)) * σ.vTildeLow j h s +
      lr G.H (t h s) * (G.r j h s (e h).2 + σ.vLowAfter j e h - β j (t h s))
  { visits := fun h s => if (e h).1 = s then σ.visits h s ++ [k] else σ.visits h s
    vTildeUp := fun j h s => if (e h).1 = s then vt j h s else σ.vTildeUp j h s
    vUp := fun j h s => if (e h).1 = s then min ((G.H : ℝ) - h.val) (vt j h s) else σ.vUp j h s
    vTildeLow := fun j h s => if (e h).1 = s then vtl j h s else σ.vTildeLow j h s
    vLow := fun j h s => if (e h).1 = s then max 0 (vtl j h s) else σ.vLow j h s
    hist := fun j h s => if (e h).1 = s then
        σ.hist j h s ++ [((e h).2 j, ((G.H : ℝ) - G.r j h s (e h).2 - σ.vUpAfter j e h) / G.H)]
      else σ.hist j h s }

/-- `runState τ k`: the V-learning state at the beginning of (0-based) episode `k` of the run
whose episodes are `τ` (`V^k, N^k, π^k`, p. 8, with `k` 0-based). -/
noncomputable def runState (G : Game) (β : Fin G.m → ℕ → ℝ) {K : ℕ} (τ : Fin K → Episode G) :
    ℕ → RunState G K
  | 0 => RunState.init G K
  | k + 1 =>
    if hk : k < K then episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩)
    else runState G β τ k

/-- The probability of reaching the state of step `h` of episode `k`: `𝟙{s_1 = G.s1}` at the
first step, `ℙ_{h−1}(s_h | s_{h−1}, a_{h−1})` afterwards. -/
noncomputable def stepProb (G : Game) {K : ℕ} (τ : Fin K → Episode G) (k : Fin K)
    (h : Fin G.H) : ℝ :=
  if hh : h.val = 0 then (if (τ k h).1 = G.s1 then 1 else 0)
  else G.P ⟨h.val - 1, by omega⟩ (τ k ⟨h.val - 1, by omega⟩).1 (τ k ⟨h.val - 1, by omega⟩).2
    (τ k h).1

/-- The probability that the `K`-episode training run of V-learning produces the episodes `τ`:
the product, over episodes and steps, of the transition probabilities and of every player's
policy probability of its own action. -/
noncomputable def traceWeight (G : Game) (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ)
    {K : ℕ} (τ : Fin K → Episode G) : ℝ :=
  ∏ k : Fin K, ∏ h : Fin G.H,
    stepProb G τ k h * jointProb alg (runState G β τ k.val) h (τ k h).1 (τ k h).2

/-- The probability, over the training run of `K` episodes, of an event `E` on the episodes. -/
noncomputable def trainProb (G : Game) (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ)
    (K : ℕ) (E : (Fin K → Episode G) → Prop) : ℝ :=
  ∑ τ : Fin K → Episode G, traceWeight G alg β τ * (if E τ then 1 else 0)

/-- `V^{π̂^k_h}_{j,h}(s)`: player `j`'s expected reward from step `h` (0-based, as a natural number;
`0` once `h ≥ H`) under the correlated output policy started at step `h` with index `k`
(Algorithm 4, p. 18, with the index `i` shared by all players, §5.1, p. 10). With
`t = N^k_h(s)` and visit episodes `k^1, …, k^t`, the index `i ∈ [t]` is drawn with probability
`α^i_t`, `k ← k^i`, and every player plays `π^{k^i}_h(· | s)`. If `t = 0`, the weight `α^0_0 = 1`
keeps `k` and the players play `π^k_h(· | s)` (the uniform initial policy). -/
noncomputable def outVal (G : Game) (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ)
    {K : ℕ} (τ : Fin K → Episode G) (j : Fin G.m) (h : ℕ) (k : Fin K) (s : Fin G.S) : ℝ :=
  if hh : h < G.H then
    let vis := (runState G β τ k.val).visits ⟨h, hh⟩ s
    let F : Fin K → ℝ := fun k' =>
      ∑ a : G.JointAct, jointProb alg (runState G β τ k'.val) ⟨h, hh⟩ s a *
        (G.r j ⟨h, hh⟩ s a + ∑ s', G.P ⟨h, hh⟩ s a s' * outVal G alg β τ j (h + 1) k' s')
    lrW G.H vis.length 0 * F k +
      ∑ i : Fin vis.length, lrW G.H vis.length (i.val + 1) * F (vis.get i)
  else 0
termination_by G.H - h

/-- A deterministic history-dependent policy of player `j` started at some step: the action as
a function of the history of states and joint actions since that step, and of the current
state (`Π_h`, p. 18; histories include the other players' actions, footnote 3, p. 4). -/
abbrev DevPolicy (G : Game) (j : Fin G.m) : Type :=
  List (Fin G.S × G.JointAct) → Fin G.S → Fin (G.A j)

/-- Player `j`'s expected reward from step `h` when it plays the deviation `μ` (having seen the
history `hist` since the start step) and the other players play `π̂^k_{−j,h}` — the correlated
output policy with shared index, as in `outVal`, with player `j`'s factor replaced by `μ`. -/
noncomputable def brW (G : Game) (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ)
    {K : ℕ} (τ : Fin K → Episode G) (j : Fin G.m) (μ : DevPolicy G j) (h : ℕ) (k : Fin K)
    (hist : List (Fin G.S × G.JointAct)) (s : Fin G.S) : ℝ :=
  if hh : h < G.H then
    let vis := (runState G β τ k.val).visits ⟨h, hh⟩ s
    let F : Fin K → ℝ := fun k' =>
      ∑ a : G.JointAct, devProb alg (runState G β τ k'.val) j (μ hist s) ⟨h, hh⟩ s a *
        (G.r j ⟨h, hh⟩ s a +
          ∑ s', G.P ⟨h, hh⟩ s a s' * brW G alg β τ j μ (h + 1) k' (hist ++ [(s, a)]) s')
    lrW G.H vis.length 0 * F k +
      ∑ i : Fin vis.length, lrW G.H vis.length (i.val + 1) * F (vis.get i)
  else 0
termination_by G.H - h

/-- `V^{†, π̂^k_{−j,h}}_{j,h}(s)` (p. 18): the best value player `j` can obtain from step `h`
against `π̂^k_{−j,h}`. It is the supremum over deterministic history-dependent deviations (the best
response is attained at deterministic policies, p. 5); under the standing assumptions and valid
bandit rules the family is bounded by `H`. -/
noncomputable def brValFrom (G : Game) (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ)
    {K : ℕ} (τ : Fin K → Episode G) (j : Fin G.m) (h : ℕ) (k : Fin K) (s : Fin G.S) : ℝ :=
  ⨆ μ : DevPolicy G j, brW G alg β τ j μ h k [] s

/-- `V^{π̂}_{j,1}(s_1)`: the output policy of Algorithm 3 draws `k` uniformly from `[K]`. -/
noncomputable def outValTop (G : Game) (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ)
    {K : ℕ} (τ : Fin K → Episode G) (j : Fin G.m) : ℝ :=
  (1 / (K : ℝ)) * ∑ k : Fin K, outVal G alg β τ j 0 k G.s1

/-- `V^{†, π̂_{−j}}_{j,1}(s_1)`: the best response does not see the latent index `k`, so the
supremum over deviations is taken **outside** the average over the uniform initial `k`. -/
noncomputable def brValTop (G : Game) (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ)
    {K : ℕ} (τ : Fin K → Episode G) (j : Fin G.m) : ℝ :=
  ⨆ μ : DevPolicy G j, (1 / (K : ℝ)) * ∑ k : Fin K, brW G alg β τ j μ 0 k [] G.s1

/-- `n^k_h = N^k_h(s^k_h)`: visits of the state of step `h` of episode `k`, before episode `k`. -/
noncomputable def visitCount (G : Game) (β : Fin G.m → ℕ → ℝ) {K : ℕ} (τ : Fin K → Episode G)
    (k : Fin K) (h : Fin G.H) : ℕ :=
  (runState G β τ k.val).N h (τ k h).1

/-- `δ^k_h = max_j (V^k_{j,h} − V̲^k_{j,h})(s^k_h)` (proof of Theorem 6, p. 22), for a 0-based
step `h`; `δ^k_{H+1} = 0`. -/
noncomputable def gapAt (G : Game) (β : Fin G.m → ℕ → ℝ) {K : ℕ} (τ : Fin K → Episode G)
    (k : Fin K) (h : ℕ) : ℝ :=
  if hh : h < G.H then
    ⨆ j : Fin G.m, ((runState G β τ k.val).vUp j ⟨h, hh⟩ (τ k ⟨h, hh⟩).1 -
      (runState G β τ k.val).vLow j ⟨h, hh⟩ (τ k ⟨h, hh⟩).1)
  else 0

/-- `ι = log(mHSAK/δ)` (Theorem 6, p. 11), with `A = max_j A_j`. -/
noncomputable def iota (G : Game) (K : ℕ) (δ : ℝ) : ℝ :=
  Real.log ((G.m : ℝ) * G.H * G.S * G.Amax * K / δ)

/-- The bonus scale `Hξ(B, t, ι) + √(H³ι/t)` of Theorem 6 (used for `t ≥ 1` only). -/
noncomputable def bonusScale (G : Game) (ξ : ℕ → ℕ → ℝ → ℝ) (B : ℕ) (ι : ℝ) (t : ℕ) : ℝ :=
  (G.H : ℝ) * ξ B t ι + Real.sqrt ((G.H : ℝ) ^ 3 * ι / t)

end VLearning.CCE


