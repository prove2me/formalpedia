-- Prove2me | Definitions.Def_IntroDelayAMDP_algStep
-- name    : IntroDelayAMDP_algStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:18.538043+00:00
-- url     : https://prove2.me/theorems/485ed339-4141-4157-aa56-3f2287e7f00b
-- title:
--   One episode of Algorithm 1
-- statement:
--   One pass of lines 3–17 of Algorithm 1 on the state before episode $\kappa$:
--
--   1. line 3 sets $\pi_\kappa$ by exponential weights at every state;
--   2. lines 4–6 compute $q_\kappa$, $b_\kappa$, $B_\kappa$ and initialize $g_\kappa=-B_\kappa$;
--   3. line 7 samples the trajectory;
--   4. lines 8–13: every unfinished estimate $(k,s,a)$ with $s$ in layer $h$ makes one attempt. It increments $\hat w_k(s,a)$, adds $L_{k,h}/2$ to $g_\kappa(s,a)$, is accepted with probability $\min\{1,\alpha_{k,\kappa}\}$, succeeds if accepted and $(s_{\kappa,h},a_{\kappa,h})=(s,a)$, is otherwise randomly stopped with probability $\gamma$, and finishes if it succeeds, is stopped, or has $\hat w_k(s,a)=M$;
--   5. lines 14–16 start an estimate for each visited pair with $q_\kappa\ge\theta$ that had fewer than $\nu$ unfinished estimates at the start of the episode;
--   6. line 17 appends the observed next states and updates the visit counts.
--
--   **Formalization Note** A uniform $u$ and the test $u<p$ realize an event of probability $p$. Each pair is visited at most once per episode, so the simultaneous updates commute.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, lines 3–17, p.16; App. A, p.29

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_AlgParams
import Definitions.Def_IntroDelayAMDP_AlgState
import Definitions.Def_IntroDelayAMDP_EpisodeCoins
import Definitions.Def_IntroDelayAMDP_expPolicy
import Definitions.Def_IntroDelayAMDP_confSet
import Definitions.Def_IntroDelayAMDP_qLow
import Definitions.Def_IntroDelayAMDP_bonus
import Definitions.Def_IntroDelayAMDP_bonusQ
import Definitions.Def_IntroDelayAMDP_sampleTraj
import Definitions.Def_IntroDelayAMDP_lossToGo
import Definitions.Def_IntroDelayAMDP_accProb

namespace IntroDelayAMDP

open Classical in
/-- **One episode of Algorithm 1** (Algorithm 1, lines 3–17, printed p.16; the bookkeeping of
App. A, printed p.29, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). Given the state `σ` before the 0-based episode `κ` and the coins
`c` of episode `κ`, it performs, line by line:

* line 3: `π_κ(a | s) ∝ exp(−η ∑_{κ′<κ} g_{κ′}(s, a))` at every state (`expPolicy`);
* line 4: `q_κ = min_{P′∈P_κ} q^{P′,π_κ}` with `P_κ = confSet L β σ.obs`, and the bonus `b_κ` of (17);
* line 5: the bonus Q-function `B_κ` of (18); line 6: `g_κ ← −B_κ`;
* line 7: samples the trajectory `τ = (s_{κ,h}, a_{κ,h})_h` from `c.act`, `c.nxt`; `L_{κ,h}` is the
  loss from step `h` to the end (`lossToGo`);
* lines 8–13: every unfinished estimate `(k, s, a)` (`σ.active`) with `s` in layer `h` makes one
  attempt: `ŵ_k(s, a) ← ŵ_k(s, a) + 1` and `g_κ(s, a) ← g_κ(s, a) + L_{k,h}/2`; the attempt is
  accepted iff `c.acc k s a < min{1, α_{k,κ}}` with `α_{k,κ}` of (4) along `τ` up to layer `h`;
  it succeeds iff accepted and `(s_{κ,h}, a_{κ,h}) = (s, a)`; if it does not succeed it is randomly
  stopped iff `c.stop k s a < γ`; the estimate finishes if it succeeds, is stopped, or has
  `ŵ_k(s, a) = M`; `I_{k,κ}(s, a)` records success or stop;
* lines 14–16: for every layer `h`, the visited pair `(s, a) = (s_{κ,h}, a_{κ,h})` starts the estimate
  `(κ, s, a)` with `ŵ = 0` iff `q_κ(s, a) ≥ θ` and it had fewer than `ν` unfinished estimates at the
  start of episode `κ`;
* line 17: the next state observed after each visited non-last-layer pair is appended to its
  observations, and the visit counts are incremented.

**Formalization Note.** Uniform `u` and the test `u < p` realize an event of probability `p`. A
pair `(s, a)` is visited in the episode iff `τ (layer s) = (s, a)`, so each pair is visited at most
once per episode, and all simultaneous updates of lines 8–17 commute. The estimate `(κ, s, a)`
makes its first attempt in episode `κ + 1`. -/
noncomputable def algStep {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams) (a0 : A)
    (σ : AlgState St A) (κ : ℕ) (c : EpisodeCoins St A) : AlgState St A :=
  let π : St → A → ℝ := expPolicy p.eta σ.cumG
  let cs := confSet L p.beta σ.obs
  let q : St → A → ℝ := qLow L cs π
  let b : St → ℝ := bonus p.c1 p.eta p.theta H π q
  let B : St → A → ℝ := bonusQ L cs π b
  let τ : ℕ → St × A := sampleTraj L P π c.act c.nxt a0
  let visited : St → A → Prop := fun s a => τ (L.layer s) = (s, a)
  let succ : ℕ → St → A → Prop := fun k s a =>
    c.acc k s a < min 1 (accProb (σ.pol k) π (fun i : Fin (L.layer s + 1) => τ i)) ∧ visited s a
  let stopped : ℕ → St → A → Prop := fun k s a => ¬ succ k s a ∧ c.stop k s a < p.gamma
  let w' : ℕ → St → A → ℕ := fun k s a => if σ.active k s a then σ.w k s a + 1 else σ.w k s a
  let finished : ℕ → St → A → Prop := fun k s a => succ k s a ∨ stopped k s a ∨ w' k s a = p.M
  let g : St → A → ℝ := fun s a =>
    -B s a + ∑ k ∈ Finset.range κ, if σ.active k s a then σ.piece k s a else 0
  let start : St → A → Prop := fun s a =>
    visited s a ∧ p.theta ≤ q s a ∧
      (((Finset.range κ).filter (fun k => σ.active k s a)).card : ℝ) < p.nu
  { cumG := fun s a => σ.cumG s a + g s a
    obs := fun s a =>
      if visited s a ∧ L.layer s + 1 < H then σ.obs s a ++ [(τ (L.layer s + 1)).1] else σ.obs s a
    visits := fun s a => if visited s a then σ.visits s a + 1 else σ.visits s a
    pol := fun k => if k = κ then π else σ.pol k
    traj := fun k => if k = κ then τ else σ.traj k
    started := fun k s a => if k = κ then start s a else σ.started k s a
    active := fun k s a => if k = κ then start s a else σ.active k s a ∧ ¬ finished k s a
    w := fun k s a => if k = κ then 0 else w' k s a
    piece := fun k s a =>
      if k = κ then (if start s a then lossToGo (ℓ κ) H τ (L.layer s) / 2 else 0)
      else σ.piece k s a
    ind := fun k κ' s a =>
      if κ' = κ then σ.active k s a ∧ (succ k s a ∨ stopped k s a) else σ.ind k κ' s a }

end IntroDelayAMDP


