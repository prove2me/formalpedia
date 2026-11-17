-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg4Process
-- name    : IntroDelayAMDP_Supplement_alg4Process
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:41:54.028376+00:00
-- url     : https://prove2.me/theorems/22a01f93-9cef-4bd1-835f-fab90e619005
-- title:
--   Algorithm 4 — processing one episode (lines 4–17)
-- statement:
--   This is the processing step of **Algorithm 4** (policy optimization with GRR for tabular AMDPs with delayed feedback). Episode $\kappa$ is processed at the end of episode $\kappa+\min\{d_\kappa,\bar d\}$, using the policy $\pi_\kappa$ and the trajectory $(s_{\kappa,h},a_{\kappa,h})_h$ stored when it was played. It is **skipped** if $d_\kappa>\bar d$ or $\kappa+d_\kappa>K$.
--
--   1. If $\kappa$ is not skipped: the confidence set $\mathcal P_\kappa$ of Eq. (16) is computed from the trajectories processed so far, $q_\kappa=\min_{P'\in\mathcal P_\kappa}q^{P',\pi_\kappa}$, the bonuses $b_\kappa$ and $B_\kappa$ of Eqs. (17)–(18) are computed, and $-B_\kappa$ is added to the received loss $g_t$ of the current episode $t$.
--   2. Skipped or not: every unfinished GRR estimate started in episode $k$ for a pair $(s,a)\in\mathcal S_h\times\mathcal A$ makes one attempt with $\kappa$: $\hat w_k(s,a)$ increases by $1$ and $g_t(s,a)$ by $L_{k,h}/2$; the attempt is accepted with probability $\min\{1,\alpha_{k,\kappa}\}$ (Eq. (4)); the estimate succeeds if accepted and $(s_{\kappa,h},a_{\kappa,h})=(s,a)$, is otherwise randomly stopped with probability $\gamma$, and finishes on success, stop, or $\hat w_k(s,a)=M$.
--   3. If $\kappa$ is not skipped: each visited pair $(s_{\kappa,h},a_{\kappa,h})$ with $q_\kappa\ge\theta$ and fewer than $\nu$ unfinished estimates starts a GRR estimate that keeps $\pi_\kappa$ and $L_{\kappa,h}$.
--   4. Skipped or not: the transitions of episode $\kappa$ are added to the data of the confidence sets.
--
--   Together with `alg4Step` this is the whole of Algorithm 4; with $\bar d=0$ and no delays it is Algorithm 1 of the base mission.
--
--
--   **Formalization Note** The acceptance and stop events are realized by uniform coins of the base mission's random tape ($u<p$ has probability $p$). Unfinished-estimate counts are taken at the start of the processing of $\kappa$. The state record is the base mission's `AlgState`.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 4, lines 4–17, p.58; App. C.1, p.58

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_AlgParams
import Definitions.Def_IntroDelayAMDP_AlgState
import Definitions.Def_IntroDelayAMDP_EpisodeCoins
import Definitions.Def_IntroDelayAMDP_confSet
import Definitions.Def_IntroDelayAMDP_qLow
import Definitions.Def_IntroDelayAMDP_bonus
import Definitions.Def_IntroDelayAMDP_bonusQ
import Definitions.Def_IntroDelayAMDP_lossToGo
import Definitions.Def_IntroDelayAMDP_accProb

namespace IntroDelayAMDP.Supplement

open Classical in
/-- **Processing one episode in Algorithm 4** (Algorithm 4, lines 4–17, printed p.58, PDF p.60, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530); App. C.1, printed p.58).
Given the state `σ` of the algorithm, the 0-based episode `κ` being processed (its policy
`π_κ = σ.pol κ` and trajectory `τ = σ.traj κ` were stored when it was played), whether `κ` is
skipped, and the coins `c` of episode `κ`, it performs, line by line:
* lines 4–6 (only if `κ` is not skipped): `P_κ = confSet L β σ.obs` from the trajectories processed so
  far (Eq. (16)), `q_κ = min_{P′∈P_κ} q^{P′,π_κ}`, the bonus `b_κ` of (17) and `B_κ` of (18), and
  `g_t ← g_t − B_κ`;
* line 7 / lines 14–16 (only if not skipped): the visited pair `(s_{κ,h}, a_{κ,h})` of each layer starts the
  estimate `(κ, s, a)` with `ŵ = 0`, keeping `π_κ` and `L_{κ,h}`, iff `q_κ(s, a) ≥ θ` and it has fewer
  than `ν` unfinished estimates (`u_κ(s, a) = 0`);
* lines 8–13 (skipped or not): every unfinished estimate `(k, s, a)`, `s` in layer `h`, makes one
  attempt with episode `κ`: `ŵ_k(s, a) ← ŵ_k(s, a) + 1`, `g_t(s, a) ← g_t(s, a) + L_{k,h}/2`; it is accepted
  iff `c.acc k s a < min{1, α_{k,κ}}` with `α_{k,κ}` of (4) for `π_k`, `π_κ` along `κ`'s trajectory up to
  layer `h`; it succeeds iff accepted and `(s_{κ,h}, a_{κ,h}) = (s, a)`; otherwise it is randomly stopped
  iff `c.stop k s a < γ`; it finishes on success, stop or `ŵ_k(s, a) = M`;
* line 17 (skipped or not): the next state after each visited non-last-layer pair of episode `κ` is
  added to the data of the confidence sets, and the visit counts are incremented.
The received loss `g_t` of the current episode `t` is added to `σ.cumG` as each processed episode
contributes; the policy `π_t` was fixed before processing, so this is the same as adding `g_t` at the end
of episode `t`.

**Formalization Note.** Estimate keys `k` range over `0, …, K − 1` (an estimate is started only by a
processed episode `k < K`). The count of unfinished estimates and the attempts are taken at the start
of the processing of `κ` (before its own starts), as on the page. Uniform `u` and the test `u < p`
realize an event of probability `p`. The bookkeeping fields `visits` and `ind` (`I_{k,κ}`) are updated as in
Algorithm 1. -/
noncomputable def alg4Process {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (ℓ : ℕ → St → A → ℝ) (p : AlgParams) (K : ℕ)
    (σ : AlgState St A) (κ : ℕ) (skipped : Prop) (c : EpisodeCoins St A) : AlgState St A :=
  let π : St → A → ℝ := σ.pol κ
  let τ : ℕ → St × A := σ.traj κ
  let cs := confSet L p.beta σ.obs
  let q : St → A → ℝ := qLow L cs π
  let b : St → ℝ := bonus p.c1 p.eta p.theta H π q
  let B : St → A → ℝ := bonusQ L cs π b
  let visited : St → A → Prop := fun s a => τ (L.layer s) = (s, a)
  let succ : ℕ → St → A → Prop := fun k s a =>
    c.acc k s a < min 1 (accProb (σ.pol k) π (fun i : Fin (L.layer s + 1) => τ i)) ∧ visited s a
  let stopped : ℕ → St → A → Prop := fun k s a => ¬ succ k s a ∧ c.stop k s a < p.gamma
  let w' : ℕ → St → A → ℕ := fun k s a => if σ.active k s a then σ.w k s a + 1 else σ.w k s a
  let finished : ℕ → St → A → Prop := fun k s a => succ k s a ∨ stopped k s a ∨ w' k s a = p.M
  let g : St → A → ℝ := fun s a =>
    (if skipped then 0 else -B s a) +
      ∑ k ∈ Finset.range K, if σ.active k s a then σ.piece k s a else 0
  let start : St → A → Prop := fun s a =>
    ¬ skipped ∧ visited s a ∧ p.theta ≤ q s a ∧
      (((Finset.range K).filter (fun k => σ.active k s a)).card : ℝ) < p.nu
  { cumG := fun s a => σ.cumG s a + g s a
    obs := fun s a =>
      if visited s a ∧ L.layer s + 1 < H then σ.obs s a ++ [(τ (L.layer s + 1)).1] else σ.obs s a
    visits := fun s a => if visited s a then σ.visits s a + 1 else σ.visits s a
    pol := σ.pol
    traj := σ.traj
    started := fun k s a => if k = κ then start s a else σ.started k s a
    active := fun k s a => if k = κ then start s a else σ.active k s a ∧ ¬ finished k s a
    w := fun k s a => if k = κ then 0 else w' k s a
    piece := fun k s a =>
      if k = κ then (if start s a then lossToGo (ℓ κ) H τ (L.layer s) / 2 else 0)
      else σ.piece k s a
    ind := fun k κ' s a =>
      if κ' = κ then σ.active k s a ∧ (succ k s a ∨ stopped k s a) else σ.ind k κ' s a }

end IntroDelayAMDP.Supplement


