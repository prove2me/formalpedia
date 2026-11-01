-- Prove2me | Definitions.Def_TimeVaryingGames_StageGames
-- name    : TimeVaryingGames_StageGames
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:16.154182+00:00
-- url     : https://prove2.me/theorems/3f42d584-9b00-4c29-a0de-d58f15d059d0
-- title:
--   Assumption 1 on the stage games and the stabilization gap $R_{i,t}$
-- statement:
--   A **time-varying game** is a sequence of stage games $\mathcal G_t$, $t=1,2,\dots$, on the same players and action sets $\mathcal K_i$, with stage payoffs $u_{i,t}$ and stage payoff gradients $v_{i,t}(x)=\nabla_{x_i}u_{i,t}(x)$.
--
--   1. **Assumption 1.** Every stage payoff is $C^2$ on an open neighbourhood of $\mathcal K$, and there are constants $G_i,L_i>0$ with
--   $$\|v_{i,t}(x)\|_*\le G_i,\qquad \|v_{i,t}(x')-v_{i,t}(x)\|_*\le L_i\|x'-x\|$$
--   for all $t$, all players $i$ and all $x,x'\in\mathcal K$, where $\|x\|^2=\sum_i\|x_i\|^2$.
--   2. Given a limit game with payoff gradients $v_i$, the **stabilization gap** is
--   $$R_{i,t}=\max_{x\in\mathcal K}\|v_{i,t}(x)-v_i(x)\|_*,$$
--   and the stage games **converge** to the limit game if $R_{i,t}\to0$ for every player $i$.
--
--   Assumption 1 is the only standing assumption on the stage games; $R_{i,t}$ measures how far the stage game is from the limit game and enters the step-size condition (S3).
--
--   **Formalization Note** The open neighbourhood may depend on the stage. The profile norm $\sqrt{\sum_j\|x'_j-x_j\|^2}$ is written out because Lean's product norm is the sup norm. The maximum is a real supremum over the nonempty set of profiles; under the hypotheses of every statement using it the function is bounded, so it is the paper's maximum.
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Assumption 1 and eqs. (4a)–(4b), p.5; eqs. (17)–(18), p.9

import Mathlib
import Definitions.Def_TimeVaryingGames_ContinuousGame

namespace TimeVaryingGames

/-- **Assumption 1** on the sequence of stage games `G_t`.
arXiv:1809.03066v3, §3.1, p.5: "Assumption 1. The game's payoff functions are C²-smooth; in
particular, there exist constants G_i, L_i > 0 such that ‖v_{i,t}(x)‖_* ≤ G_i (4a)
‖v_{i,t}(x') − v_{i,t}(x)‖_* ≤ L_i‖x' − x‖ (4b) for all t = 1, 2, . . . , and all i ∈ N,
x, x' ∈ K."

`Assumption1 K U uStage G L`: for every stage `t` (Lean's `t : ℕ` is the paper's stage `t + 1`),
the stage payoffs `uStage t i` are `C²` on an open set `U t` containing the action space, and
the stage payoff gradients `v_{i,t} = partialGradient (uStage t) i` satisfy (4a) and (4b) on the
action space.

**Formalization Note.**
* The paper tacitly takes each payoff on an open neighbourhood of `K` (§2.2, p.4); the
  neighbourhood `U t` is explicit and may depend on the stage.
* The norm on profiles in (4b) is the paper's `‖x‖² = Σ_i ‖x_i‖²` (p.4), written out, since
  Lean's norm on a product is the sup norm. -/
def Assumption1 {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (K : ∀ i, Set (E i)) (U : ℕ → Set (∀ j, E j)) (uStage : ℕ → ι → (∀ j, E j) → ℝ)
    (G L : ι → ℝ) : Prop :=
  (∀ t, IsOpen (U t) ∧ profiles K ⊆ U t ∧ ∀ i, ContDiffOn ℝ 2 (uStage t i) (U t)) ∧
  (∀ i, 0 < G i ∧ 0 < L i) ∧
  (∀ t i, ∀ x ∈ profiles K, ‖partialGradient (uStage t) i x‖ ≤ G i) ∧
  (∀ t i, ∀ x ∈ profiles K, ∀ x' ∈ profiles K,
    ‖partialGradient (uStage t) i x' - partialGradient (uStage t) i x‖ ≤
      L i * Real.sqrt (∑ j, ‖x' j - x j‖ ^ 2))

/-- **Stabilization gap** `R_{i,t} = max_{x∈K} ‖v_{i,t}(x) − v_i(x)‖_*`.
arXiv:1809.03066v3, §4.1, p.9, eq. (17): "R_{i,t} = max_{x∈K} ‖v_{i,t}(x) − v_i(x)‖_*", and (18):
"the sequence of games G_t, t = 1, 2, . . . , converges to G if lim_{t→∞} R_{i,t} = 0 for all
i ∈ N."

**Formalization Note.** The maximum is a real supremum over the subtype of action profiles. In
every statement using it the action sets are nonempty and the function is bounded on them (the
stage gradients by (4a), the limit gradient by continuity on the compact `K`), so the supremum is
the paper's maximum and not a junk value. -/
noncomputable def stabilizationGap {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (K : ∀ i, Set (E i)) (uStage : ℕ → ι → (∀ j, E j) → ℝ) (uLim : ι → (∀ j, E j) → ℝ)
    (i : ι) (t : ℕ) : ℝ :=
  ⨆ x : profiles K, ‖partialGradient (uStage t) i x - partialGradient uLim i x‖

end TimeVaryingGames


