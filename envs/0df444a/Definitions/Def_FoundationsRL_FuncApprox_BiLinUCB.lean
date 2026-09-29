-- Prove2me | Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB
-- name    : FoundationsRL_FuncApprox_BiLinUCB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:27:33.401975+00:00
-- url     : https://prove2.me/theorems/1bcbb7c7-d5ce-4005-8652-a1b96b2a9925
-- title:
--   The BiLinUCB algorithm
-- statement:
--   This file defines the BiLinUCB algorithm (Foster & Rakhlin, arXiv:2312.16730v1, §7.3.1,
--   p. 139–140) for reinforcement learning with a finite value-function class $\mathcal Q$,
--   realized here as a finite type `Qc` together with an evaluation map
--   $\mathrm{qeval} : \mathrm{Qc} \to (h,s,a) \mapsto Q_h(s,a)$.
--
--   BiLinUCB proceeds in $K$ iterations of $n$ episodes each. At the start of iteration $k$
--   (having observed $k$ prior iterations of data), it forms the confidence set
--   $$
--   \mathcal Q_{k} = \Big\{ Q \in \mathcal Q : \sum_{i<k} \big(\hat E^i_h(Q)\big)^2 \le \beta
--   \ \ \forall h \Big\},
--   $$
--   where $\hat E^i_h(Q)$ is the empirical Bellman residual of $Q$ estimated from batch $i$'s
--   $n$ realized episodes; picks the optimistic value function
--   $Q_k = \arg\max_{Q \in \mathcal Q_k} \mathbb E_{s_1\sim d_1}[Q_1(s_1,\pi_Q(s_1))]$ and plays
--   its greedy policy $\pi_k = \pi_{Q_k}$ for the iteration's $n$ episodes; and finally outputs
--   the policy $\hat\pi = \pi_{\hat k}$ for the iteration $\hat k$ with the largest empirical
--   return $\hat V^k$.
--
--   This file builds the whole random process — batches, the residual estimator, the
--   confidence set, the optimistic value function, the per-iteration policy, and the final
--   output policy — as functions of the realized episode history, reusing the
--   `Trajectory`/`Learner`/`probEvent` machinery of `RLBasics.UCBVI` so that BiLinUCB is
--   itself an instance of that `Learner` type.
--
--   **Formalization Note** As in `FuncApprox.Core`'s Bellman residual, every realized
--   per-step reward is taken equal to its conditional mean $R_h(s,a)$, so the residual
--   estimator here is the exact empirical counterpart of the population Bellman residual, not
--   an approximation of it. `bestQ`, `greedyPolicy` and the final-iteration selector break
--   ties via an arbitrary (`Classical.arbitrary`/`getD`) choice, matching the book's
--   unspecified tie-breaking in `arg max`.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 139-140, §7.3.1 (BiLinUCB algorithm)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core

/-!
The BiLinUCB algorithm (Foster & Rakhlin, arXiv:2312.16730v1, §7.3.1, p. 139–140), for a
finite value-function class `Qc` (interpreted via `qeval : Qc → ℕ → S → A → ℝ`), reusing the
published episode/history machinery `Trajectory`, `Learner`, `probEvent`, `stateAt`,
`actionAt`, `nextStateAt`, `detPolicy` from `RLBasics.UCBVI`/`RLBasics.Core`. As in
`bellmanResidual` (`Def_FoundationsRL_FuncApprox_Core`), every realized per-step reward is
taken equal to its conditional mean `M.R h s a`, so BiLinUCB's residual estimator below is the
exact empirical counterpart of `bellmanResidual`, not an approximation of it. -/

open scoped Classical

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ} {Qc : Type*} [Fintype Qc] [Nonempty Qc]

/-- The `i`-th (`0`-indexed) batch of `n` episodes inside a realized history `hist`
(Foster–Rakhlin's iteration index `i+1`, batch members `l = 1,…,n`). -/
def batch (hist : List (Trajectory S A H)) (n i : ℕ) : List (Trajectory S A H) :=
  (hist.drop (i * n)).take n

/-- The greedy action `arg max_a Q_h(s,a)` for the value function `Qf : Qc` evaluated via
`qeval` (Foster–Rakhlin's `π_Q`). -/
noncomputable def greedyPolicy (qeval : Qc → ℕ → S → A → ℝ) (Qf : Qc) (h : ℕ) (s : S) : A :=
  ((Finset.univ : Finset A).toList.argmax (qeval Qf h s)).getD (Classical.arbitrary A)

/-- BiLinUCB's residual estimator `\hat E^i_h(Q)` (Foster–Rakhlin, p. 140), computed from
batch `i`'s `n` realized trajectories, with `Q_{H+1} ≡ 0` imposed at the horizon exactly as in
`bellmanResidual`. -/
noncomputable def residualEst (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ)
    (hist : List (Trajectory S A H)) (n h i : ℕ) (Qf : Qc) : ℝ :=
  (((batch hist n i).map (fun τ =>
      qeval Qf h (stateAt τ h) (actionAt τ h) - M.R h (stateAt τ h) (actionAt τ h) -
        (if h + 1 < H then ⨆ a' : A, qeval Qf (h + 1) (nextStateAt τ h) a' else 0))).sum) /
    (n : ℝ)

/-- BiLinUCB's confidence set `Q_{k+1}` (Foster–Rakhlin, Eq. (7.26), p. 140) after `k`
completed iterations of `n` episodes each. -/
noncomputable def confSet (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ)
    (hist : List (Trajectory S A H)) (n : ℕ) (β : ℝ) (k : ℕ) : Finset Qc :=
  Finset.univ.filter (fun Qf =>
    ∀ h : Fin H, ∑ i ∈ Finset.range k, (residualEst M qeval hist n h.1 i Qf) ^ 2 ≤ β)

/-- The initial-state value `E_{s_1∼d_1}[Q_1(s_1,\pi_Q(s_1))]` (Foster–Rakhlin, p. 139) of a
value function `Qf`, used to pick the optimistic `Q_k`. -/
noncomputable def initValue (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (Qf : Qc) :
    ℝ :=
  ∑ s : S, M.d1 s * qeval Qf 0 s (greedyPolicy qeval Qf 0 s)

/-- BiLinUCB's optimistic value function `Q_k = arg max_{Q∈Q_k} E_{s_1∼d_1}[Q_1(s_1,π_Q(s_1))]`
(Foster–Rakhlin, p. 140), computed from `k` completed iterations of data. -/
noncomputable def bestQ (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ)
    (hist : List (Trajectory S A H)) (n : ℕ) (β : ℝ) (k : ℕ) : Qc :=
  ((confSet M qeval hist n β k).toList.argmax (initValue M qeval)).getD (Classical.arbitrary Qc)

/-- The policy `π_i` BiLinUCB plays at iteration `i` (`0`-indexed), as a function of the full
realized history: the greedy policy for `bestQ` computed from the first `i` completed
iterations of `hist`. -/
noncomputable def iterPolicy (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ)
    (hist : List (Trajectory S A H)) (n : ℕ) (β : ℝ) (i : ℕ) : Policy S A H :=
  detPolicy (greedyPolicy qeval (bestQ M qeval (hist.take (i * n)) n β i))

/-- BiLinUCB as a `Learner` (Foster–Rakhlin, p. 140): at any point inside iteration
`hist.length / n`, play the policy for that iteration, computed from the completed prior
iterations recorded in `hist`. -/
noncomputable def biLinUCBLearner (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ)
    (n : ℕ) (β : ℝ) : Learner S A H :=
  fun hist => iterPolicy M qeval hist n β (hist.length / n)

/-- The empirical average return `\hat V^k` of iteration `k` (Foster–Rakhlin, p. 140). -/
noncomputable def empValue (M : EpisodicMDP S A H) (hist : List (Trajectory S A H)) (n k : ℕ) :
    ℝ :=
  (((batch hist n k).map (fun τ =>
      ∑ h ∈ Finset.range H, M.R h (stateAt τ h) (actionAt τ h))).sum) / (n : ℝ)

/-- BiLinUCB's output policy `\hatπ = π_{\hat k}` for `\hat k = arg max_{k∈[K]} \hat V^k`
(Foster–Rakhlin, p. 140), given the full `K·n`-episode history. -/
noncomputable def biLinUCBOutput (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ)
    (hist : List (Trajectory S A H)) (n : ℕ) (β : ℝ) (K : ℕ) : Policy S A H :=
  iterPolicy M qeval hist n β (((List.range K).argmax (empValue M hist n)).getD 0)

end FoundationsRL.FuncApprox


