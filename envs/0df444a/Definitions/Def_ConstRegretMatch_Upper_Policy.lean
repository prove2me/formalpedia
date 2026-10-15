-- Prove2me | Definitions.Def_ConstRegretMatch_Upper_Policy
-- name    : ConstRegretMatch_Upper_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:01.477189+00:00
-- url     : https://prove2.me/theorems/50d1de54-aadf-4f7b-97dd-ad64a2388bfb
-- title:
--   §2, pp. 8–9 — admissible matching policies, queues Qᵗ, the value 𝓡^{D,t} and the hindsight benchmark 𝓡^{*,t}
-- statement:
--   A **matching policy** is described by its cumulative counts $D^t_m$, the number of times match $m$ has been performed by time $t$ (the matches at time $t$ included). It is **admissible** if
--
--   1. $D^0=0$;
--   2. $D^t_m$ is nondecreasing in $t$;
--   3. it is non-anticipative: $D^t$ depends only on the arrivals at times $1,\dots,t$;
--   4. it only matches agents that are present: $MD^t\le A^t$ componentwise.
--
--   The **pre-match queue** at time $t\ge1$ is (1):
--   $$Q^t=A^t-MD^{t-1}.$$
--   The **expected total value** collected by time $t$ is $\mathcal R^{D,t}=\mathbb E^D[r\cdot D^t]$.
--
--   The **static matching problem** with queue vector $u\in\mathbb Z^n_{\ge0}$ is $\max\{r\cdot y: My\le u,\ y\in\mathbb Z^d_{\ge0}\}$, and the **hindsight benchmark** is
--   $$\mathcal R^{*,t}=\mathbb E\Big[\max\{r\cdot y: My\le A^t,\ y\in\mathbb Z^d_{\ge 0}\}\Big].$$
--
--   The regret of a policy at time $t$ is $\mathcal R^{*,t}-\mathcal R^{D,t}$; the mission's goal bounds it uniformly in $t$.
--
--   **Formalization Note** Time is discrete ($t\in\mathbb N$), as in the model of p. 7. Admissible policies never reject agents (the paper's (1) has no rejection term); the exhaustive resolving policy's removals of under-demanded leftovers are modelled by its virtual queue in the definition `Resolving`. The subtraction in $Q^t$ is in $\mathbb N$ and does not truncate for admissible policies. The static optimum is a maximum over the finite box $\{0,\dots,\sum_iu_i\}^d$, which contains every feasible $y$ since each match uses some agent type; the value $0$ of $y=0$ is inserted so that the set is syntactically nonempty, which does not change the maximum. $\mathcal R^{*,t}$ is defined as the expected static optimum; its equality with $\max_{D}\mathcal R^{D,t}$ is the first milestone.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), pp. 8–9, §2 (Performance measure), (1)

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_Arrivals

namespace ConstRegretMatch.Upper

variable {n d : ℕ}

/-- A matching policy, as its cumulative match counts: `D t ω m = D^t_m`, the number of times match
`m` has been performed by time `t` (matches at time `t` included) along the arrival path `ω`. -/
abbrev Policy (n d : ℕ) := ℕ → (ℕ → Fin n) → Fin d → ℕ

/-- An admissible matching policy (§2, p. 8), in discrete time and without rejections:
1. nothing is matched at time `0`;
2. `D^t` is nondecreasing in `t`;
3. non-anticipative: `D^t` depends only on the arrivals at times `1, …, t`
   (that is, on `ω 0, …, ω (t-1)`);
4. feasible: the post-match queues `A^t - M D^t` are nonnegative, i.e. every match is formed from
   agents present in the market. Together with 2 this is (1), `Q^t = A^t - M D^{t-}`, with
   nonnegative queues. -/
def IsAdmissible (N : MatchingNetwork n d) (D : Policy n d) : Prop :=
  (∀ ω, D 0 ω = 0) ∧
    (∀ t ω m, D t ω m ≤ D (t + 1) ω m) ∧
    (∀ t ω ω', (∀ s < t, ω s = ω' s) → D t ω = D t ω') ∧
    (∀ t ω i, ∑ m, N.inc i m * D t ω m ≤ arrivals ω t i)

/-- The pre-match queue length `Q^t_i = A^t_i - (M D^{t-1})_i` at time `t ≥ 1` ((1), p. 8). For an
admissible policy the natural-number subtraction does not truncate:
`(M D^{t-1})_i ≤ A^{t-1}_i ≤ A^t_i`. -/
def queue (N : MatchingNetwork n d) (D : Policy n d) (ω : ℕ → Fin n) (t : ℕ) (i : Fin n) : ℕ :=
  arrivals ω t i - ∑ m, N.inc i m * D (t - 1) ω m

/-- The expected total value collected by time `t`, `𝓡^{D,t} = 𝔼^D[r · D^t]` (p. 8). -/
noncomputable def valueOf (lam : Fin n → ℝ) (r : Fin d → ℝ) (D : Policy n d) (t : ℕ) : ℝ :=
  expect lam t (fun ω => ∑ m, r m * (D t ω m : ℝ))

/-- `y ∈ ℤ^d_{≥0}` is feasible for the static matching problem with queue vector `u`: `M y ≤ u`. -/
def StaticFeasible (N : MatchingNetwork n d) (u : Fin n → ℕ) (y : Fin d → ℕ) : Prop :=
  ∀ i, ∑ m, N.inc i m * y m ≤ u i

/-- `StaticFeasible N u` is decidable (finitely many inequalities between naturals). -/
instance (N : MatchingNetwork n d) (u : Fin n → ℕ) : DecidablePred (StaticFeasible N u) :=
  fun y => by unfold StaticFeasible; infer_instance

/-- The value of the static weighted matching problem `max {r · y : M y ≤ u, y ∈ ℤ^d_{≥0}}` (p. 9).
Every feasible `y` has `y_m ≤ ∑_i u_i` (each match uses some agent type), so the maximum is taken over
the feasible points of the box `{0, …, ∑_i u_i}^d`; `y = 0` is feasible with value `0`, and the
`insert 0` only makes nonemptiness syntactic (it does not change the maximum). -/
noncomputable def staticOpt (N : MatchingNetwork n d) (r : Fin d → ℝ) (u : Fin n → ℕ) : ℝ :=
  (insert 0 (((Fintype.piFinset (fun _ : Fin d => Finset.range (∑ i, u i + 1))).filter
      (fun y => StaticFeasible N u y)).image (fun y => ∑ m, r m * (y m : ℝ)))).max'
    (Finset.insert_nonempty _ _)

/-- The hindsight benchmark `𝓡^{*,t} = 𝔼[max {r · y : M y ≤ A^t, y ∈ ℤ^d_{≥0}}]` (p. 9). -/
noncomputable def Rstar (N : MatchingNetwork n d) (lam : Fin n → ℝ) (r : Fin d → ℝ) (t : ℕ) : ℝ :=
  expect lam t (fun ω => staticOpt N r (arrivals ω t))

end ConstRegretMatch.Upper


