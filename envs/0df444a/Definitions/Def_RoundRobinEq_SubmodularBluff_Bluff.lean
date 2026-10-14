-- Prove2me | Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
-- name    : RoundRobinEq_SubmodularBluff_Bluff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:17.5794+00:00
-- url     : https://prove2.me/theorems/03d7e741-49e5-4c31-96dc-b389da6ecbc3
-- title:
--   p. 9–10, Algorithm 2 — the greedy renaming $h_1,\dots,h_m$ and the submodular bluff profile
-- statement:
--   Algorithm 2 (p. 10) renames the goods $h_1,\dots,h_m$ by a hypothetical *truthfully greedy* run. Every agent starts with $X_i=\emptyset$. At iteration $j=1,\dots,m$ the active agent is $i=(j-1)\bmod n+1$, and she receives a good of largest marginal value with respect to her current goods among the goods not yet handed out:
--   $$h_j\in\arg\max_{g\in M\setminus\bigcup_\ell X_\ell} v_i(g\mid X_i),\qquad X_i\leftarrow X_i\cup\{h_j\}.$$
--   The resulting total order $h_1\succ^{\mathrm b}h_2\succ^{\mathrm b}\cdots\succ^{\mathrm b}h_m$ is $\succ^{\mathrm b}$, and the *bluff profile* is the profile in which every agent reports it, $\boldsymbol\succ^{\mathrm b}=(\succ^{\mathrm b},\dots,\succ^{\mathrm b})$ (p. 9).
--
--   The bluff profile is the candidate equilibrium of Theorem 3.7.
--
--   **Formalization Note.** `IsGreedyOrder v h` says that the list `h` is a ranking and that every entry `h[j]` (0-based) maximizes $v_i(g\mid X_i)$ for the agent $i$ acting at step $j$, where $X_i$ (`greedyBundle n h j`) is the set of earlier entries at that agent's steps, over all $g$ not among the earlier entries. Algorithm 2 breaks ties lexicographically; `IsGreedyOrder` admits every tie-breaking, so statements quantified over all greedy orders cover the paper's lexicographic bluff profile and are at least as strong.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 9 (§3.2, definition of the bluff profile) and p. 10, Algorithm 2

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting

namespace RoundRobinEq.SubmodularBluff

/-- The goods that agent `agentAt n j` received among the first `j` entries `h[0], …, h[j-1]`
of the list `h` in Algorithm 2 (the set `X_i` at iteration `j`). -/
def greedyBundle (n : ℕ) [NeZero n] {M : Type*} [DecidableEq M] (h : List M) (j : ℕ) :
    Finset M :=
  ((Finset.range j).filter (fun t => RoundRobinEq.CancelableBluff.agentAt n t = RoundRobinEq.CancelableBluff.agentAt n j)).biUnion
    (fun t => (h[t]?).toFinset)

/-- `h = (h_1, …, h_m)` is an output of Algorithm 2 (p. 10) for some tie-breaking rule: `h` is a
ranking of `M`, and for every position `j` (0-based) the entry `h[j]` maximizes the RoundRobinEq.CancelableBluff.marginal
value `v_i(g | X_i)` of the agent `i = RoundRobinEq.CancelableBluff.agentAt n j` with respect to the goods `X_i` she received
at the earlier positions, over all goods `g` not among the earlier entries. -/
def IsGreedyOrder {n : ℕ} [NeZero n] {M : Type*} [DecidableEq M]
    (v : Fin n → Finset M → ℝ) (h : List M) : Prop :=
  RoundRobinEq.CancelableBluff.IsRanking h ∧
    ∀ (j : ℕ) (hj : j < h.length) (g : M), g ∉ h.take j →
      RoundRobinEq.CancelableBluff.marginal (v (RoundRobinEq.CancelableBluff.agentAt n j)) {g} (greedyBundle n h j) ≤
        RoundRobinEq.CancelableBluff.marginal (v (RoundRobinEq.CancelableBluff.agentAt n j)) {h[j]} (greedyBundle n h j)

/-- The bluff profile `≻^b = (≻^b, …, ≻^b)` (p. 9): every agent reports the greedy order `h`. -/
def bluff {n : ℕ} {M : Type*} (h : List M) : Fin n → List M :=
  fun _ => h

end RoundRobinEq.SubmodularBluff


