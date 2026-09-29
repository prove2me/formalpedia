-- Prove2me | Definitions.Def_KServer_evader
-- name    : KServer_evader
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T08:28:44.992261+00:00
-- url     : https://prove2.me/theorems/d7a26abc-3a37-45b9-b47b-972040231e63
-- title:
--   Metrical service systems (the evader problem) and the escape price relaxation
-- statement:
--   **Metrical service systems** (also *small set chasing*, MSS): a single server — the *evader* — occupies a point of a metric space $M$. The adversary requests subsets $S_1, S_2, \dots \subseteq M$; upon each request the evader must move into the requested set, paying the distance travelled. An online algorithm chooses its position knowing only the requests so far.
--
--   The definitions provide:
--
--   - `EvaderAlgorithm M` — a deterministic online MSS algorithm: a position function on request histories, constrained to land inside each newly requested nonempty set;
--   - `EvaderAlgorithm.cost` — its total movement on a request sequence, and `costOn h χ` — the partial cost of a chunk $\chi$ served after the history $h$;
--   - `EvaderAlgorithm.escapeCost h χ p` — the *escape price relaxation* of Bubeck–Coester–Rabani: the cheapest way to serve $\chi$ after $h$ when the algorithm may, after any proper prefix, bail out for a one-time payment $p$ (the minimum over bail-out times, which lower-bounds every escape strategy);
--   - `EvaderServes` / `evaderOfflineCost` — feasible offline paths and the optimal offline cost.
--
--   ## Role
--
--   On an $(k{+}1)$-point space, the $k$-server problem is equivalent to MSS through the motion of the *hole* (the unique uncovered point): a set request $S$ corresponds to a block of $k$-server requests enumerating $M \setminus S$. MSS is the setting in which the Bubeck–Coester–Rabani $\Omega(\log^2 k)$ randomized lower bound (STOC 2023) is constructed; the escape-price relaxation is the device that makes their chunked induction go through (their Section 2 and Lemma 6). These definitions are the foundation of that lower-bound formalization.
--
--   ## Formalization note
--
--   Requests are arbitrary `Set M`; an empty request imposes no constraint (in the BCR construction all requests are nonempty). The escape cost is a `Finset.inf'` over the bail-out time, so no game semantics is needed: lower bounds on it dominate every online escape strategy.
-- source:
--   M. Chrobak, L. Larmore, 'Metrical service systems: deterministic strategies', 1992; escape price relaxation from S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 2.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

/-- A deterministic online algorithm for **metrical service systems** (small set
chasing, MSS): a single server — the *evader* — moves in the metric space `M` and
must move into each requested set. `pos l` is its position after serving the
request sequence `l`; the algorithm is online because the position depends only
on the requests seen so far. An empty request imposes no constraint. -/
structure EvaderAlgorithm (M : Type*) [MetricSpace M] where
  pos : List (Set M) → M
  serves : ∀ (l : List (Set M)) (S : Set M), S.Nonempty → pos (l ++ [S]) ∈ S

/-- The total movement cost of the evader algorithm `A` on the request
sequence `σ`. -/
noncomputable def EvaderAlgorithm.cost {M : Type*} [MetricSpace M]
    (A : EvaderAlgorithm M) (σ : List (Set M)) : ℝ :=
  ∑ j ∈ Finset.range σ.length, dist (A.pos (σ.take j)) (A.pos (σ.take (j + 1)))

/-- The **partial cost** of `A` on the chunk `χ` served after the history `h`:
the cost of `h ++ χ` beyond the cost of `h`. -/
noncomputable def EvaderAlgorithm.costOn {M : Type*} [MetricSpace M]
    (A : EvaderAlgorithm M) (h χ : List (Set M)) : ℝ :=
  A.cost (h ++ χ) - A.cost h

/-- The partial cost of `A` on the chunk `χ` after the history `h` when an
**escape price** `p` is available on `χ`: the cheapest way to either serve `χ`
in full, or serve a proper prefix of it and then bail out for a one-time
payment of `p` (paying nothing thereafter). The minimum is over the bail-out
time, so this lower-bounds the cost of every escape strategy, online or not. -/
noncomputable def EvaderAlgorithm.escapeCost {M : Type*} [MetricSpace M]
    (A : EvaderAlgorithm M) (h χ : List (Set M)) (p : ℝ) : ℝ :=
  (Finset.range (χ.length + 1)).inf' ⟨0, by simp⟩ fun t =>
    if t = χ.length then A.costOn h χ else A.costOn h (χ.take t) + p

/-- `EvaderServes x₀ σ P`: the offline evader path `P` starts at `x₀` and
serves the request sequence `σ`: after the `j`-th request it is inside the
requested set (whenever that set is nonempty). -/
def EvaderServes {M : Type*} [MetricSpace M]
    (x₀ : M) (σ : List (Set M)) (P : ℕ → M) : Prop :=
  P 0 = x₀ ∧ ∀ j : Fin σ.length, (σ.get j).Nonempty → P (j + 1) ∈ σ.get j

/-- The **optimal offline cost** of serving the request sequence `σ` from `x₀`:
the infimum of the total movement over all feasible offline evader paths. -/
noncomputable def evaderOfflineCost {M : Type*} [MetricSpace M]
    (x₀ : M) (σ : List (Set M)) : ℝ :=
  sInf {c : ℝ | ∃ P : ℕ → M, EvaderServes x₀ σ P ∧
    c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))}

end KServer


