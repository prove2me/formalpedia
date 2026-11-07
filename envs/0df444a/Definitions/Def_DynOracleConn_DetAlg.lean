-- Prove2me | Definitions.Def_DynOracleConn_DetAlg
-- name    : DynOracleConn_DetAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:35.972101+00:00
-- url     : https://prove2.me/theorems/40cc2f27-d2ea-4888-8292-de5ccd4042ad
-- title:
--   Deterministic dynamic oracle algorithms with a persistent state
-- statement:
--   A deterministic dynamic algorithm has a state set $S$ (the memory kept between updates), an initial state, and for each update index $k$, state and announced update, a probe tree whose leaf gives the new state and an answer bit.
--
--   On a sequence $\sigma$, the tree of the $k$-th update is run against the oracle of the graph **before** that update, $G_k(\sigma)$. The run records, per update, the probes with their replies and the answer. Its **total cost** is the number of probes over all updates. It is **correct on** $\sigma$ for terminals $s,t$ if, for each $k<|\sigma|$, the $k$-th answer is true exactly when $s$ and $t$ are connected in the graph **after** the update, $G_{k+1}(\sigma)$.
--
--   These are the paper's snapshot semantics: "the algorithm can inspect the graph as it was before the update, and it must report whether s and t are connected after the update".
--
--   **Formalization Note** The $B$ bits of memory appear wherever used as the hypothesis $|S|\le 2^B$. Memory inside one update is not limited and the step may depend on the index $k$, so the class contains every algorithm of the paper's model, as §3 p.19 allows for its lower bound. There is no initialization phase. Updates are 0-based.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4 and §2, pp.15–16

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree
import Definitions.Def_DynOracleConn_GraphAfter

namespace DynOracleConn

/-!
# Deterministic dynamic oracle algorithms with a bounded persistent state

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4 and the box
"Dynamic Oracle Model", §2, p.15: "Each update is announced before it takes effect: while
processing an insertion or deletion, the algorithm can inspect the graph as it was before the
update, and it must report whether s and t are connected after the update; the oracle then
advances to the updated graph."

**Formalization Note.**
1. An algorithm is a state type `S` (the memory kept between updates), an initial state, and for
   the `k`-th update (0-based), the current state and the announced update, a probe tree whose
   leaf gives the new state and the answer bit. The paper's B bits of memory become the hypothesis
   `Fintype.card S ≤ 2 ^ B` wherever it is used. Memory used inside one update is not restricted,
   and the step may depend on the index `k`; this class contains every algorithm of the paper's
   model (§3, p.19: "while processing a block, the algorithm may use unlimited workspace").
2. Snapshot semantics: the `k`-th update's probes are answered by `O (graphAfter σ k)`, the graph
   *before* the update; the answer is checked against `graphAfter σ (k + 1)`, the graph after it.
3. `transcript` records, for every update, the list of (probe, reply) pairs and the answer bit;
   `totalCost` is the total number of probes over the whole sequence. There is no initialization
   phase (p.4: "we allow no initialization time").
4. `AllCorrect` asks for a correct answer after every update, as in the box "Output. After every
   update, the algorithm outputs whether s and t are connected in the current graph" (p.16).
-/

/-- A deterministic dynamic algorithm on `Fin n` with oracle questions `Q`, replies `Ans` and
persistent state `S`. -/
structure DetAlg (n : ℕ) (Q Ans S : Type) : Type where
  /-- The state before the first update. -/
  init : S
  /-- The probe tree processing the `k`-th update (0-based) from state `st`; its leaf gives the
  new state and the reported answer. -/
  step : ℕ → S → PunctSketch.Update n → ProbeTree Q Ans (S × Bool)

namespace DetAlg

variable {n : ℕ} {Q Ans S : Type}

/-- The run from update index `k`, state `st` and current graph `G` on the remaining updates:
the per-update transcripts and answers. Each step is answered by the graph *before* its update. -/
noncomputable def runFrom (A : DetAlg n Q Ans S) (O : SimpleGraph (Fin n) → Q → Ans) :
    ℕ → S → SimpleGraph (Fin n) → List (PunctSketch.Update n) → List (List (Q × Ans) × Bool)
  | _, _, _, [] => []
  | k, st, G, u :: rest =>
      ((A.step k st u).transcript (O G), ((A.step k st u).run (O G)).2) ::
        runFrom A O (k + 1) ((A.step k st u).run (O G)).1 (u.apply G) rest

/-- The run of `A` on the update sequence `σ` from the empty graph: for every update, the probes
with their replies and the reported answer. -/
noncomputable def transcript (A : DetAlg n Q Ans S) (O : SimpleGraph (Fin n) → Q → Ans)
    (σ : List (PunctSketch.Update n)) : List (List (Q × Ans) × Bool) :=
  A.runFrom O 0 A.init ⊥ σ

/-- The answers reported after the updates of `σ`, in order. -/
noncomputable def answers (A : DetAlg n Q Ans S) (O : SimpleGraph (Fin n) → Q → Ans)
    (σ : List (PunctSketch.Update n)) : List Bool :=
  (A.transcript O σ).map Prod.snd

/-- The total number of oracle probes made while processing `σ`. -/
noncomputable def totalCost (A : DetAlg n Q Ans S) (O : SimpleGraph (Fin n) → Q → Ans)
    (σ : List (PunctSketch.Update n)) : ℕ :=
  ((A.transcript O σ).map (fun p => p.1.length)).sum

/-- Every answer is correct: after the `k`-th update, the reported bit is `true` exactly when `s`
and `t` are connected in the graph after that update. -/
def AllCorrect (A : DetAlg n Q Ans S) (O : SimpleGraph (Fin n) → Q → Ans) (s t : Fin n)
    (σ : List (PunctSketch.Update n)) : Prop :=
  ∀ k < σ.length, ((A.answers O σ)[k]? = some true ↔ (graphAfter σ (k + 1)).Reachable s t)

end DetAlg

end DynOracleConn


