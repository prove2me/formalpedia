-- Prove2me | Definitions.Def_GoldbergTarjan_Generic_Run
-- name    : GoldbergTarjan_Generic_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:24:28.392232+00:00
-- url     : https://prove2.me/theorems/da2dbea9-178d-4b5b-96b4-90df28c39e4b
-- title:
--   Executions of the generic algorithm (Fig. 2, simple labeling) and counts of relabelings, saturating and nonsaturating pushes
-- statement:
--   The **initial state** of the generic maximum-flow algorithm (Fig. 2) is the preflow that saturates every edge leaving the source and is zero elsewhere,
--   $$f(s,v) = c(s,v),\quad f(v,s) = -c(s,v)\ \ (v \in V), \qquad f(v,w) = 0\ \ (v,w \ne s),$$
--   together with the **simple labeling** $d(s) = n$, $d(v) = 0$ for $v \in V - \{s\}$.
--
--   An **execution** (run) with $K$ basic operations is a sequence of states $(f_0,d_0), (f_1,d_1), \dots, (f_K,d_K)$ that starts at the initial state and in which each $(f_{k+1},d_{k+1})$ is obtained from $(f_k,d_k)$ by one applicable push or relabel, the operations being chosen in any order.
--
--   For a run we count, among its $K$ steps:
--
--   1. the number of relabelings of a given vertex $v$, and the total number of relabelings;
--   2. the number of **saturating** pushes: steps Push$(v,w)$ after which $r_f(v,w) = 0$;
--   3. the number of **nonsaturating** pushes: steps Push$(v,w)$ after which $r_f(v,w) > 0$.
--
--   These counts are the quantities bounded in Lemmas 3.8, 3.9 and 3.10, and their sum is the total number $K$ of basic operations bounded in Theorem 3.11.
--
--   **Formalization Note.** A run is a function `σ : ℕ → State V` with a length `K`; only `σ 0, …, σ K` matter. Each count is the number of indices $k < K$ whose step $(σ_k, σ_{k+1})$ is of the given kind. A push step changes $f$ (by $\delta > 0$) and a relabel step does not, and a push step determines its pair $(v,w)$, so every step is exactly one of: a relabeling, a saturating push, a nonsaturating push. The paper's initial labeling may be any valid labeling; the paper assumes the simple one for its proofs (p. 926), and so does this definition.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 925, Fig. 2 (initialization, loop), saturating/nonsaturating push; p. 926 (simple labeling)

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Operations

namespace GoldbergTarjan.Generic

open Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The initial preflow of Fig. 2 (p. 925): `f(s, v) = c(s, v)`, `f(v, s) = -c(s, v)` for every
`v`, and `f(v, w) = 0` for `v, w ≠ s`. (With `c(s, s) = 0` both assignments give `f(s, s) = 0`.) -/
def initialFlow (N : Network V) : V → V → ℝ :=
  fun v w => if v = N.s then N.c N.s w else if w = N.s then -N.c N.s v else 0

/-- The simple initial labeling (p. 926): `d(s) = n` and `d(v) = 0` for `v ∈ V - {s}`. -/
noncomputable def initialLabel (N : Network V) : V → ℕ∞ :=
  fun v => if v = N.s then (Fintype.card V : ℕ∞) else 0

/-- The initial state of the generic algorithm (Fig. 2 with the simple labeling). -/
noncomputable def initialState (N : Network V) : State V :=
  (initialFlow N, initialLabel N)

/-- `IsRun N σ K`: `σ 0, σ 1, …, σ K` is an execution of the generic algorithm (Fig. 2) with
`K` basic operations: it starts from the initial state, and each `σ (k + 1)` (`k < K`) is
obtained from `σ k` by one applicable push or relabel, chosen in any order. The values of
`σ` beyond `K` are irrelevant. -/
def IsRun (N : Network V) (σ : ℕ → State V) (K : ℕ) : Prop :=
  σ 0 = initialState N ∧ ∀ k < K, BasicStep N (σ k) (σ (k + 1))

/-- The number of relabeling operations applied to the vertex `v` among the first `K` steps
of `σ`. -/
noncomputable def relabelCountAt (N : Network V) (σ : ℕ → State V) (K : ℕ) (v : V) : ℕ :=
  ((Finset.range K).filter (fun k => RelabelStep N (σ k) (σ (k + 1)) v)).card

/-- The number of relabeling operations among the first `K` steps of `σ`. -/
noncomputable def relabelCount (N : Network V) (σ : ℕ → State V) (K : ℕ) : ℕ :=
  ((Finset.range K).filter (fun k => ∃ v, RelabelStep N (σ k) (σ (k + 1)) v)).card

/-- The number of saturating pushes among the first `K` steps of `σ`: steps that are a
`Push(v, w)` after which `r_f(v, w) = 0` (p. 925). -/
noncomputable def saturatingPushCount (N : Network V) (σ : ℕ → State V) (K : ℕ) : ℕ :=
  ((Finset.range K).filter (fun k => ∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
    residualCap N (σ (k + 1)).1 v w = 0)).card

/-- The number of nonsaturating pushes among the first `K` steps of `σ`: steps that are a
`Push(v, w)` after which `r_f(v, w) > 0` (p. 925). -/
noncomputable def nonsaturatingPushCount (N : Network V) (σ : ℕ → State V) (K : ℕ) : ℕ :=
  ((Finset.range K).filter (fun k => ∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
    0 < residualCap N (σ (k + 1)).1 v w)).card

end GoldbergTarjan.Generic


