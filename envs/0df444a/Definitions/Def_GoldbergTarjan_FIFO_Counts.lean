-- Prove2me | Definitions.Def_GoldbergTarjan_FIFO_Counts
-- name    : GoldbergTarjan_FIFO_Counts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:33:23.338479+00:00
-- url     : https://prove2.me/theorems/ae580a4a-92c2-49e3-a0d6-ec8c7003389b
-- title:
--   Counting nonsaturating pushes, relabelings and passes in a run of the first-in, first-out algorithm
-- statement:
--   This file defines the quantities bounded in §3–§4 of Goldberg and Tarjan, for a run of the first-in, first-out algorithm made of $K$ discharge operations.
--
--   1. A push/relabel$(v)$ operation performs a **nonsaturating push** when it pushes through its current edge $\{v,w\}$ and afterwards $r_f(v,w) > 0$. A push with $r_f(v,w) = 0$ afterwards is **saturating**.
--   2. A push/relabel$(v)$ operation performs a **relabeling** when no push is applicable through its current edge and that edge is the last on the edge list of $v$.
--   3. The **number of nonsaturating pushes** of the run is the total, over its $K$ discharges and over all push/relabel operations inside each discharge, of the operations that perform a nonsaturating push.
--   4. The **number of relabelings of a vertex** $x$ is the analogous total over the discharges of $x$ (only a discharge of $x$ relabels $x$). The **total number of relabelings** sums this over all vertices.
--   5. The **number of passes** over the queue is the largest pass number of an entry discharged by the run, and $0$ for $K = 0$.
--
--   These are the quantities in Lemma 3.8 (relabelings), Lemma 4.3 (passes) and Corollary 4.4 (nonsaturating pushes).
--
--   **Formalization Note** All counts are natural numbers, defined as sums of cardinalities of finite sets of operation indices `j < J k`. The number of passes is the supremum in `ℕ` of the pass tags of the front queue entries of the states `S k`, `k < K`.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 925 (saturating and nonsaturating pushes), p. 927 (Lemma 3.8), p. 930 (passes)

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm

open Classical

namespace GoldbergTarjan.FIFO

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The `push/relabel(v)` operation from `σ` performs a push `push(v, w)` through its current edge
`{v, w}` (Fig. 3) and the push is nonsaturating (p. 925): `r_f(v, w) > 0` after the push. -/
def IsNonsatPush (N : Network V) (L : V → List V) (v : V) (σ : Config V) : Prop :=
  ∃ w, (L v)[σ.cur v]? = some w ∧ PushApplicable N σ.f σ.d v w ∧
    0 < residual N (pushFlow N σ.f v w) v w

/-- The `push/relabel(v)` operation from `σ` takes the relabeling branch of Fig. 3: no push is
applicable through the current edge `{v, w}` and `{v, w}` is the last edge on the edge list of `v`,
so `relabel(v)` is performed. -/
def IsRelabelOp (N : Network V) (L : V → List V) (v : V) (σ : Config V) : Prop :=
  ∃ w, (L v)[σ.cur v]? = some w ∧ ¬ PushApplicable N σ.f σ.d v w ∧ σ.cur v + 1 = (L v).length

/-- The number of nonsaturating pushes performed during the first `K` discharge operations of the
run `(S, J)`: the `k`-th discharge applies `push/relabel(v_k)` to the configurations
`prIter … (S k).cfg j`, `j < J k`, where `v_k` is the front vertex of `S k`. -/
noncomputable def nonsatPushCount (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V)
    (J : ℕ → ℕ) : ℕ :=
  ∑ k ∈ Finset.range K,
    ((Finset.range (J k)).filter
      (fun j => IsNonsatPush N L (frontVertex N (S k))
        (prIter N L (frontVertex N (S k)) (S k).cfg j))).card

/-- The number of relabeling operations applied to the vertex `x` during the first `K` discharge
operations of the run `(S, J)` (only discharges of `x` can relabel `x`). -/
noncomputable def relabelCountAt (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V)
    (J : ℕ → ℕ) (x : V) : ℕ :=
  ∑ k ∈ Finset.range K,
    if frontVertex N (S k) = x then
      ((Finset.range (J k)).filter
        (fun j => IsRelabelOp N L x (prIter N L x (S k).cfg j))).card
    else 0

/-- The total number of relabeling operations during the first `K` discharge operations. -/
noncomputable def relabelCount (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V)
    (J : ℕ → ℕ) : ℕ :=
  ∑ x, relabelCountAt N L K S J x

/-- The number of passes over the queue (p. 930) made by the first `K` discharge operations: the
largest pass number of a discharged queue entry (`0` if `K = 0`). -/
def passCount (K : ℕ) (S : ℕ → State V) : ℕ :=
  (Finset.range K).sup (fun k => frontPass (S k))

end GoldbergTarjan.FIFO


