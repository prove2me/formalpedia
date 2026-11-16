-- Prove2me | Definitions.Def_CanadaCTP_Supplement_Entries
-- name    : CanadaCTP_Supplement_Entries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:35:21.472857+00:00
-- url     : https://prove2.me/theorems/fb93ab97-50c1-4e58-b624-faa9a2b20e1e
-- title:
--   Entries into a path and entry-bounded policies
-- statement:
--   An **entry** into path $i$ is a step at which the traveller stands at $s$ and starts traversing the first edge of path $i$. Along a run, the entries into each path are counted.
--
--   A policy $\pi$ **enters each path at most $k$ times** if, for every realization of the edge weights and every trajectory of positive probability (each step drawn from the support of the policy's randomized choice), every path is entered at most $k$ times.
--
--   This is the restricted class of policies of Theorem 7.
--
--   **Formalization Note** The published configurations do not record moves, so the trajectories are an inductive reachability predicate `Reach` that carries the entry counter; absorbing steps (at $t$ or after stopping) change nothing and are omitted.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 7, p.30 (Appendix A)

import Mathlib
import Definitions.Def_CanadaCTP_Model

namespace CanadaCTP.Supplement

open CanadaCTP

/-- Whether the move `mv` applied in configuration `c` is an **entry** into path `i`
(*Canada Retravelled*, manuscript, sha256 8117348e…3a33, Theorem 7, p.30): the traveller is at
`s` and starts traversing the first edge of path `i` (which exists). -/
def enters (I : Inst) {Mem : Type} (c : Config I Mem) (mv : Move I) (i : Fin I.k) : Bool :=
  match c.pos, mv with
  | Pos.s, Move.fwd i' => decide (i' = i ∧ 0 < I.m i)
  | _, _ => false

/-- `Reach I π ι c cnt`: under realization `ι`, the configuration `c` is reached by a
positive-probability trajectory of `π` (each step drawn from the support of the policy's step
distribution, as in `CanadaCTP.stepCfg`) along which path `i` was entered `cnt i` times. Steps at
`t` or after `stop` are absorbing and change nothing, so they are omitted. -/
inductive Reach (I : Inst) {Mem : Type} (π : Policy I Mem) (ι : Realz I) :
    Config I Mem → (Fin I.k → ℕ) → Prop
  | init : Reach I π ι (initCfg I π) (fun _ => 0)
  | step {c : Config I Mem} {cnt : Fin I.k → ℕ} {mm : Move I × Mem} :
      Reach I π ι c cnt → ¬ (c.pos = Pos.t ∨ c.stopped = true) →
      mm ∈ (π.step c.mem (obsOf I ι c)).support →
      Reach I π ι (applyMove I ι c mm.1 mm.2)
        (fun i => cnt i + if enters I c mm.1 i then 1 else 0)

/-- `π` **enters each path at most `k` times** (Theorem 7, p.30): on every realization and every
positive-probability trajectory, every path is entered at most `k` times. -/
def EntryBounded (I : Inst) {Mem : Type} (π : Policy I Mem) (k : ℕ) : Prop :=
  ∀ (ι : Realz I) (c : Config I Mem) (cnt : Fin I.k → ℕ), Reach I π ι c cnt → ∀ i, cnt i ≤ k

end CanadaCTP.Supplement


