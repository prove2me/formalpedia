-- Prove2me | Definitions.Def_HierADA_RunState
-- name    : HierADA_RunState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:26.891216+00:00
-- url     : https://prove2.me/theorems/4768ae55-2ded-4100-8208-e21c09038074
-- title:
--   State and record of an execution of Algorithms 1–2
-- statement:
--   The state of an execution of the hierarchical mechanism with $p$ blocks of sizes $n_j$ consists of:
--
--   1. the score vector $G_j\in\mathbb R^{n_j}$ of every block;
--   2. the number $T_j$ of corrections so far on every edge;
--   3. the index of the next test noise.
--
--   The record of the execution consists of:
--
--   1. the public transcript (each query with its released answer);
--   2. the list of queries received;
--   3. the augmented transcript;
--   4. for every correction, its edge and all score vectors right after it;
--   5. every noise value drawn, in order;
--   6. whether all queries were answered.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Algorithms 1–2, pp.13–14, and Section 3.2, p.18

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_AugEvent

set_option autoImplicit false

open IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **State and record of an execution of Algorithms 1–2** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), pp.13–14 and p.18.

For `p` blocks of sizes `n j`, the state holds the score vectors `G j`, the correction counts `T j`
of the edges, and the index of the next test noise; the record holds the public transcript (query,
released answer), the queries received, the augmented transcript, the score vectors after each
correction with the edge of that correction, every noise value drawn, and whether all queries were
answered. -/
structure RunState (X : Type) {p : ℕ} (n : Fin p → ℕ) where
  /-- score vector `G_j` of each block -/
  G : (j : Fin p) → Fin (n j) → ℝ
  /-- number of corrections `T_j` on each edge so far -/
  T : Fin p → ℕ
  /-- index of the next test noise `V` -/
  vIdx : ℕ
  /-- the public transcript: each query with its released answer -/
  transcript : Transcript (StatisticalQuery X)
  /-- the queries received, in order -/
  queries : List (StatisticalQuery X)
  /-- the augmented transcript -/
  aug : List AugEvent
  /-- each correction: its edge and all score vectors right after it -/
  corrections : List (ℕ × ((j : Fin p) → Fin (n j) → ℝ))
  /-- every noise value drawn, in order -/
  noiseUsed : List ℝ
  /-- whether all queries were answered -/
  finished : Bool

end HierADA


