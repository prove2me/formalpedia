-- Prove2me | Definitions.Def_BlockSSM_Tracker_IsFiniteState
-- name    : BlockSSM_Tracker_IsFiniteState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:21:20.356112+00:00
-- url     : https://prove2.me/theorems/0d92ccd6-acc1-43c1-9c0e-a2c8e49265cd
-- title:
--   Finite-state tracker
-- statement:
--   The **reachable set** of a tracker is $R=\{F_s(h_0): s\in G^*\}$, and the tracker is **finite-state** when $R$ is finite. The condition is essential: without it one scalar coordinate can store the entire input word, and the dimension question becomes trivial.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_BlockSSM_Tracker

universe u

namespace BlockSSM

variable {G : Type u} {b : ℕ∞}

/-- The reachable set `R = {F_s(h₀) : s ∈ G*}`. -/
def Tracker.reach (T : Tracker G b) : Set (State T.n) :=
  Set.range fun s : List G => T.wordMap s T.h₀

/-- **Finite-state tracker.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3): "The tracker is finite-state when
R = {F_s(h₀) : s ∈ G*} is finite." -/
def Tracker.IsFiniteState (T : Tracker G b) : Prop := T.reach.Finite

end BlockSSM


