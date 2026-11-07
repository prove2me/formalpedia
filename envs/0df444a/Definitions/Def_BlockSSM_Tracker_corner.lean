-- Prove2me | Definitions.Def_BlockSSM_Tracker_corner
-- name    : BlockSSM_Tracker_corner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:41.798419+00:00
-- url     : https://prove2.me/theorems/8900efc9-10c0-4cc2-a212-42d9b207f4f6
-- title:
--   The corner $EME$
-- statement:
--   For $E$ in the transition monoid $M$, the **corner** is $EME=\{EXE: X\in M\}$, the set that Lemma 6 shows to be a group when $E$ is an idempotent of least affine rank.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 6, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BlockSSM_Tracker_transMonoid

universe u

namespace BlockSSM

variable {G : Type u} {b : ℕ∞}

/-- **The corner `EME`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 6, p.3 (PDF p.4): "H = EME", the set of all `E X E` with
`X ∈ M`. -/
def Tracker.corner (T : Tracker G b) (E : T.transMonoid) : Set T.transMonoid :=
  {F | ∃ X : T.transMonoid, F = E * X * E}

end BlockSSM


