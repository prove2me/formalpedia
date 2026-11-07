-- Prove2me | Definitions.Def_BlockSSM_Tracker_IsLeastRankIdempotent
-- name    : BlockSSM_Tracker_IsLeastRankIdempotent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:26.495545+00:00
-- url     : https://prove2.me/theorems/4cc8e080-730a-4866-9407-ef569fc911c5
-- title:
--   Idempotent of least affine rank
-- statement:
--   An element $E$ of the transition monoid $M$ is an **idempotent of least affine rank** if $E^2=E$ and $\mathrm{rank}\,E\le\mathrm{rank}\,F$ for every idempotent $F\in M$.
--
--   **Formalization Note** "Least" is taken among idempotents, as in the proof of Lemma 6, where minimality is applied to an idempotent power.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 6, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BlockSSM_Tracker_transMonoid
import Definitions.Def_BlockSSM_Tracker_affineRank

universe u

namespace BlockSSM

variable {G : Type u} {b : ℕ∞}

/-- **Idempotent of least affine rank.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 6, p.3 (PDF p.4): "Let E ∈ M be an idempotent of
least affine rank".

**Formalization Note.** "Least" is among the idempotents of `M`, which is what the paper's proof uses
("minimality" is applied to the idempotent power `F^k`). -/
def Tracker.IsLeastRankIdempotent (T : Tracker G b) (E : T.transMonoid) : Prop :=
  IsIdempotentElem E ∧
    ∀ F : T.transMonoid, IsIdempotentElem F → T.affineRank E.1 ≤ T.affineRank F.1

end BlockSSM


