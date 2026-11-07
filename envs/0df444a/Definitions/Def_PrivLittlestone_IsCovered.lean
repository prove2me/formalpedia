-- Prove2me | Definitions.Def_PrivLittlestone_IsCovered
-- name    : PrivLittlestone_IsCovered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:27.423691+00:00
-- url     : https://prove2.me/theorems/7ffae42b-bfe5-4fda-87da-81dc60b4f7b6
-- title:
--   Covered retained sequence
-- statement:
--   A retained sequence is **covered** if every prefix $S$ admits a candidate $h \in C(S)$ with $\ell_S(h) = 0$. Coverage implies $Z_S \ge 1$ along the sequence.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.2, p.5

import Mathlib
import Definitions.Def_PrivLittlestone_cumLoss

namespace PrivLittlestone

/-- A retained sequence is **covered** (He–He, *Private Online Learning of Littlestone Classes
and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), §2.2, p.5) if every
prefix `S` admits some `h ∈ C(S)` with `ℓ_S(h) = 0`. -/
def IsCovered {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B) (S : List Z) :
    Prop :=
  ∀ k : ℕ, k ≤ S.length → ∃ h ∈ sys.C (S.take k), cumLoss sys (S.take k) h = 0

end PrivLittlestone


