-- Prove2me | Definitions.Def_PrivLittlestone_cumLoss
-- name    : PrivLittlestone_cumLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:27.861731+00:00
-- url     : https://prove2.me/theorems/101f57af-b7b2-44e8-8fac-1be8fae6b927
-- title:
--   Cumulative loss $\ell_S(h)$
-- statement:
--   For a ranked candidate system, the **cumulative loss** of a candidate $h$ on a finite record sequence $S$ is $\ell_S(h) = \sum_{u \in S} \ell_u(h)$, counting multiplicities. It is accumulated on all records of $S$, including records arriving while $h$ is absent from the candidate set.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.2, pp.4–5

import Mathlib
import Definitions.Def_PrivLittlestone_RankedCandidateSystem

namespace PrivLittlestone

/-- The **cumulative loss** `ℓ_S(h) = ∑_{u ∈ S} ℓ_u(h)` of a candidate on a finite record
sequence, counting multiplicities (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), §2.2, p.4; p.5: "Losses
are accumulated on all retained records, including records arriving while a candidate is
absent"). Defined for every `h ∈ U`, whether or not `h ∈ C(S)`. -/
def cumLoss {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B) (S : List Z)
    (h : U) : ℕ :=
  (S.map fun u => sys.loss u h).sum

end PrivLittlestone


