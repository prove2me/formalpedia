-- Prove2me | Definitions.Def_PrivLittlestone_potential
-- name    : PrivLittlestone_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:30:54.079372+00:00
-- url     : https://prove2.me/theorems/6554047b-022c-4a0f-925f-ff39ebdbfe4d
-- title:
--   Potential $Z_S = \sum_{h \in C(S)} w_S(h)$
-- statement:
--   The **potential** after the record sequence $S$ is the total weight of the current candidates,
--   $$
--   Z_S = \sum_{h \in C(S)} w_S(h).
--   $$
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (2), p.5

import Mathlib
import Definitions.Def_PrivLittlestone_weight

namespace PrivLittlestone

/-- The **potential** `Z_S = ∑_{h ∈ C(S)} w_S(h)` (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (2), p.5). -/
noncomputable def potential {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η a : ℝ) (S : List Z) : ℝ :=
  ∑ h ∈ sys.C S, weight sys η a S h

end PrivLittlestone


