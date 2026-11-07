-- Prove2me | Definitions.Def_PrivLittlestone_gibbs
-- name    : PrivLittlestone_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:33:32.364641+00:00
-- url     : https://prove2.me/theorems/870bbc26-38fd-4e70-81c8-20f825362d1c
-- title:
--   Candidate distribution $Q_S(h) = w_S(h)/Z_S$
-- statement:
--   The **candidate distribution** after the record sequence $S$ is the probability mass function on $C(S)$
--   $$
--   Q_S(h) = \frac{w_S(h)}{Z_S}, \qquad h \in C(S),
--   $$
--   and $Q_S(h) = 0$ for $h \notin C(S)$. It is the distribution the continual learner samples from at each phase start.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (2), p.5

import Mathlib
import Definitions.Def_PrivLittlestone_potential

namespace PrivLittlestone

open Classical in
/-- The **candidate distribution** `Q_S(h) = w_S(h)/Z_S` on `C(S)` (He–He, *Private Online
Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), (2), p.5), as a probability mass function, `0` outside `C(S)`.

**Formalization Note** `Z_S > 0` because `C(S)` is nonempty and weights are positive, so there is
no division by zero. -/
noncomputable def gibbs {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η a : ℝ) (S : List Z) (h : U) : ℝ :=
  if h ∈ sys.C S then weight sys η a S h / potential sys η a S else 0

end PrivLittlestone


