-- Prove2me | Definitions.Def_PrivLittlestone_gibbsExp
-- name    : PrivLittlestone_gibbsExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:35:32.382202+00:00
-- url     : https://prove2.me/theorems/69984486-0591-4df2-9d10-7d3d5e76a218
-- title:
--   Expectation $\mathbb E_{h\sim Q_S} f(h)$
-- statement:
--   For a function $f : U \to \mathbb R$, $\mathbb E_{h \sim Q_S} f(h) = \sum_{h \in C(S)} Q_S(h) f(h)$ is its expectation under the candidate distribution.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (3), p.6; (A2), p.7

import Mathlib
import Definitions.Def_PrivLittlestone_gibbs

namespace PrivLittlestone

/-- The expectation `E_{h∼Q_S} f(h)` under the candidate distribution (He–He, *Private Online
Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), (3), p.6, (A2), p.7): a finite sum over `C(S)`. -/
noncomputable def gibbsExp {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η a : ℝ) (S : List Z) (f : U → ℝ) : ℝ :=
  ∑ h ∈ sys.C S, gibbs sys η a S h * f h

end PrivLittlestone


