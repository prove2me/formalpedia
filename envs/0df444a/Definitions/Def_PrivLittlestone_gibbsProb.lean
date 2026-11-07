-- Prove2me | Definitions.Def_PrivLittlestone_gibbsProb
-- name    : PrivLittlestone_gibbsProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:35:00.436784+00:00
-- url     : https://prove2.me/theorems/feaf0014-0341-4568-970b-c1722be5f09f
-- title:
--   Probability $Q_S(E)$ of a set of candidates
-- statement:
--   For a set $E \subseteq U$, $Q_S(E) = \sum_{h \in C(S) \cap E} Q_S(h)$ is the probability that a draw from the candidate distribution lies in $E$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma 2.3, p.5; Appendix A.1, p.17

import Mathlib
import Definitions.Def_PrivLittlestone_gibbs

namespace PrivLittlestone

open Classical in
/-- The probability `Q_S(E)` of a set `E` of candidates under the candidate distribution (He–He,
*Private Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission
manuscript (sha256 21480556…c562), Lemma 2.3, p.5, and Appendix A.1, p.17): a finite sum over
`C(S)`, defined for every set `E ⊆ U`. -/
noncomputable def gibbsProb {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η a : ℝ) (S : List Z) (E : Set U) : ℝ :=
  ∑ h ∈ sys.C S, if h ∈ E then gibbs sys η a S h else 0

end PrivLittlestone


