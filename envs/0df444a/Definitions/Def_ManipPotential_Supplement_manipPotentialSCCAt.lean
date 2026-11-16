-- Prove2me | Definitions.Def_ManipPotential_Supplement_manipPotentialSCCAt
-- name    : ManipPotential_Supplement_manipPotentialSCCAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:56:07.897396+00:00
-- url     : https://prove2.me/theorems/1968920b-e1a2-4c2e-9006-9a31c72373ff
-- title:
--   Manipulation potential of an SCC $\mathrm{MP}(F) = \max_{\succ_T} \mathrm{MP}(F_T)$
-- statement:
--   The **manipulation potential** of an SCC $F$ at electorate size $n$ is the largest manipulation potential (Definition 2) of its tie-broken rules:
--   $$\mathrm{MP}(F) := \max_{\succ_T \in \mathcal L(C)} \mathrm{MP}(F_T),$$
--   an element of $\mathbb Z_{\ge 0} \cup \{\infty\}$.
--
--   Every theorem of Section 4 bounds this quantity for a concrete rule or a class of rules.
--
--   **Formalization Note** Valued in `ℕ∞` (with $\top = \infty$), as the published `ManipPotential.manipPotentialAt`; the maximum over the $m!$ tiebreakers is a supremum.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s", p.10

import Mathlib
import Definitions.Def_ManipPotential_manipPotentialAt
import Definitions.Def_ManipPotential_Supplement_tieBreak

namespace ManipPotential.Supplement

/-- The manipulation potential of an SCC at electorate size `n` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3,
"Tie(breaker)s", p.10): `MP(F) := max_{≻_T ∈ L(C)} MP(F_T)`.

**Formalization Note** Valued in `ℕ∞` (`⊤ = ∞`), as the published `manipPotentialAt`
(Definition 2 at electorate size `n`); the maximum over the `m!` tiebreakers is a supremum in `ℕ∞`. -/
noncomputable def manipPotentialSCCAt {m : ℕ} [NeZero m] (F : SCC m) (n : ℕ) : ℕ∞ :=
  ⨆ T : Ranking m, manipPotentialAt (tieBreak F T) n

end ManipPotential.Supplement


