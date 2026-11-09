-- Prove2me | Definitions.Def_ManipPotential_IsFullyLabelled
-- name    : ManipPotential_IsFullyLabelled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:43.22358+00:00
-- url     : https://prove2.me/theorems/d30c65e2-2262-43e7-a496-bf859140fe92
-- title:
--   Fully labelled elementary simplex
-- statement:
--   An elementary simplex (a face with $d + 1$ vertices) is **fully labelled** if its $d + 1$ vertices carry distinct labels, i.e. every label in $[d+1]$ appears on one of its vertices.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30 (before Lemma 6.8)

import Mathlib

namespace ManipPotential

/-- A fully labelled elementary simplex (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30, before Lemma 6.8): a face with
`d + 1` vertices carrying all `d + 1` labels (equivalently, `d + 1` distinct labels). -/
def IsFullyLabelled {E : Type*} {d : ℕ} (lab : E → Fin (d + 1)) (s : Finset E) : Prop :=
  s.card = d + 1 ∧ ∀ j : Fin (d + 1), ∃ v ∈ s, lab v = j

end ManipPotential


