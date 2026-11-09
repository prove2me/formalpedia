-- Prove2me | Definitions.Def_ManipPotential_GAxioms
-- name    : ManipPotential_GAxioms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:50:23.583472+00:00
-- url     : https://prove2.me/theorems/73bcd1e2-7f23-4cf8-8909-9843de91683e
-- title:
--   The axioms of Lemma 6.2 for a rule $g$ with $\lambda = K+1$
-- statement:
--   For $K \in \mathbb N$ and $\lambda = K + 1$, a rule $g$ on rational profiles satisfies **the axioms of Lemma 6.2** if it is weighted faithful, has bounded manipulation potential (5) with constant $\lambda$, and satisfies conditional participation.
--
--   Lemma 6.2 produces such a $g$ from any anonymous onto SCF with $\mathrm{MP} \le K$ at every electorate size; every later step of the proof of Theorem 6.1 uses only these three axioms.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.2, p.26

import Mathlib
import Definitions.Def_ManipPotential_Faithful
import Definitions.Def_ManipPotential_BoundedMP
import Definitions.Def_ManipPotential_CondParticipation

namespace ManipPotential

/-- The three axioms of Lemma 6.2 for a rule `g` on rational profiles, with `λ = K + 1` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…),
Lemma 6.2, p.26): weighted faithfulness, bounded manipulation potential (5), conditional
participation. -/
def GAxioms {m : ℕ} [NeZero m] (K : ℕ) (g : (Ranking m → ℚ) → Fin m) : Prop :=
  Faithful g ∧ BoundedMP K g ∧ CondParticipation g

end ManipPotential


