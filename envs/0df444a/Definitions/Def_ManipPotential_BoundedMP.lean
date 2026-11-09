-- Prove2me | Definitions.Def_ManipPotential_BoundedMP
-- name    : ManipPotential_BoundedMP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:38.423649+00:00
-- url     : https://prove2.me/theorems/c7a2d5f5-ba4f-42ff-b663-f6cc7580c3cb
-- title:
--   Bounded manipulation potential (5) of a rule on rational profiles
-- statement:
--   Let $K \in \mathbb N$ and $\lambda = K + 1$. A rule $g$ on rational profiles has **bounded manipulation potential** if for every background profile $P \in \mathbb Q^{m!}_{\ge 0}$ (including $P = 0$), all rankings $r, s$ and all positive rationals $a, b$ with $a \ge \lambda b$,
--   $$
--   g(P + a\,r) \ \succeq_r\ g(P + b\,s). \qquad (5)
--   $$
--   It is the weighted form of "$\mathrm{MP} \le K$": replacing a block of weight $b$ of any ballot by weight $a \ge \lambda b$ of the truthful ballot $r$ never hurts a voter with preference $r$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.2, Eq. (5), p.26

import Mathlib
import Definitions.Def_ManipPotential_unitVec
import Definitions.Def_ManipPotential_Ranking_WeaklyPrefers

namespace ManipPotential

/-- Bounded manipulation potential (5) of a rule `g` on rational profiles (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.2, Eq. (5),
p.26), with `λ = K + 1`: for every background profile `P ∈ ℚ^{m!}_{≥0}` (including `0`), all
rankings `r, s` and positive rationals `a, b` with `a ≥ λ b`, `g(P + a r) ⪰_r g(P + b s)`. -/
def BoundedMP {m : ℕ} (K : ℕ) (g : (Ranking m → ℚ) → Fin m) : Prop :=
  ∀ P : Ranking m → ℚ, 0 ≤ P → ∀ (r s : Ranking m) (a b : ℚ), 0 < a → 0 < b →
    ((K : ℚ) + 1) * b ≤ a →
      Ranking.WeaklyPrefers r (g (P + a • unitVec r)) (g (P + b • unitVec s))

end ManipPotential


