-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsFace
-- name    : CombOpt_ChvatalRank_IsFace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:06.246839+00:00
-- url     : https://prove2.me/theorems/4940adf5-84ee-4301-95bf-17040a0b16b7
-- title:
--   Face of a polyhedron
-- statement:
--   Let $P\subseteq\mathbb R^n$. The solution set of $w^Tx=t$ with $w\ne0$ is a **supporting hyperplane** of $P$ if $w^Tx\le t$ is valid for $P$ and $P\cap\{x : w^Tx=t\}\ne\emptyset$. A set $F$ is a **face** of $P$ if it is the intersection of $P$ with a supporting hyperplane, or, by convention, if $F=\emptyset$ or $F=P$.
--
--   Lemma 6.33 moves cutting planes from a face of a polytope to the whole polytope.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF 212)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsValid

open Matrix

namespace CombOpt.ChvatalRank

/-- **Face.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 204 (PDF 212). The solution set of `wᵀx = t` is a *hyperplane* if
`w ≠ 0`; it is a *supporting hyperplane* of `P` "if wᵀx ≤ t is valid for P and P ∩ {x : wᵀx = t} ≠ ∅";
the intersection of a polyhedron with a supporting hyperplane is "a face of the polyhedron. By
convention, we also call the null set and the polyhedron itself faces". -/
def IsFace {n : ℕ} (F P : Set (Fin n → ℝ)) : Prop :=
  F = ∅ ∨ F = P ∨
    ∃ (w : Fin n → ℝ) (t : ℝ), w ≠ 0 ∧ IsValid P w t ∧ (P ∩ {x | w ⬝ᵥ x = t}).Nonempty ∧
      F = P ∩ {x | w ⬝ᵥ x = t}

end CombOpt.ChvatalRank


