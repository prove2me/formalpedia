-- Prove2me | Definitions.Def_OnlineCAP_traceFam
-- name    : OnlineCAP_traceFam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:35.514702+00:00
-- url     : https://prove2.me/theorems/65bffadc-dc7b-41f8-8a1a-f61fed3eec89
-- title:
--   Traces of a class of planar shapes on a point set
-- statement:
--   For a finite point set $P\subseteq\mathbb R^2$ and a class of planar shapes (bottomless, topless or leftless rectangles, TL shapes), the family of **traces** of the class on $P$ is
--   $$\{\,S\cap P : S\text{ a shape of the class}\,\}\subseteq 2^P .$$
--   It is the family $\mathcal F$ of the online $\mathcal F$-hitting set problem (Definition 4.10) on the universe $P$.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1, p.15; Definition 4.10, p.20

import Mathlib

namespace OnlineCAP

/-- **The traces of a class of planar shapes on a point set.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1, p.15 (PDF p.15): "Fix
P ⊆ R2, a fixed universe of n ≥ 1 points … We first focus on the case where each request Rt is a
bottomless rectangle", and Definition 4.10, p.20 (a family F of subsets of the universe).

For a finite point set `P` and a class of shapes `Shape`, `traceFam P Shape` is the family of
subsets `S ∩ P` of the universe `P`, `S` a shape of the class. A rounding algorithm on the
universe `P` receives these sets as requests.

**Formalization Note.** The universe is the subtype `↥P` of the points of `P`. -/
def traceFam (P : Finset (ℝ × ℝ)) (Shape : Set (ℝ × ℝ) → Prop) : Set (Set ↥P) :=
  {S | ∃ R : Set (ℝ × ℝ), Shape R ∧ S = (Subtype.val : ↥P → ℝ × ℝ) ⁻¹' R}

end OnlineCAP


