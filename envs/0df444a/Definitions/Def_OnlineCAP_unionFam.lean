-- Prove2me | Definitions.Def_OnlineCAP_unionFam
-- name    : OnlineCAP_unionFam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:44.447249+00:00
-- url     : https://prove2.me/theorems/6ff5f940-d433-4783-935e-8d169506ad43
-- title:
--   The family of unions F₃ = {S₁ ∪ S₂}
-- statement:
--   For two families $\mathcal F_1,\mathcal F_2$ of subsets of a universe $U$,
--   $$\mathcal F_3=\{S_1\cup S_2 : S_1\in\mathcal F_1,\ S_2\in\mathcal F_2\}.$$
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 4.12, p.21

import Mathlib

namespace OnlineCAP

/-- **The family of unions.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 4.12, p.21 (PDF p.21) and §4.2, p.20: "F3 = {S1 ∪ S2 :
S1 ∈ F1, S2 ∈ F2}". -/
def unionFam {U : Type} (F₁ F₂ : Set (Set U)) : Set (Set U) :=
  {S | ∃ S₁ ∈ F₁, ∃ S₂ ∈ F₂, S = S₁ ∪ S₂}

end OnlineCAP


