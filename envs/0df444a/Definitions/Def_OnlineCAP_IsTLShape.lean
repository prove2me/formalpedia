-- Prove2me | Definitions.Def_OnlineCAP_IsTLShape
-- name    : OnlineCAP_IsTLShape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:44.22522+00:00
-- url     : https://prove2.me/theorems/1693130b-3e41-49ce-9932-4ea81f9055a9
-- title:
--   TL shape: union of a leftless and a topless rectangle
-- statement:
--   A **TL shape** is a set $S=R_L\cup R_T\subseteq\mathbb R^2$, the union of a leftless rectangle $R_L$ and a topless rectangle $R_T$. These are the requests of online TL-rectangle hitting set.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Definition 1.8, p.4; Problem 1.9, p.5

import Mathlib
import Definitions.Def_OnlineCAP_IsLeftless
import Definitions.Def_OnlineCAP_IsTopless

namespace OnlineCAP

/-- **TL shape.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Definition 1.8, p.4 and Problem 1.9, p.5 (PDF p.5): "a shape S ⊆ R2
arrives to be hit where S = RL ∪ RT is the union of a leftless rectangle RL and a topless
rectangle RT". -/
def IsTLShape (S : Set (ℝ × ℝ)) : Prop :=
  ∃ R T : Set (ℝ × ℝ), IsLeftless R ∧ IsTopless T ∧ S = R ∪ T

end OnlineCAP


