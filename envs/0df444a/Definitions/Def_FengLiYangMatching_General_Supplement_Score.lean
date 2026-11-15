-- Prove2me | Definitions.Def_FengLiYangMatching_General_Supplement_Score
-- name    : FengLiYangMatching_General_Supplement_Score
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:19:42.335469+00:00
-- url     : https://prove2.me/theorems/991d1e3e-d06b-4818-a476-e17dc42a2c45
-- title:
--   Appendix B weighted coupled score
-- statement:
--   Fix a finite simple graph $G$, a maximum matching $M^*$, a shadow history $h=H_b$, and a reserve-phase shadow edge $e$. Use the published background graph $B$, augmented graph $B_e$, and their coupled Greedy runs with the same edge order. Let $N$ count endpoints of $e$ matched in $M(B_e)$, $R$ count its reference vertices matched there, and $K$ count its reference vertices matched in $M(B)$. The new score is
--
--   $$S^{\mathrm{tf}}=7N+4R+3K.$$
--
--   All graphs, conditional laws and counts are those of the published base definitions; only these three weights change. This is the quantity used by Lemma B.2.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), Appendix B.1, p. 26, Lemma B.2 and its preceding setup.

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement
noncomputable section

/-- Appendix B.1: the same two coupled runs, with weights (7,4,3). -/
def triangleScore {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (a b : ℝ)
    (h : History n) (e : Edge n) (w : Sample G) : ℝ :=
  let MB := coupledRun G (background G a b h e w) w
  let ME := coupledRun G (augmented G a b h e w) w
  7 * count (covered {e}) ME + 4 * count (references M h e) ME +
    3 * count (references M h e) MB

end
end FengLiYangMatching.General.Supplement


