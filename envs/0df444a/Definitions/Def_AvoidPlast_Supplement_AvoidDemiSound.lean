-- Prove2me | Definitions.Def_AvoidPlast_Supplement_AvoidDemiSound
-- name    : AvoidPlast_Supplement_AvoidDemiSound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:07:03.936212+00:00
-- url     : https://prove2.me/theorems/12a7afa3-4674-4b24-9253-88da7e320fcb
-- title:
--   Soundness event for Avoid on $C_s$
-- statement:
--   $\forall w: A(C_s,w)\notin\mathrm{Range}(C_s)$, rejection (the output $\bot$) counting as outside the range.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 6.5, 6.6, Corollary 6.7, pp.34–37

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Supplement_inRangeDemi

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The soundness event of Theorems 6.5, 6.6 and Corollary 6.7 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), pp.34–37):
`∀ w : A(C_s, w) ∉ Range(C_s)`, the output `⊥` (rejection) counting as outside the range. -/
def AvoidDemiSound (A : Machine 2) (a : ℕ) (g : ℕ → List Bool → List Bool) (lam t : ℕ → ℕ)
    (n : ℕ) (s : List Bool) : Prop :=
  ∀ w : List Bool, w.length ≤ a * (s.length ^ a + 1) → Accepts A ![s, w] →
    ¬ inRangeDemi g lam t n s (output A ![s, w])

end AvoidPlast.Supplement


