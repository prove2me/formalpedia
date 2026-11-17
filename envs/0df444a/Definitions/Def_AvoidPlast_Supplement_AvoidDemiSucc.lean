-- Prove2me | Definitions.Def_AvoidPlast_Supplement_AvoidDemiSucc
-- name    : AvoidPlast_Supplement_AvoidDemiSucc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:06:12.205765+00:00
-- url     : https://prove2.me/theorems/e5acc050-7882-4837-92d4-76306570eb4f
-- title:
--   Completeness event for Avoid on $C_s$
-- statement:
--   $\exists w: A(C_s,w)\in\{0,1\}^n\setminus\mathrm{Range}(C_s)$: some polynomially long witness is accepted by $A$ on the index $s$ with an $n$-bit output outside the range of $C_s$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 6.5, 6.6, Corollary 6.7, pp.34–37

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Supplement_inRangeDemi

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The completeness event of Theorems 6.5, 6.6 and Corollary 6.7 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), pp.34–37):
`∃ w : A(C_s, w) ∈ {0,1}^n \ Range(C_s)`. The non-deterministic `A` reads the index `s` and a
witness of polynomial length; rejecting is the output `⊥`. -/
def AvoidDemiSucc (A : Machine 2) (a : ℕ) (g : ℕ → List Bool → List Bool) (lam t : ℕ → ℕ)
    (n : ℕ) (s : List Bool) : Prop :=
  ∃ w : List Bool, w.length ≤ a * (s.length ^ a + 1) ∧ Accepts A ![s, w] ∧
    (output A ![s, w]).length = n ∧ ¬ inRangeDemi g lam t n s (output A ![s, w])

end AvoidPlast.Supplement


