-- Prove2me | Definitions.Def_row23_rh_supp_RH67156Segment
-- name    : row23_rh_supp_RH67156Segment
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:51:52.11955+00:00
-- url     : https://prove2.me/theorems/0b05ac93-5b43-4b44-9725-83d3f30bf32a
-- title:
--   Row 23 RH support: RH67156Segment
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156CountCapstoneConditional
import Definitions.Def_row23_rh_supp_RH67156UpperEdge
import Definitions.Def_row23_rh_supp_RH67156TopSlab16Final
import Theorems.Thm_Arb4_H1000_E_T121_hAH
import Theorems.Thm_Arb4_H1000_S_L121_clear
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH67156Count

theorem segment (ρ : ℂ) (hz : riemannZeta ρ = 0) (him0 : 0 < ρ.im)
    (himA : (121 : ℝ) ≤ ρ.im) (himB : ρ.im ≤ 67156) : ρ.re = 1 / 2 := by
  have hs : EdgeClearGlue.SlabClear (67156 : ℝ) ((67156 : ℝ) + 3 / 1000) := by
    intro x y hx0 hx1 hy0 hy1
    apply RH67156TopSlab16R016.top_slab_clear x y hx0 hx1 hy0
    linarith
  exact segment_of_boundary_inputs hs Arb4.H1000.S_L121_clear RH67156Edge.upper_edge
    Arb4.H1000.E_T121_hAH ρ hz him0 himA himB
end RH67156Count
#print axioms RH67156Count.segment


