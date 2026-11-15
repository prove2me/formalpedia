-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Segment
-- name    : row23_rh_supp_RH66388Segment
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:38:20.84227+00:00
-- url     : https://prove2.me/theorems/c7d63898-d352-453b-a8dd-e50aa2599d49
-- title:
--   Row 23 RH support: RH66388Segment
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Theorems.Thm_TaoFivePrimes_rh66388_segment_cut_boundary_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_segment_cut_upper_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_segment_cut_slab_20261115
import Mathlib.Tactic
import Theorems.Thm_Arb4_H1000_E_T121_hAH
import Theorems.Thm_Arb4_H1000_S_L121_clear
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66388Count

theorem segment (ρ : ℂ) (hz : riemannZeta ρ = 0) (him0 : 0 < ρ.im)
    (himA : (121 : ℝ) ≤ ρ.im) (himB : ρ.im ≤ 66388) : ρ.re = 1 / 2 := by
  have hs : EdgeClearGlue.SlabClear (66388 : ℝ) ((66388 : ℝ) + 3 / 1000) := by
    intro x y hx0 hx1 hy0 hy1
    apply TaoFivePrimes.rh66388_segment_cut_slab_20261115 x y hx0 hx1 hy0
    linarith
  exact TaoFivePrimes.rh66388_segment_cut_boundary_20261115 hs Arb4.H1000.S_L121_clear
    TaoFivePrimes.rh66388_segment_cut_upper_20261115 Arb4.H1000.E_T121_hAH ρ hz him0 himA himB
end RH66388Count
#print axioms RH66388Count.segment


