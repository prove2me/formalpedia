-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMass8
-- name    : row23_rh_supp_RHLocalMass8
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:23:23.647743+00:00
-- url     : https://prove2.me/theorems/9852b189-db73-400d-a36e-25663c06082f
-- title:
--   Row 23 RH support: RHLocalMass8
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalMass8Cell00
import Definitions.Def_row23_rh_supp_RHLocalMass8Cell01
import Definitions.Def_row23_rh_supp_RHLocalMass8Cell02
import Definitions.Def_row23_rh_supp_RHLocalMass8Cell03
import Definitions.Def_row23_rh_supp_RHLocalMass8Cell04
import Definitions.Def_row23_rh_supp_RHLocalMass8Cell05
import Definitions.Def_row23_rh_supp_RHLocalMass8Cell06
import Definitions.Def_row23_rh_supp_RHLocalMass8Cell07
import Definitions.Def_row23_rh_supp_RHLocalMass8Cell08
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
namespace RHLocalMass8
open Polynomial Finset MeasureTheory intervalIntegral DusartLegendreSmoothing
noncomputable def nodes : List ℚ := [(0/1:ℚ), (3971/200000:ℚ), (101667/1000000:ℚ), (118617/500000:ℚ), (408283/1000000:ℚ), (591717/1000000:ℚ), (381383/500000:ℚ), (898333/1000000:ℚ), (196029/200000:ℚ), (1/1:ℚ)]
noncomputable def bounds : List ℚ := [(86121562721/10000000000000:ℚ), (211997673967/10000000000000:ℚ), (275053823929/10000000000000:ℚ), (61897312149/2000000000000:ℚ), (320616633211/10000000000000:ℚ), (309486561743/10000000000000:ℚ), (275053825583/10000000000000:ℚ), (211997675661/10000000000000:ℚ), (86121563487/10000000000000:ℚ)]
theorem integral_bound :
    (∫ t : ℝ in 0..1, |(p.map (Rat.castHom ℝ)).eval t|) ≤ ((2085935881047/10000000000000:ℚ):ℝ) := by
  have h := partition_integral_abs_bound (p.map (Rat.castHom ℝ)) 9
    (fun i => (nodes.getD i 0:ℝ)) (by norm_num [nodes]) (by norm_num [nodes])
    (fun i => (bounds.getD i 0:ℝ)) (by
      intro i hi
      interval_cases i
      · simpa [nodes,bounds] using cell00
      · simpa [nodes,bounds] using cell01
      · simpa [nodes,bounds] using cell02
      · simpa [nodes,bounds] using cell03
      · simpa [nodes,bounds] using cell04
      · simpa [nodes,bounds] using cell05
      · simpa [nodes,bounds] using cell06
      · simpa [nodes,bounds] using cell07
      · simpa [nodes,bounds] using cell08
    )
  norm_num [bounds,Finset.sum_range_succ] at h ⊢
  exact h
theorem mass_bound : DusartLegendreSmoothing.derivativeMass 8 ((1/1000000000:ℚ):ℝ) ≤ (1841000000:ℝ) := by
  rw [DusartLegendreSmoothing.derivativeMass_rational_polynomial 8 (1/1000000000:ℚ) (by norm_num)]
  have h := mul_le_mul_of_nonneg_left integral_bound
    (by positivity : (0:ℝ) ≤ ((2*8+1).factorial:ℝ)/((8).factorial:ℝ))
  exact h.trans (by norm_num)
end RHLocalMass8
#print axioms RHLocalMass8.mass_bound


