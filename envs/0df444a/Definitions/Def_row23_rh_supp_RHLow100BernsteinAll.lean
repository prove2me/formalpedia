-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinAll
-- name    : row23_rh_supp_RHLow100BernsteinAll
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:50:28.269192+00:00
-- url     : https://prove2.me/theorems/4fd727ac-1430-4632-937a-080a75727a78
-- title:
--   Row 23 RH support: RHLow100BernsteinAll
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch00
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch01
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch02
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch03
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch04
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch05
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch06
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch07
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch08
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch09
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch10
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch11
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch12
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch13
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch14
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch15
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch16
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch17
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch18
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch19
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch20
import Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RHLow100Bernstein
theorem all_boxes : (∀ (i : Fin 86) (j : ℕ), j < (CertifiedLocalBoxes.rowSpecs i).length →
      CertifiedStreamingLocalBoxes.valid i j (CertifiedStreamingLocalBoxes.certificateAt i j)) ∧
    (∀ i : Fin 86, (CertifiedLocalBoxes.rowSpecs i).length ≤ 2) := by
  constructor
  · intro i j hj
    fin_cases i
    · change j < 1 at hj
      interval_cases j
      · exact row00box0
    · change j < 1 at hj
      interval_cases j
      · exact row01box0
    · change j < 1 at hj
      interval_cases j
      · exact row02box0
    · change j < 1 at hj
      interval_cases j
      · exact row03box0
    · change j < 1 at hj
      interval_cases j
      · exact row04box0
    · change j < 1 at hj
      interval_cases j
      · exact row05box0
    · change j < 1 at hj
      interval_cases j
      · exact row06box0
    · change j < 1 at hj
      interval_cases j
      · exact row07box0
    · change j < 1 at hj
      interval_cases j
      · exact row08box0
    · change j < 1 at hj
      interval_cases j
      · exact row09box0
    · change j < 1 at hj
      interval_cases j
      · exact row10box0
    · change j < 1 at hj
      interval_cases j
      · exact row11box0
    · change j < 1 at hj
      interval_cases j
      · exact row12box0
    · change j < 1 at hj
      interval_cases j
      · exact row13box0
    · change j < 1 at hj
      interval_cases j
      · exact row14box0
    · change j < 1 at hj
      interval_cases j
      · exact row15box0
    · change j < 1 at hj
      interval_cases j
      · exact row16box0
    · change j < 1 at hj
      interval_cases j
      · exact row17box0
    · change j < 1 at hj
      interval_cases j
      · exact row18box0
    · change j < 1 at hj
      interval_cases j
      · exact row19box0
    · change j < 1 at hj
      interval_cases j
      · exact row20box0
    · change j < 1 at hj
      interval_cases j
      · exact row21box0
    · change j < 1 at hj
      interval_cases j
      · exact row22box0
    · change j < 1 at hj
      interval_cases j
      · exact row23box0
    · change j < 1 at hj
      interval_cases j
      · exact row24box0
    · change j < 1 at hj
      interval_cases j
      · exact row25box0
    · change j < 1 at hj
      interval_cases j
      · exact row26box0
    · change j < 1 at hj
      interval_cases j
      · exact row27box0
    · change j < 1 at hj
      interval_cases j
      · exact row28box0
    · change j < 1 at hj
      interval_cases j
      · exact row29box0
    · change j < 1 at hj
      interval_cases j
      · exact row30box0
    · change j < 1 at hj
      interval_cases j
      · exact row31box0
    · change j < 1 at hj
      interval_cases j
      · exact row32box0
    · change j < 1 at hj
      interval_cases j
      · exact row33box0
    · change j < 2 at hj
      interval_cases j
      · exact row34box0
      · exact row34box1
    · change j < 1 at hj
      interval_cases j
      · exact row35box0
    · change j < 1 at hj
      interval_cases j
      · exact row36box0
    · change j < 1 at hj
      interval_cases j
      · exact row37box0
    · change j < 1 at hj
      interval_cases j
      · exact row38box0
    · change j < 1 at hj
      interval_cases j
      · exact row39box0
    · change j < 1 at hj
      interval_cases j
      · exact row40box0
    · change j < 1 at hj
      interval_cases j
      · exact row41box0
    · change j < 1 at hj
      interval_cases j
      · exact row42box0
    · change j < 1 at hj
      interval_cases j
      · exact row43box0
    · change j < 1 at hj
      interval_cases j
      · exact row44box0
    · change j < 2 at hj
      interval_cases j
      · exact row45box0
      · exact row45box1
    · change j < 1 at hj
      interval_cases j
      · exact row46box0
    · change j < 1 at hj
      interval_cases j
      · exact row47box0
    · change j < 1 at hj
      interval_cases j
      · exact row48box0
    · change j < 1 at hj
      interval_cases j
      · exact row49box0
    · change j < 1 at hj
      interval_cases j
      · exact row50box0
    · change j < 2 at hj
      interval_cases j
      · exact row51box0
      · exact row51box1
    · change j < 1 at hj
      interval_cases j
      · exact row52box0
    · change j < 2 at hj
      interval_cases j
      · exact row53box0
      · exact row53box1
    · change j < 1 at hj
      interval_cases j
      · exact row54box0
    · change j < 1 at hj
      interval_cases j
      · exact row55box0
    · change j < 1 at hj
      interval_cases j
      · exact row56box0
    · change j < 1 at hj
      interval_cases j
      · exact row57box0
    · change j < 1 at hj
      interval_cases j
      · exact row58box0
    · change j < 1 at hj
      interval_cases j
      · exact row59box0
    · change j < 1 at hj
      interval_cases j
      · exact row60box0
    · change j < 1 at hj
      interval_cases j
      · exact row61box0
    · change j < 1 at hj
      interval_cases j
      · exact row62box0
    · change j < 2 at hj
      interval_cases j
      · exact row63box0
      · exact row63box1
    · change j < 1 at hj
      interval_cases j
      · exact row64box0
    · change j < 1 at hj
      interval_cases j
      · exact row65box0
    · change j < 1 at hj
      interval_cases j
      · exact row66box0
    · change j < 1 at hj
      interval_cases j
      · exact row67box0
    · change j < 1 at hj
      interval_cases j
      · exact row68box0
    · change j < 1 at hj
      interval_cases j
      · exact row69box0
    · change j < 1 at hj
      interval_cases j
      · exact row70box0
    · change j < 1 at hj
      interval_cases j
      · exact row71box0
    · change j < 1 at hj
      interval_cases j
      · exact row72box0
    · change j < 2 at hj
      interval_cases j
      · exact row73box0
      · exact row73box1
    · change j < 1 at hj
      interval_cases j
      · exact row74box0
    · change j < 1 at hj
      interval_cases j
      · exact row75box0
    · change j < 1 at hj
      interval_cases j
      · exact row76box0
    · change j < 1 at hj
      interval_cases j
      · exact row77box0
    · change j < 1 at hj
      interval_cases j
      · exact row78box0
    · change j < 1 at hj
      interval_cases j
      · exact row79box0
    · change j < 1 at hj
      interval_cases j
      · exact row80box0
    · change j < 2 at hj
      interval_cases j
      · exact row81box0
      · exact row81box1
    · change j < 1 at hj
      interval_cases j
      · exact row82box0
    · change j < 1 at hj
      interval_cases j
      · exact row83box0
    · change j < 1 at hj
      interval_cases j
      · exact row84box0
    · change j < 1 at hj
      interval_cases j
      · exact row85box0
  · intro i
    fin_cases i <;> decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.all_boxes


