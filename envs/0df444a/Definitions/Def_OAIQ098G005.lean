-- Prove2me | Definitions.Def_OAIQ098G005
-- name    : OAIQ098G005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:55:59.447205+00:00
-- url     : https://prove2.me/theorems/aaf0cf59-b130-4058-a389-7f3bd16bcd53
-- title:
--   Definitions bundle OAIQ098G005 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.Numerical.Aplus`, `OAI.SharpPlanar.Numerical.Wplus`, `OAI.SharpPlanar.Numerical.WplusInt`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_WCertificates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WCertificates.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G102`; the statements `OAI.SharpPlanar.Numerical.U100.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U12.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U13.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U15.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U16.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U19.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U24.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U25.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U27.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U9.wuplus_column_g`, `OAI.SharpPlanar.Numerical.defectplus_column_g` and `OAI.SharpPlanar.Numerical.defectplus_lt_one_g`; the proof of `OAI.SharpPlanar.Numerical.defectplus_lt_one_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G004

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open scoped BigOperators
noncomputable def WplusInt : Matrix (Fin 6) (Fin 6) ℤ := ![![4159,4452,(-2003),(-10467),(-2421),(-1683)],
![2714,6573,1689,8258,104,(-335)],
![(-4675),4785,7003,(-13100),(-1355),(-1163)],
![36853,(-37142),27514,105973,1100,2012],
![57838,(-56941),36296,158623,29097,17293],
![(-4705),3589,(-3311),(-11932),(-2562),6919]]
noncomputable def Wplus : Matrix (Fin 6) (Fin 6) ℝ := fun i j => (WplusInt i j:ℝ)/10000
noncomputable def Aplus : Matrix (Fin 6) (Fin 6) ℝ := 1 - Dmat
end SharpPlanar.Numerical

end OAI
end


