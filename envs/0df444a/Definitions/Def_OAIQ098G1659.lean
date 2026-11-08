-- Prove2me | Definitions.Def_OAIQ098G1659
-- name    : OAIQ098G1659
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:49:07.936782+00:00
-- url     : https://prove2.me/theorems/5d164fe5-d95c-4f50-ab4a-d626d7361037
-- title:
--   Definitions bundle OAIQ098G1659 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 20 definitions. The definitions and types are `OAI.SharpPlanar.Residual100.box0_1`, `OAI.SharpPlanar.Residual12.box0_1`, `OAI.SharpPlanar.Residual13.box0_1`, `OAI.SharpPlanar.Residual7.box1_1`, `OAI.SharpPlanar.Residual72.box1_1`, `OAI.SharpPlanar.Residual73.box1_1`, `OAI.SharpPlanar.Residual75.box1_1`, `OAI.SharpPlanar.Residual76.box1_1`, `OAI.SharpPlanar.Residual79.box1_1`, `OAI.SharpPlanar.Residual81.box1_1`, `OAI.SharpPlanar.Residual84.box1_1`, `OAI.SharpPlanar.Residual85.box1_1`, `OAI.SharpPlanar.Residual87.box1_1`, `OAI.SharpPlanar.Residual88.box1_1`, `OAI.SharpPlanar.Residual9.box1_1`, `OAI.SharpPlanar.Residual91.box1_1`, `OAI.SharpPlanar.Residual93.box1_1`, `OAI.SharpPlanar.Residual96.box1_1`, `OAI.SharpPlanar.Residual97.box1_1`, `OAI.SharpPlanar.Residual99.box1_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_Residual100`, `PlanarPacking_Certificate_Residual12`, `PlanarPacking_Certificate_Residual13`, `PlanarPacking_Certificate_Residual7`, `PlanarPacking_Certificate_Residual72`, `PlanarPacking_Certificate_Residual73`, `PlanarPacking_Certificate_Residual75`, `PlanarPacking_Certificate_Residual76`, `PlanarPacking_Certificate_Residual79`, `PlanarPacking_Certificate_Residual81`, `PlanarPacking_Certificate_Residual84`, `PlanarPacking_Certificate_Residual85`, `PlanarPacking_Certificate_Residual87`, `PlanarPacking_Certificate_Residual88`, `PlanarPacking_Certificate_Residual9`, `PlanarPacking_Certificate_Residual91`, `PlanarPacking_Certificate_Residual93`, `PlanarPacking_Certificate_Residual96`, `PlanarPacking_Certificate_Residual97`, `PlanarPacking_Certificate_Residual99`.
--
--   **Imports.** It imports the bundles `OAIQ098G100` and `OAIQ098G1533` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Residual100.bound0_1_g`, `OAI.SharpPlanar.Residual12.bound0_1_g`, `OAI.SharpPlanar.Residual13.bound0_1_g`, `OAI.SharpPlanar.Residual72.bound1_1_g`, `OAI.SharpPlanar.Residual73.bound1_1_g`, `OAI.SharpPlanar.Residual75.bound1_1_g`, `OAI.SharpPlanar.Residual76.bound1_1_g`, `OAI.SharpPlanar.Residual79.bound1_1_g`, `OAI.SharpPlanar.Residual7.bound1_1_g`, `OAI.SharpPlanar.Residual81.bound1_1_g`, `OAI.SharpPlanar.Residual84.bound1_1_g`, `OAI.SharpPlanar.Residual85.bound1_1_g`, `OAI.SharpPlanar.Residual87.bound1_1_g`, `OAI.SharpPlanar.Residual88.bound1_1_g`, `OAI.SharpPlanar.Residual91.bound1_1_g`, `OAI.SharpPlanar.Residual93.bound1_1_g`, `OAI.SharpPlanar.Residual96.bound1_1_g`, `OAI.SharpPlanar.Residual97.bound1_1_g`, `OAI.SharpPlanar.Residual99.bound1_1_g` and `OAI.SharpPlanar.Residual9.bound1_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G100
import Definitions.Def_OAIQ098G1533

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual100
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

namespace SharpPlanar.Residual100
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_1 : RBox := (RBox.rat (2) 10000000000).add ((tm1_100_1.realAnswer.add (((dBox 100).mul tm1_100_0.realAnswer).neg)).mul (qiBox 100))
end SharpPlanar.Residual100

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual12
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

namespace SharpPlanar.Residual12
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_1 : RBox := (RBox.rat (-34846939) 10000000000).add ((tm1_12_1.realAnswer.add (((dBox 12).mul tm1_12_0.realAnswer).neg)).mul (qiBox 12))
end SharpPlanar.Residual12

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual13
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

namespace SharpPlanar.Residual13
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_1 : RBox := (RBox.rat (63030995) 10000000000).add ((tm1_13_1.realAnswer.add (((dBox 13).mul tm1_13_0.realAnswer).neg)).mul (qiBox 13))
end SharpPlanar.Residual13

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual7
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

namespace SharpPlanar.Residual7
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (21637038) 10000000000).add ((tm0_7_1.realAnswer.add (((dBox 7).mul tm0_7_0.realAnswer).neg)).mul (qiBox 7))
end SharpPlanar.Residual7

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual72
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

namespace SharpPlanar.Residual72
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-301) 10000000000).add ((tm0_72_1.realAnswer.add (((dBox 72).mul tm0_72_0.realAnswer).neg)).mul (qiBox 72))
end SharpPlanar.Residual72

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual73
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

namespace SharpPlanar.Residual73
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (685) 10000000000).add ((tm0_73_1.realAnswer.add (((dBox 73).mul tm0_73_0.realAnswer).neg)).mul (qiBox 73))
end SharpPlanar.Residual73

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual75
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

namespace SharpPlanar.Residual75
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (338) 10000000000).add ((tm0_75_1.realAnswer.add (((dBox 75).mul tm0_75_0.realAnswer).neg)).mul (qiBox 75))
end SharpPlanar.Residual75

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual76
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

namespace SharpPlanar.Residual76
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (104) 10000000000).add ((tm0_76_1.realAnswer.add (((dBox 76).mul tm0_76_0.realAnswer).neg)).mul (qiBox 76))
end SharpPlanar.Residual76

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual79
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

namespace SharpPlanar.Residual79
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-15) 10000000000).add ((tm0_79_1.realAnswer.add (((dBox 79).mul tm0_79_0.realAnswer).neg)).mul (qiBox 79))
end SharpPlanar.Residual79

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual81
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

namespace SharpPlanar.Residual81
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-8) 10000000000).add ((tm0_81_1.realAnswer.add (((dBox 81).mul tm0_81_0.realAnswer).neg)).mul (qiBox 81))
end SharpPlanar.Residual81

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual84
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

namespace SharpPlanar.Residual84
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (0) 10000000000).add ((tm0_84_1.realAnswer.add (((dBox 84).mul tm0_84_0.realAnswer).neg)).mul (qiBox 84))
end SharpPlanar.Residual84

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual85
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

namespace SharpPlanar.Residual85
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (70) 10000000000).add ((tm0_85_1.realAnswer.add (((dBox 85).mul tm0_85_0.realAnswer).neg)).mul (qiBox 85))
end SharpPlanar.Residual85

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual87
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

namespace SharpPlanar.Residual87
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (49) 10000000000).add ((tm0_87_1.realAnswer.add (((dBox 87).mul tm0_87_0.realAnswer).neg)).mul (qiBox 87))
end SharpPlanar.Residual87

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual88
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

namespace SharpPlanar.Residual88
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-5) 10000000000).add ((tm0_88_1.realAnswer.add (((dBox 88).mul tm0_88_0.realAnswer).neg)).mul (qiBox 88))
end SharpPlanar.Residual88

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual9
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

namespace SharpPlanar.Residual9
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (2145806) 10000000000).add ((tm0_9_1.realAnswer.add (((dBox 9).mul tm0_9_0.realAnswer).neg)).mul (qiBox 9))
end SharpPlanar.Residual9

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual91
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

namespace SharpPlanar.Residual91
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-1) 10000000000).add ((tm0_91_1.realAnswer.add (((dBox 91).mul tm0_91_0.realAnswer).neg)).mul (qiBox 91))
end SharpPlanar.Residual91

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual93
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

namespace SharpPlanar.Residual93
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-1) 10000000000).add ((tm0_93_1.realAnswer.add (((dBox 93).mul tm0_93_0.realAnswer).neg)).mul (qiBox 93))
end SharpPlanar.Residual93

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual96
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

namespace SharpPlanar.Residual96
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (3) 10000000000).add ((tm0_96_1.realAnswer.add (((dBox 96).mul tm0_96_0.realAnswer).neg)).mul (qiBox 96))
end SharpPlanar.Residual96

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual97
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

namespace SharpPlanar.Residual97
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (4) 10000000000).add ((tm0_97_1.realAnswer.add (((dBox 97).mul tm0_97_0.realAnswer).neg)).mul (qiBox 97))
end SharpPlanar.Residual97

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual99
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

namespace SharpPlanar.Residual99
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (5) 10000000000).add ((tm0_99_1.realAnswer.add (((dBox 99).mul tm0_99_0.realAnswer).neg)).mul (qiBox 99))
end SharpPlanar.Residual99

end OAI
end


