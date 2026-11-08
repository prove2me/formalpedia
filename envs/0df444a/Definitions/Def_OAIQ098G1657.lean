-- Prove2me | Definitions.Def_OAIQ098G1657
-- name    : OAIQ098G1657
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:30.497201+00:00
-- url     : https://prove2.me/theorems/31a7cc66-0a46-4e25-a5e0-fdace2850264
-- title:
--   Definitions bundle OAIQ098G1657 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 13 definitions. The definitions and types are `OAI.SharpPlanar.Residual1.box1_1`, `OAI.SharpPlanar.Residual12.box1_1`, `OAI.SharpPlanar.Residual13.box1_1`, `OAI.SharpPlanar.Residual15.box1_1`, `OAI.SharpPlanar.Residual16.box1_1`, `OAI.SharpPlanar.Residual19.box1_1`, `OAI.SharpPlanar.Residual21.box1_1`, `OAI.SharpPlanar.Residual24.box1_1`, `OAI.SharpPlanar.Residual25.box1_1`, `OAI.SharpPlanar.Residual27.box1_1`, `OAI.SharpPlanar.Residual28.box1_1`, `OAI.SharpPlanar.Residual31.box1_1`, `OAI.SharpPlanar.Residual33.box1_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_Residual1`, `PlanarPacking_Certificate_Residual12`, `PlanarPacking_Certificate_Residual13`, `PlanarPacking_Certificate_Residual15`, `PlanarPacking_Certificate_Residual16`, `PlanarPacking_Certificate_Residual19`, `PlanarPacking_Certificate_Residual21`, `PlanarPacking_Certificate_Residual24`, `PlanarPacking_Certificate_Residual25`, `PlanarPacking_Certificate_Residual27`, `PlanarPacking_Certificate_Residual28`, `PlanarPacking_Certificate_Residual31`, `PlanarPacking_Certificate_Residual33`.
--
--   **Imports.** It imports the bundles `OAIQ098G100` and `OAIQ098G1456` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Residual12.bound1_1_g`, `OAI.SharpPlanar.Residual13.bound1_1_g`, `OAI.SharpPlanar.Residual15.bound1_1_g`, `OAI.SharpPlanar.Residual16.bound1_1_g`, `OAI.SharpPlanar.Residual19.bound1_1_g`, `OAI.SharpPlanar.Residual21.bound1_1_g`, `OAI.SharpPlanar.Residual24.bound1_1_g`, `OAI.SharpPlanar.Residual25.bound1_1_g`, `OAI.SharpPlanar.Residual27.bound1_1_g`, `OAI.SharpPlanar.Residual28.bound1_1_g`, `OAI.SharpPlanar.Residual31.bound1_1_g`, `OAI.SharpPlanar.Residual33.bound1_1_g` and `OAI.SharpPlanar.residual_finite_central_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G100
import Definitions.Def_OAIQ098G1456

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual1
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

namespace SharpPlanar.Residual1
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (4107732082) 10000000000).add ((tm0_1_1.realAnswer.add (((dBox 1).mul tm0_1_0.realAnswer).neg)).mul (qiBox 1))
end SharpPlanar.Residual1

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
noncomputable def box1_1 : RBox := (RBox.rat (34369042) 10000000000).add ((tm0_12_1.realAnswer.add (((dBox 12).mul tm0_12_0.realAnswer).neg)).mul (qiBox 12))
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
noncomputable def box1_1 : RBox := (RBox.rat (-75237042) 10000000000).add ((tm0_13_1.realAnswer.add (((dBox 13).mul tm0_13_0.realAnswer).neg)).mul (qiBox 13))
end SharpPlanar.Residual13

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual15
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

namespace SharpPlanar.Residual15
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-34985096) 10000000000).add ((tm0_15_1.realAnswer.add (((dBox 15).mul tm0_15_0.realAnswer).neg)).mul (qiBox 15))
end SharpPlanar.Residual15

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual16
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

namespace SharpPlanar.Residual16
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-10980954) 10000000000).add ((tm0_16_1.realAnswer.add (((dBox 16).mul tm0_16_0.realAnswer).neg)).mul (qiBox 16))
end SharpPlanar.Residual16

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual19
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

namespace SharpPlanar.Residual19
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (1498351) 10000000000).add ((tm0_19_1.realAnswer.add (((dBox 19).mul tm0_19_0.realAnswer).neg)).mul (qiBox 19))
end SharpPlanar.Residual19

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual21
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

namespace SharpPlanar.Residual21
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (747946) 10000000000).add ((tm0_21_1.realAnswer.add (((dBox 21).mul tm0_21_0.realAnswer).neg)).mul (qiBox 21))
end SharpPlanar.Residual21

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual24
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

namespace SharpPlanar.Residual24
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (105643) 10000000000).add ((tm0_24_1.realAnswer.add (((dBox 24).mul tm0_24_0.realAnswer).neg)).mul (qiBox 24))
end SharpPlanar.Residual24

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual25
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

namespace SharpPlanar.Residual25
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-6510015) 10000000000).add ((tm0_25_1.realAnswer.add (((dBox 25).mul tm0_25_0.realAnswer).neg)).mul (qiBox 25))
end SharpPlanar.Residual25

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual27
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

namespace SharpPlanar.Residual27
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (-4440927) 10000000000).add ((tm0_27_1.realAnswer.add (((dBox 27).mul tm0_27_0.realAnswer).neg)).mul (qiBox 27))
end SharpPlanar.Residual27

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual28
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

namespace SharpPlanar.Residual28
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (403751) 10000000000).add ((tm0_28_1.realAnswer.add (((dBox 28).mul tm0_28_0.realAnswer).neg)).mul (qiBox 28))
end SharpPlanar.Residual28

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual31
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

namespace SharpPlanar.Residual31
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (90515) 10000000000).add ((tm0_31_1.realAnswer.add (((dBox 31).mul tm0_31_0.realAnswer).neg)).mul (qiBox 31))
end SharpPlanar.Residual31

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual33
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

namespace SharpPlanar.Residual33
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_1 : RBox := (RBox.rat (99081) 10000000000).add ((tm0_33_1.realAnswer.add (((dBox 33).mul tm0_33_0.realAnswer).neg)).mul (qiBox 33))
end SharpPlanar.Residual33

end OAI
end


