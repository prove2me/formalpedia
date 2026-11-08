-- Prove2me | Definitions.Def_OAIQ098G1656
-- name    : OAIQ098G1656
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:29:54.051782+00:00
-- url     : https://prove2.me/theorems/a23f56ee-9995-4dba-8ccf-f8131aef15f8
-- title:
--   Definitions bundle OAIQ098G1656 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 13 definitions. The definitions and types are `OAI.SharpPlanar.Residual1.box1_0`, `OAI.SharpPlanar.Residual12.box1_0`, `OAI.SharpPlanar.Residual13.box1_0`, `OAI.SharpPlanar.Residual15.box1_0`, `OAI.SharpPlanar.Residual16.box1_0`, `OAI.SharpPlanar.Residual19.box1_0`, `OAI.SharpPlanar.Residual21.box1_0`, `OAI.SharpPlanar.Residual24.box1_0`, `OAI.SharpPlanar.Residual25.box1_0`, `OAI.SharpPlanar.Residual27.box1_0`, `OAI.SharpPlanar.Residual28.box1_0`, `OAI.SharpPlanar.Residual31.box1_0`, `OAI.SharpPlanar.Residual33.box1_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_Residual1`, `PlanarPacking_Certificate_Residual12`, `PlanarPacking_Certificate_Residual13`, `PlanarPacking_Certificate_Residual15`, `PlanarPacking_Certificate_Residual16`, `PlanarPacking_Certificate_Residual19`, `PlanarPacking_Certificate_Residual21`, `PlanarPacking_Certificate_Residual24`, `PlanarPacking_Certificate_Residual25`, `PlanarPacking_Certificate_Residual27`, `PlanarPacking_Certificate_Residual28`, `PlanarPacking_Certificate_Residual31`, `PlanarPacking_Certificate_Residual33`.
--
--   **Imports.** It imports the bundles `OAIQ098G099` and `OAIQ098G1456` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Residual13.bound1_0_g`, `OAI.SharpPlanar.Residual15.bound1_0_g`, `OAI.SharpPlanar.Residual16.bound1_0_g`, `OAI.SharpPlanar.Residual31.bound1_0_g`, `OAI.SharpPlanar.Residual33.bound1_0_g`, `OAI.SharpPlanar.residual_finite_central_1_g` and `OAI.SharpPlanar.residual_finite_exterior_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G099
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
noncomputable def box1_0 : RBox := (RBox.rat (-250018302) 10000000000).add ((tm0_1_0.realAnswer).mul (qiBox 1))
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
noncomputable def box1_0 : RBox := (RBox.rat (-6005382) 10000000000).add ((tm0_12_0.realAnswer).mul (qiBox 12))
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
noncomputable def box1_0 : RBox := (RBox.rat (-574123) 10000000000).add ((tm0_13_0.realAnswer).mul (qiBox 13))
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
noncomputable def box1_0 : RBox := (RBox.rat (-11312377) 10000000000).add ((tm0_15_0.realAnswer).mul (qiBox 15))
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
noncomputable def box1_0 : RBox := (RBox.rat (5915710) 10000000000).add ((tm0_16_0.realAnswer).mul (qiBox 16))
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
noncomputable def box1_0 : RBox := (RBox.rat (-120136) 10000000000).add ((tm0_19_0.realAnswer).mul (qiBox 19))
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
noncomputable def box1_0 : RBox := (RBox.rat (177992) 10000000000).add ((tm0_21_0.realAnswer).mul (qiBox 21))
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
noncomputable def box1_0 : RBox := (RBox.rat (-1037705) 10000000000).add ((tm0_24_0.realAnswer).mul (qiBox 24))
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
noncomputable def box1_0 : RBox := (RBox.rat (1011732) 10000000000).add ((tm0_25_0.realAnswer).mul (qiBox 25))
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
noncomputable def box1_0 : RBox := (RBox.rat (-428528) 10000000000).add ((tm0_27_0.realAnswer).mul (qiBox 27))
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
noncomputable def box1_0 : RBox := (RBox.rat (399655) 10000000000).add ((tm0_28_0.realAnswer).mul (qiBox 28))
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
noncomputable def box1_0 : RBox := (RBox.rat (-31773) 10000000000).add ((tm0_31_0.realAnswer).mul (qiBox 31))
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
noncomputable def box1_0 : RBox := (RBox.rat (1240) 10000000000).add ((tm0_33_0.realAnswer).mul (qiBox 33))
end SharpPlanar.Residual33

end OAI
end


