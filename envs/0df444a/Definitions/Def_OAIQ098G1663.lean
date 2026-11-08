-- Prove2me | Definitions.Def_OAIQ098G1663
-- name    : OAIQ098G1663
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:30:10.778282+00:00
-- url     : https://prove2.me/theorems/a10c13f4-9621-4cce-b208-5f278908f0a2
-- title:
--   Definitions bundle OAIQ098G1663 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 20 definitions. The definitions and types are `OAI.SharpPlanar.Residual3.box1_0`, `OAI.SharpPlanar.Residual36.box1_0`, `OAI.SharpPlanar.Residual37.box1_0`, `OAI.SharpPlanar.Residual39.box1_0`, `OAI.SharpPlanar.Residual4.box1_0`, `OAI.SharpPlanar.Residual40.box1_0`, `OAI.SharpPlanar.Residual43.box1_0`, `OAI.SharpPlanar.Residual45.box1_0`, `OAI.SharpPlanar.Residual48.box1_0`, `OAI.SharpPlanar.Residual49.box1_0`, `OAI.SharpPlanar.Residual51.box1_0`, `OAI.SharpPlanar.Residual52.box1_0`, `OAI.SharpPlanar.Residual55.box1_0`, `OAI.SharpPlanar.Residual57.box1_0`, `OAI.SharpPlanar.Residual60.box1_0`, `OAI.SharpPlanar.Residual61.box1_0`, `OAI.SharpPlanar.Residual63.box1_0`, `OAI.SharpPlanar.Residual64.box1_0`, `OAI.SharpPlanar.Residual67.box1_0`, `OAI.SharpPlanar.Residual69.box1_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_Residual3`, `PlanarPacking_Certificate_Residual36`, `PlanarPacking_Certificate_Residual37`, `PlanarPacking_Certificate_Residual39`, `PlanarPacking_Certificate_Residual4`, `PlanarPacking_Certificate_Residual40`, `PlanarPacking_Certificate_Residual43`, `PlanarPacking_Certificate_Residual45`, `PlanarPacking_Certificate_Residual48`, `PlanarPacking_Certificate_Residual49`, `PlanarPacking_Certificate_Residual51`, `PlanarPacking_Certificate_Residual52`, `PlanarPacking_Certificate_Residual55`, `PlanarPacking_Certificate_Residual57`, `PlanarPacking_Certificate_Residual60`, `PlanarPacking_Certificate_Residual61`, `PlanarPacking_Certificate_Residual63`, `PlanarPacking_Certificate_Residual64`, `PlanarPacking_Certificate_Residual67`, `PlanarPacking_Certificate_Residual69`.
--
--   **Imports.** It imports the bundles `OAIQ098G099` and `OAIQ098G1513` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Residual36.bound1_0_g`, `OAI.SharpPlanar.Residual37.bound1_0_g`, `OAI.SharpPlanar.Residual40.bound1_0_g`, `OAI.SharpPlanar.Residual43.bound1_0_g`, `OAI.SharpPlanar.Residual45.bound1_0_g`, `OAI.SharpPlanar.Residual48.bound1_0_g`, `OAI.SharpPlanar.Residual49.bound1_0_g`, `OAI.SharpPlanar.Residual51.bound1_0_g`, `OAI.SharpPlanar.Residual52.bound1_0_g`, `OAI.SharpPlanar.Residual55.bound1_0_g`, `OAI.SharpPlanar.Residual57.bound1_0_g`, `OAI.SharpPlanar.Residual60.bound1_0_g`, `OAI.SharpPlanar.Residual61.bound1_0_g`, `OAI.SharpPlanar.Residual63.bound1_0_g`, `OAI.SharpPlanar.Residual64.bound1_0_g`, `OAI.SharpPlanar.Residual67.bound1_0_g`, `OAI.SharpPlanar.Residual69.bound1_0_g`, `OAI.SharpPlanar.residual_finite_central_1_g` and `OAI.SharpPlanar.residual_finite_exterior_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G099
import Definitions.Def_OAIQ098G1513

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual3
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

namespace SharpPlanar.Residual3
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-186215974) 10000000000).add ((tm0_3_0.realAnswer).mul (qiBox 3))
end SharpPlanar.Residual3

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual36
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

namespace SharpPlanar.Residual36
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-114876) 10000000000).add ((tm0_36_0.realAnswer).mul (qiBox 36))
end SharpPlanar.Residual36

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual37
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

namespace SharpPlanar.Residual37
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (166591) 10000000000).add ((tm0_37_0.realAnswer).mul (qiBox 37))
end SharpPlanar.Residual37

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual39
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

namespace SharpPlanar.Residual39
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (32128) 10000000000).add ((tm0_39_0.realAnswer).mul (qiBox 39))
end SharpPlanar.Residual39

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual4
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

namespace SharpPlanar.Residual4
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (82882809) 10000000000).add ((tm0_4_0.realAnswer).mul (qiBox 4))
end SharpPlanar.Residual4

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual40
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

namespace SharpPlanar.Residual40
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (10836) 10000000000).add ((tm0_40_0.realAnswer).mul (qiBox 40))
end SharpPlanar.Residual40

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual43
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

namespace SharpPlanar.Residual43
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-4050) 10000000000).add ((tm0_43_0.realAnswer).mul (qiBox 43))
end SharpPlanar.Residual43

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual45
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

namespace SharpPlanar.Residual45
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-1524) 10000000000).add ((tm0_45_0.realAnswer).mul (qiBox 45))
end SharpPlanar.Residual45

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual48
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

namespace SharpPlanar.Residual48
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-8611) 10000000000).add ((tm0_48_0.realAnswer).mul (qiBox 48))
end SharpPlanar.Residual48

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual49
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

namespace SharpPlanar.Residual49
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (17354) 10000000000).add ((tm0_49_0.realAnswer).mul (qiBox 49))
end SharpPlanar.Residual49

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual51
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

namespace SharpPlanar.Residual51
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (9641) 10000000000).add ((tm0_51_0.realAnswer).mul (qiBox 51))
end SharpPlanar.Residual51

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual52
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

namespace SharpPlanar.Residual52
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-2269) 10000000000).add ((tm0_52_0.realAnswer).mul (qiBox 52))
end SharpPlanar.Residual52

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual55
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

namespace SharpPlanar.Residual55
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-344) 10000000000).add ((tm0_55_0.realAnswer).mul (qiBox 55))
end SharpPlanar.Residual55

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual57
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

namespace SharpPlanar.Residual57
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-266) 10000000000).add ((tm0_57_0.realAnswer).mul (qiBox 57))
end SharpPlanar.Residual57

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual60
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

namespace SharpPlanar.Residual60
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-231) 10000000000).add ((tm0_60_0.realAnswer).mul (qiBox 60))
end SharpPlanar.Residual60

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual61
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

namespace SharpPlanar.Residual61
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (1140) 10000000000).add ((tm0_61_0.realAnswer).mul (qiBox 61))
end SharpPlanar.Residual61

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual63
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

namespace SharpPlanar.Residual63
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (1265) 10000000000).add ((tm0_63_0.realAnswer).mul (qiBox 63))
end SharpPlanar.Residual63

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual64
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

namespace SharpPlanar.Residual64
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-491) 10000000000).add ((tm0_64_0.realAnswer).mul (qiBox 64))
end SharpPlanar.Residual64

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual67
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

namespace SharpPlanar.Residual67
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-14) 10000000000).add ((tm0_67_0.realAnswer).mul (qiBox 67))
end SharpPlanar.Residual67

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual69
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

namespace SharpPlanar.Residual69
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box1_0 : RBox := (RBox.rat (-28) 10000000000).add ((tm0_69_0.realAnswer).mul (qiBox 69))
end SharpPlanar.Residual69

end OAI
end


