-- Prove2me | Definitions.Def_OAIQ098G1666
-- name    : OAIQ098G1666
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:51:27.71121+00:00
-- url     : https://prove2.me/theorems/aa4c99e4-c19a-4c0a-ac0f-b4302b284065
-- title:
--   Definitions bundle OAIQ098G1666 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 20 definitions. The definitions and types are `OAI.SharpPlanar.Residual4.box0_1`, `OAI.SharpPlanar.Residual49.box0_1`, `OAI.SharpPlanar.Residual51.box0_1`, `OAI.SharpPlanar.Residual52.box0_1`, `OAI.SharpPlanar.Residual55.box0_1`, `OAI.SharpPlanar.Residual57.box0_1`, `OAI.SharpPlanar.Residual60.box0_1`, `OAI.SharpPlanar.Residual61.box0_1`, `OAI.SharpPlanar.Residual63.box0_1`, `OAI.SharpPlanar.Residual64.box0_1`, `OAI.SharpPlanar.Residual67.box0_1`, `OAI.SharpPlanar.Residual69.box0_1`, `OAI.SharpPlanar.Residual7.box0_1`, `OAI.SharpPlanar.Residual72.box0_1`, `OAI.SharpPlanar.Residual73.box0_1`, `OAI.SharpPlanar.Residual75.box0_1`, `OAI.SharpPlanar.Residual76.box0_1`, `OAI.SharpPlanar.Residual79.box0_1`, `OAI.SharpPlanar.Residual81.box0_1`, `OAI.SharpPlanar.Residual84.box0_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_Residual4`, `PlanarPacking_Certificate_Residual49`, `PlanarPacking_Certificate_Residual51`, `PlanarPacking_Certificate_Residual52`, `PlanarPacking_Certificate_Residual55`, `PlanarPacking_Certificate_Residual57`, `PlanarPacking_Certificate_Residual60`, `PlanarPacking_Certificate_Residual61`, `PlanarPacking_Certificate_Residual63`, `PlanarPacking_Certificate_Residual64`, `PlanarPacking_Certificate_Residual67`, `PlanarPacking_Certificate_Residual69`, `PlanarPacking_Certificate_Residual7`, `PlanarPacking_Certificate_Residual72`, `PlanarPacking_Certificate_Residual73`, `PlanarPacking_Certificate_Residual75`, `PlanarPacking_Certificate_Residual76`, `PlanarPacking_Certificate_Residual79`, `PlanarPacking_Certificate_Residual81`, `PlanarPacking_Certificate_Residual84`.
--
--   **Imports.** It imports the bundles `OAIQ098G100` and `OAIQ098G1570` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Residual49.bound0_1_g`, `OAI.SharpPlanar.Residual51.bound0_1_g`, `OAI.SharpPlanar.Residual52.bound0_1_g`, `OAI.SharpPlanar.Residual55.bound0_1_g`, `OAI.SharpPlanar.Residual57.bound0_1_g`, `OAI.SharpPlanar.Residual60.bound0_1_g`, `OAI.SharpPlanar.Residual61.bound0_1_g`, `OAI.SharpPlanar.Residual63.bound0_1_g`, `OAI.SharpPlanar.Residual64.bound0_1_g`, `OAI.SharpPlanar.Residual67.bound0_1_g`, `OAI.SharpPlanar.Residual69.bound0_1_g`, `OAI.SharpPlanar.Residual72.bound0_1_g`, `OAI.SharpPlanar.Residual73.bound0_1_g`, `OAI.SharpPlanar.Residual75.bound0_1_g`, `OAI.SharpPlanar.Residual76.bound0_1_g`, `OAI.SharpPlanar.Residual79.bound0_1_g`, `OAI.SharpPlanar.Residual7.bound0_1_g`, `OAI.SharpPlanar.Residual81.bound0_1_g`, `OAI.SharpPlanar.Residual84.bound0_1_g` and `OAI.SharpPlanar.residual_finite_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G100
import Definitions.Def_OAIQ098G1570

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
noncomputable def box0_1 : RBox := (RBox.rat (121133118) 10000000000).add ((tm1_4_1.realAnswer.add (((dBox 4).mul tm1_4_0.realAnswer).neg)).mul (qiBox 4))
end SharpPlanar.Residual4

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
noncomputable def box0_1 : RBox := (RBox.rat (7495) 10000000000).add ((tm1_49_1.realAnswer.add (((dBox 49).mul tm1_49_0.realAnswer).neg)).mul (qiBox 49))
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
noncomputable def box0_1 : RBox := (RBox.rat (29035) 10000000000).add ((tm1_51_1.realAnswer.add (((dBox 51).mul tm1_51_0.realAnswer).neg)).mul (qiBox 51))
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
noncomputable def box0_1 : RBox := (RBox.rat (-26523) 10000000000).add ((tm1_52_1.realAnswer.add (((dBox 52).mul tm1_52_0.realAnswer).neg)).mul (qiBox 52))
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
noncomputable def box0_1 : RBox := (RBox.rat (858) 10000000000).add ((tm1_55_1.realAnswer.add (((dBox 55).mul tm1_55_0.realAnswer).neg)).mul (qiBox 55))
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
noncomputable def box0_1 : RBox := (RBox.rat (-632) 10000000000).add ((tm1_57_1.realAnswer.add (((dBox 57).mul tm1_57_0.realAnswer).neg)).mul (qiBox 57))
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
noncomputable def box0_1 : RBox := (RBox.rat (5658) 10000000000).add ((tm1_60_1.realAnswer.add (((dBox 60).mul tm1_60_0.realAnswer).neg)).mul (qiBox 60))
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
noncomputable def box0_1 : RBox := (RBox.rat (-4320) 10000000000).add ((tm1_61_1.realAnswer.add (((dBox 61).mul tm1_61_0.realAnswer).neg)).mul (qiBox 61))
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
noncomputable def box0_1 : RBox := (RBox.rat (-352) 10000000000).add ((tm1_63_1.realAnswer.add (((dBox 63).mul tm1_63_0.realAnswer).neg)).mul (qiBox 63))
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
noncomputable def box0_1 : RBox := (RBox.rat (-2609) 10000000000).add ((tm1_64_1.realAnswer.add (((dBox 64).mul tm1_64_0.realAnswer).neg)).mul (qiBox 64))
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
noncomputable def box0_1 : RBox := (RBox.rat (169) 10000000000).add ((tm1_67_1.realAnswer.add (((dBox 67).mul tm1_67_0.realAnswer).neg)).mul (qiBox 67))
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
noncomputable def box0_1 : RBox := (RBox.rat (13) 10000000000).add ((tm1_69_1.realAnswer.add (((dBox 69).mul tm1_69_0.realAnswer).neg)).mul (qiBox 69))
end SharpPlanar.Residual69

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
noncomputable def box0_1 : RBox := (RBox.rat (-16329465) 10000000000).add ((tm1_7_1.realAnswer.add (((dBox 7).mul tm1_7_0.realAnswer).neg)).mul (qiBox 7))
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
noncomputable def box0_1 : RBox := (RBox.rat (394) 10000000000).add ((tm1_72_1.realAnswer.add (((dBox 72).mul tm1_72_0.realAnswer).neg)).mul (qiBox 72))
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
noncomputable def box0_1 : RBox := (RBox.rat (-805) 10000000000).add ((tm1_73_1.realAnswer.add (((dBox 73).mul tm1_73_0.realAnswer).neg)).mul (qiBox 73))
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
noncomputable def box0_1 : RBox := (RBox.rat (-379) 10000000000).add ((tm1_75_1.realAnswer.add (((dBox 75).mul tm1_75_0.realAnswer).neg)).mul (qiBox 75))
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
noncomputable def box0_1 : RBox := (RBox.rat (-144) 10000000000).add ((tm1_76_1.realAnswer.add (((dBox 76).mul tm1_76_0.realAnswer).neg)).mul (qiBox 76))
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
noncomputable def box0_1 : RBox := (RBox.rat (19) 10000000000).add ((tm1_79_1.realAnswer.add (((dBox 79).mul tm1_79_0.realAnswer).neg)).mul (qiBox 79))
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
noncomputable def box0_1 : RBox := (RBox.rat (9) 10000000000).add ((tm1_81_1.realAnswer.add (((dBox 81).mul tm1_81_0.realAnswer).neg)).mul (qiBox 81))
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
noncomputable def box0_1 : RBox := (RBox.rat (3) 10000000000).add ((tm1_84_1.realAnswer.add (((dBox 84).mul tm1_84_0.realAnswer).neg)).mul (qiBox 84))
end SharpPlanar.Residual84

end OAI
end


