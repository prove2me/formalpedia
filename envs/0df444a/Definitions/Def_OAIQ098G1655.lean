-- Prove2me | Definitions.Def_OAIQ098G1655
-- name    : OAIQ098G1655
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:49:03.132601+00:00
-- url     : https://prove2.me/theorems/8bc43965-a038-40e1-834f-146053f9f0e9
-- title:
--   Definitions bundle OAIQ098G1655 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 18 definitions. The definitions and types are `OAI.SharpPlanar.Residual1.box0_1`, `OAI.SharpPlanar.Residual16.box0_1`, `OAI.SharpPlanar.Residual19.box0_1`, `OAI.SharpPlanar.Residual21.box0_1`, `OAI.SharpPlanar.Residual24.box0_1`, `OAI.SharpPlanar.Residual25.box0_1`, `OAI.SharpPlanar.Residual27.box0_1`, `OAI.SharpPlanar.Residual28.box0_1`, `OAI.SharpPlanar.Residual3.box0_1`, `OAI.SharpPlanar.Residual31.box0_1`, `OAI.SharpPlanar.Residual33.box0_1`, `OAI.SharpPlanar.Residual36.box0_1`, `OAI.SharpPlanar.Residual37.box0_1`, `OAI.SharpPlanar.Residual39.box0_1`, `OAI.SharpPlanar.Residual40.box0_1`, `OAI.SharpPlanar.Residual43.box0_1`, `OAI.SharpPlanar.Residual45.box0_1`, `OAI.SharpPlanar.Residual48.box0_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_Residual1`, `PlanarPacking_Certificate_Residual16`, `PlanarPacking_Certificate_Residual19`, `PlanarPacking_Certificate_Residual21`, `PlanarPacking_Certificate_Residual24`, `PlanarPacking_Certificate_Residual25`, `PlanarPacking_Certificate_Residual27`, `PlanarPacking_Certificate_Residual28`, `PlanarPacking_Certificate_Residual3`, `PlanarPacking_Certificate_Residual31`, `PlanarPacking_Certificate_Residual33`, `PlanarPacking_Certificate_Residual36`, `PlanarPacking_Certificate_Residual37`, `PlanarPacking_Certificate_Residual39`, `PlanarPacking_Certificate_Residual40`, `PlanarPacking_Certificate_Residual43`, `PlanarPacking_Certificate_Residual45`, `PlanarPacking_Certificate_Residual48`.
--
--   **Imports.** It imports the bundles `OAIQ098G100` and `OAIQ098G1552` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Residual16.bound0_1_g`, `OAI.SharpPlanar.Residual19.bound0_1_g`, `OAI.SharpPlanar.Residual21.bound0_1_g`, `OAI.SharpPlanar.Residual24.bound0_1_g`, `OAI.SharpPlanar.Residual25.bound0_1_g`, `OAI.SharpPlanar.Residual27.bound0_1_g`, `OAI.SharpPlanar.Residual28.bound0_1_g`, `OAI.SharpPlanar.Residual31.bound0_1_g`, `OAI.SharpPlanar.Residual33.bound0_1_g`, `OAI.SharpPlanar.Residual36.bound0_1_g`, `OAI.SharpPlanar.Residual37.bound0_1_g`, `OAI.SharpPlanar.Residual39.bound0_1_g`, `OAI.SharpPlanar.Residual40.bound0_1_g`, `OAI.SharpPlanar.Residual43.bound0_1_g`, `OAI.SharpPlanar.Residual45.bound0_1_g`, `OAI.SharpPlanar.Residual48.bound0_1_g` and `OAI.SharpPlanar.residual_finite_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G100
import Definitions.Def_OAIQ098G1552

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
noncomputable def box0_1 : RBox := (RBox.rat (3601371201) 10000000000).add ((tm1_1_1.realAnswer.add (((dBox 1).mul tm1_1_0.realAnswer).neg)).mul (qiBox 1))
end SharpPlanar.Residual1

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
noncomputable def box0_1 : RBox := (RBox.rat (13405071) 10000000000).add ((tm1_16_1.realAnswer.add (((dBox 16).mul tm1_16_0.realAnswer).neg)).mul (qiBox 16))
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
noncomputable def box0_1 : RBox := (RBox.rat (-1515007) 10000000000).add ((tm1_19_1.realAnswer.add (((dBox 19).mul tm1_19_0.realAnswer).neg)).mul (qiBox 19))
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
noncomputable def box0_1 : RBox := (RBox.rat (-634307) 10000000000).add ((tm1_21_1.realAnswer.add (((dBox 21).mul tm1_21_0.realAnswer).neg)).mul (qiBox 21))
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
noncomputable def box0_1 : RBox := (RBox.rat (-804949) 10000000000).add ((tm1_24_1.realAnswer.add (((dBox 24).mul tm1_24_0.realAnswer).neg)).mul (qiBox 24))
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
noncomputable def box0_1 : RBox := (RBox.rat (7003719) 10000000000).add ((tm1_25_1.realAnswer.add (((dBox 25).mul tm1_25_0.realAnswer).neg)).mul (qiBox 25))
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
noncomputable def box0_1 : RBox := (RBox.rat (4536095) 10000000000).add ((tm1_27_1.realAnswer.add (((dBox 27).mul tm1_27_0.realAnswer).neg)).mul (qiBox 27))
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
noncomputable def box0_1 : RBox := (RBox.rat (-107613) 10000000000).add ((tm1_28_1.realAnswer.add (((dBox 28).mul tm1_28_0.realAnswer).neg)).mul (qiBox 28))
end SharpPlanar.Residual28

end OAI
end

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
noncomputable def box0_1 : RBox := (RBox.rat (564897270) 10000000000).add ((tm1_3_1.realAnswer.add (((dBox 3).mul tm1_3_0.realAnswer).neg)).mul (qiBox 3))
end SharpPlanar.Residual3

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
noncomputable def box0_1 : RBox := (RBox.rat (-112653) 10000000000).add ((tm1_31_1.realAnswer.add (((dBox 31).mul tm1_31_0.realAnswer).neg)).mul (qiBox 31))
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
noncomputable def box0_1 : RBox := (RBox.rat (-105568) 10000000000).add ((tm1_33_1.realAnswer.add (((dBox 33).mul tm1_33_0.realAnswer).neg)).mul (qiBox 33))
end SharpPlanar.Residual33

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
noncomputable def box0_1 : RBox := (RBox.rat (246018) 10000000000).add ((tm1_36_1.realAnswer.add (((dBox 36).mul tm1_36_0.realAnswer).neg)).mul (qiBox 36))
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
noncomputable def box0_1 : RBox := (RBox.rat (505187) 10000000000).add ((tm1_37_1.realAnswer.add (((dBox 37).mul tm1_37_0.realAnswer).neg)).mul (qiBox 37))
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
noncomputable def box0_1 : RBox := (RBox.rat (472037) 10000000000).add ((tm1_39_1.realAnswer.add (((dBox 39).mul tm1_39_0.realAnswer).neg)).mul (qiBox 39))
end SharpPlanar.Residual39

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
noncomputable def box0_1 : RBox := (RBox.rat (-165597) 10000000000).add ((tm1_40_1.realAnswer.add (((dBox 40).mul tm1_40_0.realAnswer).neg)).mul (qiBox 40))
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
noncomputable def box0_1 : RBox := (RBox.rat (-2296) 10000000000).add ((tm1_43_1.realAnswer.add (((dBox 43).mul tm1_43_0.realAnswer).neg)).mul (qiBox 43))
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
noncomputable def box0_1 : RBox := (RBox.rat (-10734) 10000000000).add ((tm1_45_1.realAnswer.add (((dBox 45).mul tm1_45_0.realAnswer).neg)).mul (qiBox 45))
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
noncomputable def box0_1 : RBox := (RBox.rat (50050) 10000000000).add ((tm1_48_1.realAnswer.add (((dBox 48).mul tm1_48_0.realAnswer).neg)).mul (qiBox 48))
end SharpPlanar.Residual48

end OAI
end


