-- Prove2me | Definitions.Def_OAIQ098G1669
-- name    : OAIQ098G1669
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:50:20.85499+00:00
-- url     : https://prove2.me/theorems/048341c9-116c-4f5c-b14b-1e237c52e465
-- title:
--   Definitions bundle OAIQ098G1669 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.SharpPlanar.Residual87.box0_1`, `OAI.SharpPlanar.Residual88.box0_1`, `OAI.SharpPlanar.Residual9.box0_1`, `OAI.SharpPlanar.Residual91.box0_1`, `OAI.SharpPlanar.Residual93.box0_1`, `OAI.SharpPlanar.Residual96.box0_1`, `OAI.SharpPlanar.Residual97.box0_1`, `OAI.SharpPlanar.Residual99.box0_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Residual87`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual87.lean), [`PlanarPacking_Certificate_Residual88`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual88.lean), [`PlanarPacking_Certificate_Residual9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual9.lean), [`PlanarPacking_Certificate_Residual91`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual91.lean), [`PlanarPacking_Certificate_Residual93`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual93.lean), [`PlanarPacking_Certificate_Residual96`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual96.lean), [`PlanarPacking_Certificate_Residual97`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual97.lean), [`PlanarPacking_Certificate_Residual99`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual99.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G100` and `OAIQ098G1588` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Residual87.bound0_1_g`, `OAI.SharpPlanar.Residual88.bound0_1_g`, `OAI.SharpPlanar.Residual91.bound0_1_g`, `OAI.SharpPlanar.Residual93.bound0_1_g`, `OAI.SharpPlanar.Residual96.bound0_1_g`, `OAI.SharpPlanar.Residual97.bound0_1_g`, `OAI.SharpPlanar.Residual99.bound0_1_g` and `OAI.SharpPlanar.Residual9.bound0_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G100
import Definitions.Def_OAIQ098G1588

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
noncomputable def box0_1 : RBox := (RBox.rat (-60) 10000000000).add ((tm1_87_1.realAnswer.add (((dBox 87).mul tm1_87_0.realAnswer).neg)).mul (qiBox 87))
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
noncomputable def box0_1 : RBox := (RBox.rat (5) 10000000000).add ((tm1_88_1.realAnswer.add (((dBox 88).mul tm1_88_0.realAnswer).neg)).mul (qiBox 88))
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
noncomputable def box0_1 : RBox := (RBox.rat (-940875) 10000000000).add ((tm1_9_1.realAnswer.add (((dBox 9).mul tm1_9_0.realAnswer).neg)).mul (qiBox 9))
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
noncomputable def box0_1 : RBox := (RBox.rat (1) 10000000000).add ((tm1_91_1.realAnswer.add (((dBox 91).mul tm1_91_0.realAnswer).neg)).mul (qiBox 91))
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
noncomputable def box0_1 : RBox := (RBox.rat (1) 10000000000).add ((tm1_93_1.realAnswer.add (((dBox 93).mul tm1_93_0.realAnswer).neg)).mul (qiBox 93))
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
noncomputable def box0_1 : RBox := (RBox.rat (-4) 10000000000).add ((tm1_96_1.realAnswer.add (((dBox 96).mul tm1_96_0.realAnswer).neg)).mul (qiBox 96))
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
noncomputable def box0_1 : RBox := (RBox.rat (-6) 10000000000).add ((tm1_97_1.realAnswer.add (((dBox 97).mul tm1_97_0.realAnswer).neg)).mul (qiBox 97))
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
noncomputable def box0_1 : RBox := (RBox.rat (-6) 10000000000).add ((tm1_99_1.realAnswer.add (((dBox 99).mul tm1_99_0.realAnswer).neg)).mul (qiBox 99))
end SharpPlanar.Residual99

end OAI
end


