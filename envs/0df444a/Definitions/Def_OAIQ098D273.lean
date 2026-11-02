-- Prove2me | Definitions.Def_OAIQ098D273
-- name    : OAIQ098D273
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:41:34.176402+00:00
-- url     : https://prove2.me/theorems/e73d8e10-fbe4-49d1-b382-e69fe274cd26
-- title:
--   Definitions bundle OAIQ098D273 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 387 declarations of OpenAI's Lean: 101 definitions and 286 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.hm33_1_0_12.s0`, `OAI.SharpPlanar.CachedData.hm33_1_0_12.s1`, `OAI.SharpPlanar.CachedData.hm33_1_0_12.sums`, `OAI.SharpPlanar.CachedData.hm33_1_0_13.s0`, `OAI.SharpPlanar.CachedData.hm33_1_0_13.sums`, `OAI.SharpPlanar.CachedData.hm36_0_0_11.s0`, `OAI.SharpPlanar.CachedData.hm36_0_0_11.s1`, `OAI.SharpPlanar.CachedData.hm36_0_0_11.s2`, `OAI.SharpPlanar.CachedData.hm36_0_0_11.sums`, `OAI.SharpPlanar.CachedData.hm36_1_0_11.s0`, `OAI.SharpPlanar.CachedData.hm36_1_0_11.s1`, `OAI.SharpPlanar.CachedData.hm36_1_0_11.s2`, `OAI.SharpPlanar.CachedData.hm36_1_0_11.s3`, `OAI.SharpPlanar.CachedData.hm36_1_0_11.s4`, `OAI.SharpPlanar.CachedData.hm36_1_0_11.s5`, `OAI.SharpPlanar.CachedData.hm36_1_0_11.sums`, `OAI.SharpPlanar.CachedData.hm36_1_0_12.s0`, `OAI.SharpPlanar.CachedData.hm36_1_0_12.sums`, `OAI.SharpPlanar.CachedData.hm37_0_0_11.s0`, `OAI.SharpPlanar.CachedData.hm37_0_0_11.sums`, `OAI.SharpPlanar.CachedData.hm37_0_0_12.s0`, `OAI.SharpPlanar.CachedData.hm37_0_0_12.s1`, `OAI.SharpPlanar.CachedData.hm37_0_0_12.s2`, `OAI.SharpPlanar.CachedData.hm37_0_0_12.s3`, `OAI.SharpPlanar.CachedData.hm37_0_0_12.s4`, `OAI.SharpPlanar.CachedData.hm37_0_0_12.sums`, `OAI.SharpPlanar.CachedData.hm37_1_0_3.s0`, `OAI.SharpPlanar.CachedData.hm37_1_0_3.s1`, `OAI.SharpPlanar.CachedData.hm37_1_0_3.sums`, `OAI.SharpPlanar.CachedData.hm37_1_0_6.s0`, `OAI.SharpPlanar.CachedData.hm37_1_0_6.sums`, `OAI.SharpPlanar.CachedData.hm39_0_0_4.s0`, `OAI.SharpPlanar.CachedData.hm39_0_0_4.s1`, `OAI.SharpPlanar.CachedData.hm39_0_0_4.s2`, `OAI.SharpPlanar.CachedData.hm39_0_0_4.s3`, `OAI.SharpPlanar.CachedData.hm39_0_0_4.s4`, `OAI.SharpPlanar.CachedData.hm39_0_0_4.s5`, `OAI.SharpPlanar.CachedData.hm39_0_0_4.sums`, `OAI.SharpPlanar.CachedData.hm39_0_0_9.s0`, `OAI.SharpPlanar.CachedData.hm39_0_0_9.sums` and 61 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_HighMoments3_0`, `PlanarPacking_Certificate_LowBlock31_0`, `PlanarPacking_Certificate_LowBlock31_1`, `PlanarPacking_Certificate_LowBlock31_10`, `PlanarPacking_Certificate_LowBlock33_0`, `PlanarPacking_Certificate_LowBlock33_1`, `PlanarPacking_Certificate_LowBlock33_10`, `PlanarPacking_Certificate_LowBlock36_0`, `PlanarPacking_Certificate_LowBlock36_1`, `PlanarPacking_Certificate_LowBlock36_10`, `PlanarPacking_Certificate_LowBlock37_0`, `PlanarPacking_Certificate_LowBlock37_1`, `PlanarPacking_Certificate_LowBlock37_10`, `PlanarPacking_Certificate_LowBlock39_0`, `PlanarPacking_Certificate_LowBlock39_1`, `PlanarPacking_Certificate_LowBlock39_10`, `PlanarPacking_Certificate_LowBlock3_1`, `PlanarPacking_Certificate_LowBlock3_10`, `PlanarPacking_Certificate_LowBlock3_11`, `PlanarPacking_Certificate_LowBlock40_0`, `PlanarPacking_Certificate_LowBlock40_1`, `PlanarPacking_Certificate_LowBlock40_10`, `PlanarPacking_Certificate_LowBlock4_0`, `PlanarPacking_Certificate_LowBlock4_1`, `PlanarPacking_Certificate_LowBlock4_10`, `PlanarPacking_Certificate_LowBlock4_11`, `PlanarPacking_Certificate_LowBlock4_12`, `PlanarPacking_Certificate_LowBlock4_2`, `PlanarPacking_Certificate_TransformedPowers20`.
--
--   **Imports.** It imports the bundles `OAIQ098D041`, `OAIQ098D204`, `OAIQ098D205`, `OAIQ098D206`, `OAIQ098D207`, `OAIQ098D208`, `OAIQ098D209`, `OAIQ098D210`, `OAIQ098D211`, `OAIQ098D212`, `OAIQ098D213`, `OAIQ098D214`, `OAIQ098D215`, `OAIQ098D216`, `OAIQ098D217`, `OAIQ098D218`, `OAIQ098D219`, `OAIQ098D220`, `OAIQ098D221`, `OAIQ098D222`, `OAIQ098D231` and `OAIQ098D232` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D371` and `OAIQ098D427`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D204
import Definitions.Def_OAIQ098D205
import Definitions.Def_OAIQ098D206
import Definitions.Def_OAIQ098D207
import Definitions.Def_OAIQ098D208
import Definitions.Def_OAIQ098D209
import Definitions.Def_OAIQ098D210
import Definitions.Def_OAIQ098D211
import Definitions.Def_OAIQ098D212
import Definitions.Def_OAIQ098D213
import Definitions.Def_OAIQ098D214
import Definitions.Def_OAIQ098D215
import Definitions.Def_OAIQ098D216
import Definitions.Def_OAIQ098D217
import Definitions.Def_OAIQ098D218
import Definitions.Def_OAIQ098D219
import Definitions.Def_OAIQ098D220
import Definitions.Def_OAIQ098D221
import Definitions.Def_OAIQ098D222
import Definitions.Def_OAIQ098D231
import Definitions.Def_OAIQ098D232

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments3_0
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm3_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_2
namespace hm3_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_2
namespace hm3_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_3
namespace hm3_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_3
namespace hm3_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_4
namespace hm3_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_4
namespace hm3_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_5
namespace hm3_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_5
namespace hm3_0_0_6
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_6
namespace hm3_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_6
namespace hm3_0_0_7
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_7
namespace hm3_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers20
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def trans19_r0 : Fin 16 → Fin 16 → CBox := ![trans19_r0_0,trans19_r0_1,trans19_r0_2,trans19_r0_3,trans19_r0_4,trans19_r0_5,trans19_r0_6,trans19_r0_7,trans19_r0_8,trans19_r0_9,trans19_r0_10,trans19_r0_11,trans19_r0_12,trans19_r0_13,trans19_r0_14,trans19_r0_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock31_0
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm31_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_2
namespace hm31_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_3
namespace hm31_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_4
namespace hm31_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_5
namespace hm31_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_6
namespace hm31_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock31_1
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm31_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_8
namespace hm31_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_9
namespace hm31_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_9
namespace hm31_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_10
namespace hm31_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_11
namespace hm31_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_12
namespace hm31_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock31_10
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm31_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_1_2
namespace hm31_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_1_2
namespace hm31_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_1_3
namespace hm31_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_1_3
namespace hm31_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_1_4
namespace hm31_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_1_4
namespace hm31_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_1_5
namespace hm31_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_1_5
namespace hm31_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_1_6
namespace hm31_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_1_6
namespace hm31_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_1_7
namespace hm31_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock33_0
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm33_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_2
namespace hm33_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_2
namespace hm33_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_3
namespace hm33_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_3
namespace hm33_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_4
namespace hm33_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_4
namespace hm33_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_5
namespace hm33_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_5
namespace hm33_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_6
namespace hm33_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_6
namespace hm33_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_7
namespace hm33_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock33_1
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm33_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_8
namespace hm33_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_8
namespace hm33_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_9
namespace hm33_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_9
namespace hm33_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_10
namespace hm33_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_10
namespace hm33_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_11
namespace hm33_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_11
namespace hm33_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_12
namespace hm33_1_0_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_12
namespace hm33_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_0_13
namespace hm33_1_0_13
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock33_10
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm33_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_1_2
namespace hm33_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_1_2
namespace hm33_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_1_3
namespace hm33_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_1_3
namespace hm33_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_1_4
namespace hm33_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_1_4
namespace hm33_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_1_5
namespace hm33_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_1_5
namespace hm33_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_1_6
namespace hm33_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_1_6
namespace hm33_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_0_1_7
namespace hm33_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm33_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock36_0
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm36_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_2
namespace hm36_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_2
namespace hm36_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_3
namespace hm36_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_3
namespace hm36_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_4
namespace hm36_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_4
namespace hm36_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_5
namespace hm36_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_5
namespace hm36_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_6
namespace hm36_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_6
namespace hm36_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_7
namespace hm36_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock36_1
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm36_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_8
namespace hm36_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_8
namespace hm36_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_9
namespace hm36_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_9
namespace hm36_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_10
namespace hm36_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_10
namespace hm36_0_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_11
namespace hm36_1_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_11
namespace hm36_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_12
namespace hm36_1_0_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_12
namespace hm36_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_0_13
namespace hm36_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock36_10
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm36_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_1_2
namespace hm36_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_1_2
namespace hm36_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_1_3
namespace hm36_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_1_3
namespace hm36_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_1_4
namespace hm36_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_1_4
namespace hm36_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_0_1_5
namespace hm36_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm36_1_1_5
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock37_0
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm37_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_2
namespace hm37_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_2
namespace hm37_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_3
namespace hm37_1_0_3
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_3
namespace hm37_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_4
namespace hm37_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_4
namespace hm37_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_5
namespace hm37_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_5
namespace hm37_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_6
namespace hm37_1_0_6
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_6
namespace hm37_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_7
namespace hm37_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock37_1
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm37_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_8
namespace hm37_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_8
namespace hm37_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_9
namespace hm37_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_9
namespace hm37_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_10
namespace hm37_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_10
namespace hm37_0_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_11
namespace hm37_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_11
namespace hm37_0_0_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_0_12
namespace hm37_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock37_10
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm37_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_1_2
namespace hm37_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_1_2
namespace hm37_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_1_3
namespace hm37_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_1_3
namespace hm37_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_1_4
namespace hm37_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_1_4
namespace hm37_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_0_1_5
namespace hm37_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm37_1_1_5
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock39_0
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm39_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_2
namespace hm39_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_2
namespace hm39_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_3
namespace hm39_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_3
namespace hm39_0_0_4
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_4
namespace hm39_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_4
namespace hm39_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_5
namespace hm39_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_5
namespace hm39_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_6
namespace hm39_1_0_6
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_6
namespace hm39_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_7
namespace hm39_1_0_7
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock39_1
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm39_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_8
namespace hm39_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_8
namespace hm39_0_0_9
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_9
namespace hm39_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_9
namespace hm39_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_10
namespace hm39_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_10
namespace hm39_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_11
namespace hm39_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_11
namespace hm39_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_0_12
namespace hm39_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock39_10
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm39_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_1_2
namespace hm39_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_1_2
namespace hm39_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_1_3
namespace hm39_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_1_3
namespace hm39_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_1_4
namespace hm39_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_1_4
namespace hm39_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_0_1_5
namespace hm39_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm39_1_1_5
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock3_1
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm3_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_8
namespace hm3_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_8
namespace hm3_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_9
namespace hm3_1_0_9
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_9
namespace hm3_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_10
namespace hm3_1_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_10
namespace hm3_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_11
namespace hm3_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_11
namespace hm3_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_12
namespace hm3_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_12
namespace hm3_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_0_13
namespace hm3_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock3_10
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm3_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_2
namespace hm3_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_2
namespace hm3_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_3
namespace hm3_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_3
namespace hm3_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_4
namespace hm3_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_4
namespace hm3_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_5
namespace hm3_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_5
namespace hm3_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_6
namespace hm3_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_6
namespace hm3_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_7
namespace hm3_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock3_11
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm3_0_1_8
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_8
namespace hm3_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_8
namespace hm3_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_9
namespace hm3_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_9
namespace hm3_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_10
namespace hm3_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_10
namespace hm3_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_11
namespace hm3_1_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_11
namespace hm3_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_12
namespace hm3_1_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_12
namespace hm3_0_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_0_1_13
namespace hm3_1_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm3_1_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock40_0
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm40_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_2
namespace hm40_1_0_2
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_2
namespace hm40_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_3
namespace hm40_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_3
namespace hm40_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_4
namespace hm40_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_4
namespace hm40_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_5
namespace hm40_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_5
namespace hm40_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_6
namespace hm40_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_6
namespace hm40_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_7
namespace hm40_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock40_1
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm40_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_8
namespace hm40_1_0_8
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_8
namespace hm40_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_9
namespace hm40_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_9
namespace hm40_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_10
namespace hm40_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_10
namespace hm40_0_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_11
namespace hm40_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_11
namespace hm40_0_0_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_12
namespace hm40_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_12
namespace hm40_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_0_13
namespace hm40_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock40_10
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm40_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_1_2
namespace hm40_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_1_2
namespace hm40_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_0_1_3
namespace hm40_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm40_1_1_3
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_0
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_2
namespace hm4_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_2
namespace hm4_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_3
namespace hm4_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_3
namespace hm4_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_4
namespace hm4_1_0_4
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_4
namespace hm4_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_5
namespace hm4_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_5
namespace hm4_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_6
namespace hm4_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_6
namespace hm4_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_7
namespace hm4_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_1
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_8
namespace hm4_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_8
namespace hm4_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_9
namespace hm4_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_9
namespace hm4_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_10
namespace hm4_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_10
namespace hm4_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_11
namespace hm4_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_11
namespace hm4_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_12
namespace hm4_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_12
namespace hm4_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_13
namespace hm4_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_10
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_2
namespace hm4_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_3
namespace hm4_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_4
namespace hm4_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_5
namespace hm4_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_6
namespace hm4_0_1_7
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_11
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_8
namespace hm4_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_9
namespace hm4_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_10
namespace hm4_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_10
namespace hm4_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_11
namespace hm4_1_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_11
namespace hm4_0_1_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_12
namespace hm4_1_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_12
namespace hm4_0_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_12
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_0_1_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_14
namespace hm4_0_1_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_15
namespace hm4_0_1_16
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_16
namespace hm4_0_1_17
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_17
namespace hm4_1_1_17
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
end hm4_1_1_17
namespace hm4_0_1_18
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_18
namespace hm4_0_1_19
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_1_19
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_2
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_0_0_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_14
namespace hm4_1_0_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_14
namespace hm4_0_0_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_15
namespace hm4_1_0_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_15
namespace hm4_0_0_16
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_16
namespace hm4_1_0_16
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_16
namespace hm4_0_0_17
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_17
namespace hm4_1_0_17
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_17
namespace hm4_0_0_18
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_18
namespace hm4_1_0_18
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_18
namespace hm4_0_0_19
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_0_0_19
namespace hm4_1_0_19
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_0_19
end SharpPlanar.CachedData

end OAI
end


