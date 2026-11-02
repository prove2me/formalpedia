-- Prove2me | Definitions.Def_OAIQ098D271
-- name    : OAIQ098D271
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:37:58.440643+00:00
-- url     : https://prove2.me/theorems/1522f48d-10ba-43c8-a4f5-678a5ab40ef0
-- title:
--   Definitions bundle OAIQ098D271 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 274 declarations of OpenAI's Lean: 73 definitions and 201 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.hm16_1_0_3.s2`, `OAI.SharpPlanar.CachedData.hm16_1_1_6.s0`, `OAI.SharpPlanar.CachedData.hm16_1_1_6.s1`, `OAI.SharpPlanar.CachedData.hm16_1_1_6.s2`, `OAI.SharpPlanar.CachedData.hm16_1_1_6.s3`, `OAI.SharpPlanar.CachedData.hm16_1_1_6.sums`, `OAI.SharpPlanar.CachedData.hm16_1_1_7.s0`, `OAI.SharpPlanar.CachedData.hm16_1_1_7.sums`, `OAI.SharpPlanar.CachedData.hm19_0_0_7.s1`, `OAI.SharpPlanar.CachedData.hm19_0_0_7.s2`, `OAI.SharpPlanar.CachedData.hm19_0_0_7.sums`, `OAI.SharpPlanar.CachedData.hm19_0_1_8.s3`, `OAI.SharpPlanar.CachedData.hm19_0_1_8.s4`, `OAI.SharpPlanar.CachedData.hm19_0_1_8.s5`, `OAI.SharpPlanar.CachedData.hm19_0_1_8.sums`, `OAI.SharpPlanar.CachedData.hm19_1_0_9.s0`, `OAI.SharpPlanar.CachedData.hm19_1_0_9.sums`, `OAI.SharpPlanar.CachedData.hm1_0_0_1.s0`, `OAI.SharpPlanar.CachedData.hm1_0_0_1.s1`, `OAI.SharpPlanar.CachedData.hm1_0_0_1.s2`, `OAI.SharpPlanar.CachedData.hm1_0_0_1.s3`, `OAI.SharpPlanar.CachedData.hm1_0_0_1.s4`, `OAI.SharpPlanar.CachedData.hm1_0_0_1.s5`, `OAI.SharpPlanar.CachedData.hm1_0_0_1.sums`, `OAI.SharpPlanar.CachedData.hm1_0_0_10.s0`, `OAI.SharpPlanar.CachedData.hm1_0_0_10.sums`, `OAI.SharpPlanar.CachedData.hm1_0_0_18.s0`, `OAI.SharpPlanar.CachedData.hm1_0_0_18.sums`, `OAI.SharpPlanar.CachedData.hm1_0_0_27.s4`, `OAI.SharpPlanar.CachedData.hm1_0_0_27.s5`, `OAI.SharpPlanar.CachedData.hm1_0_0_27.sums`, `OAI.SharpPlanar.CachedData.hm1_0_0_9.s0`, `OAI.SharpPlanar.CachedData.hm1_0_0_9.s1`, `OAI.SharpPlanar.CachedData.hm1_0_0_9.s2`, `OAI.SharpPlanar.CachedData.hm1_0_0_9.s3`, `OAI.SharpPlanar.CachedData.hm1_0_0_9.s4`, `OAI.SharpPlanar.CachedData.hm1_0_0_9.s5`, `OAI.SharpPlanar.CachedData.hm1_0_0_9.sums`, `OAI.SharpPlanar.CachedData.hm1_0_1_10.s0`, `OAI.SharpPlanar.CachedData.hm1_0_1_10.sums` and 33 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_HighMoments1_0`, `PlanarPacking_Certificate_HighMoments1_1`, `PlanarPacking_Certificate_HighMoments1_2`, `PlanarPacking_Certificate_HighMoments1_3`, `PlanarPacking_Certificate_HighMoments1_4`, `PlanarPacking_Certificate_HighMoments1_5`, `PlanarPacking_Certificate_HighMoments1_6`, `PlanarPacking_Certificate_HighMoments1_7`, `PlanarPacking_Certificate_LowBlock16_0`, `PlanarPacking_Certificate_LowBlock16_1`, `PlanarPacking_Certificate_LowBlock16_10`, `PlanarPacking_Certificate_LowBlock16_11`, `PlanarPacking_Certificate_LowBlock19_0`, `PlanarPacking_Certificate_LowBlock19_1`, `PlanarPacking_Certificate_LowBlock19_10`, `PlanarPacking_Certificate_LowBlock19_11`.
--
--   **Imports.** It imports the bundles `OAIQ098D041`, `OAIQ098D170`, `OAIQ098D171`, `OAIQ098D172`, `OAIQ098D173`, `OAIQ098D174`, `OAIQ098D175`, `OAIQ098D176`, `OAIQ098D177`, `OAIQ098D178`, `OAIQ098D179`, `OAIQ098D180`, `OAIQ098D181`, `OAIQ098D182`, `OAIQ098D183`, `OAIQ098D184`, `OAIQ098D185`, `OAIQ098D186`, `OAIQ098D187` and `OAIQ098D188` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D365` and `OAIQ098D387`; the proofs of `OAI.SharpPlanar.Bernstein19.N0_left.t0_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t8_contains`, `OAI.SharpPlanar.Bernstein19.N0_left.t9_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t0_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t8_contains`, `OAI.SharpPlanar.Bernstein19.N0_right.t9_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t0_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t8_contains`, `OAI.SharpPlanar.Bernstein19.N1_left.t9_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t0_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein19.N1_right.t8_contains` and `OAI.SharpPlanar.Bernstein19.N1_right.t9_contains`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D170
import Definitions.Def_OAIQ098D171
import Definitions.Def_OAIQ098D172
import Definitions.Def_OAIQ098D173
import Definitions.Def_OAIQ098D174
import Definitions.Def_OAIQ098D175
import Definitions.Def_OAIQ098D176
import Definitions.Def_OAIQ098D177
import Definitions.Def_OAIQ098D178
import Definitions.Def_OAIQ098D179
import Definitions.Def_OAIQ098D180
import Definitions.Def_OAIQ098D181
import Definitions.Def_OAIQ098D182
import Definitions.Def_OAIQ098D183
import Definitions.Def_OAIQ098D184
import Definitions.Def_OAIQ098D185
import Definitions.Def_OAIQ098D186
import Definitions.Def_OAIQ098D187
import Definitions.Def_OAIQ098D188

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_0
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
namespace hm1_0_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_1
namespace hm1_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_2
namespace hm1_1_0_2
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_2
namespace hm1_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_3
namespace hm1_1_0_3
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_3
namespace hm1_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_4
namespace hm1_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_4
namespace hm1_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_5
namespace hm1_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_5
namespace hm1_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_6
namespace hm1_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_6
namespace hm1_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_7
namespace hm1_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_1
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
namespace hm1_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_8
namespace hm1_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_8
namespace hm1_0_0_9
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_9
namespace hm1_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_9
namespace hm1_0_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_10
namespace hm1_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_10
namespace hm1_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_11
namespace hm1_1_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_11
namespace hm1_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_12
namespace hm1_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_12
namespace hm1_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_13
namespace hm1_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_13
namespace hm1_0_0_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_14
namespace hm1_1_0_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_14
namespace hm1_0_0_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_15
namespace hm1_1_0_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_2
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
namespace hm1_0_0_16
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_16
namespace hm1_1_0_16
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_16
namespace hm1_0_0_17
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_17
namespace hm1_1_0_17
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_17
namespace hm1_0_0_18
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_18
namespace hm1_1_0_18
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_18
namespace hm1_0_0_19
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_19
namespace hm1_1_0_19
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_19
namespace hm1_0_0_20
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_20
namespace hm1_1_0_20
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_20
namespace hm1_0_0_21
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_21
namespace hm1_1_0_21
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_21
namespace hm1_0_0_22
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_22
namespace hm1_1_0_22
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_22
namespace hm1_0_0_23
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_23
namespace hm1_1_0_23
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_23
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_3
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
namespace hm1_0_0_24
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_24
namespace hm1_1_0_24
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_24
namespace hm1_0_0_25
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_25
namespace hm1_1_0_25
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_25
namespace hm1_0_0_26
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_26
namespace hm1_1_0_26
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_26
namespace hm1_0_0_27
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_27
namespace hm1_1_0_27
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_27
namespace hm1_0_0_28
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_28
namespace hm1_1_0_28
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_28
namespace hm1_0_0_29
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_0_29
namespace hm1_1_0_29
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_29
namespace hm1_1_0_30
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_0_30
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_4
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
namespace hm1_1_1_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_1
namespace hm1_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_2
namespace hm1_1_1_2
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_2
namespace hm1_0_1_3
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_3
namespace hm1_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_4
namespace hm1_1_1_4
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
end hm1_1_1_4
namespace hm1_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_5
namespace hm1_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_6
namespace hm1_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_5
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
namespace hm1_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_8
namespace hm1_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_9
namespace hm1_0_1_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_10
namespace hm1_1_1_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_10
namespace hm1_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_11
namespace hm1_1_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_11
namespace hm1_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_12
namespace hm1_1_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_12
namespace hm1_0_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_13
namespace hm1_1_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_13
namespace hm1_0_1_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_14
namespace hm1_1_1_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_14
namespace hm1_0_1_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_15
namespace hm1_1_1_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_6
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
namespace hm1_0_1_16
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_16
namespace hm1_1_1_16
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_16
namespace hm1_0_1_17
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_17
namespace hm1_1_1_17
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_17
namespace hm1_0_1_18
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_18
namespace hm1_1_1_18
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_18
namespace hm1_0_1_19
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_19
namespace hm1_1_1_19
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_19
namespace hm1_0_1_20
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_20
namespace hm1_1_1_20
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_20
namespace hm1_0_1_21
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_21
namespace hm1_1_1_21
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_21
namespace hm1_0_1_22
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_22
namespace hm1_1_1_22
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_22
namespace hm1_0_1_23
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_23
namespace hm1_1_1_23
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_23
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_7
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
namespace hm1_0_1_24
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_24
namespace hm1_1_1_24
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_24
namespace hm1_0_1_25
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_25
namespace hm1_1_1_25
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_25
namespace hm1_0_1_26
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_26
namespace hm1_1_1_26
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_26
namespace hm1_0_1_27
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_27
namespace hm1_1_1_27
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_27
namespace hm1_0_1_28
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_28
namespace hm1_0_1_29
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_29
namespace hm1_0_1_30
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_0_1_30
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_0
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
namespace hm16_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_2
namespace hm16_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_2
namespace hm16_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_3
namespace hm16_1_0_3
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_3
namespace hm16_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_4
namespace hm16_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_4
namespace hm16_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_5
namespace hm16_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_5
namespace hm16_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_6
namespace hm16_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_6
namespace hm16_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_7
namespace hm16_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_1
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
namespace hm16_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_8
namespace hm16_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_8
namespace hm16_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_9
namespace hm16_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_9
namespace hm16_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_10
namespace hm16_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_11
namespace hm16_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_12
namespace hm16_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_12
namespace hm16_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_13
namespace hm16_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_10
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
namespace hm16_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_2
namespace hm16_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_2
namespace hm16_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_3
namespace hm16_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_3
namespace hm16_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_4
namespace hm16_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_4
namespace hm16_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_5
namespace hm16_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_5
namespace hm16_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_6
namespace hm16_1_1_6
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_6
namespace hm16_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_7
namespace hm16_1_1_7
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_11
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
namespace hm16_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_8
namespace hm16_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_8
namespace hm16_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_9
namespace hm16_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_9
namespace hm16_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_10
namespace hm16_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_10
namespace hm16_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_11
namespace hm16_1_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_11
namespace hm16_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_12
namespace hm16_1_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_12
namespace hm16_0_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_1_13
namespace hm16_1_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_1_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock19_0
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
namespace hm19_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_2
namespace hm19_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_2
namespace hm19_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_3
namespace hm19_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_3
namespace hm19_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_4
namespace hm19_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_4
namespace hm19_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_5
namespace hm19_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_5
namespace hm19_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_6
namespace hm19_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_6
namespace hm19_0_0_7
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_7
namespace hm19_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock19_1
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
namespace hm19_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_8
namespace hm19_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_8
namespace hm19_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_9
namespace hm19_1_0_9
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_9
namespace hm19_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_10
namespace hm19_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_10
namespace hm19_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_11
namespace hm19_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_11
namespace hm19_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_12
namespace hm19_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_12
namespace hm19_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_0_13
namespace hm19_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock19_10
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
namespace hm19_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_2
namespace hm19_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_2
namespace hm19_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_3
namespace hm19_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_3
namespace hm19_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_4
namespace hm19_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_4
namespace hm19_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_5
namespace hm19_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_5
namespace hm19_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_6
namespace hm19_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_6
namespace hm19_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_7
namespace hm19_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock19_11
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
namespace hm19_0_1_8
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_8
namespace hm19_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_8
namespace hm19_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_9
namespace hm19_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_9
namespace hm19_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_10
namespace hm19_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_10
namespace hm19_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_11
namespace hm19_1_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_11
namespace hm19_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_12
namespace hm19_1_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_12
namespace hm19_0_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_0_1_13
namespace hm19_1_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm19_1_1_13
end SharpPlanar.CachedData

end OAI
end


