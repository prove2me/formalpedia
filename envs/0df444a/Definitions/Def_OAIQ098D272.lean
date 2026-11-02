-- Prove2me | Definitions.Def_OAIQ098D272
-- name    : OAIQ098D272
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:41:42.591611+00:00
-- url     : https://prove2.me/theorems/1e9dacf0-d2e1-477d-a393-057267e29af5
-- title:
--   Definitions bundle OAIQ098D272 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 341 declarations of OpenAI's Lean: 117 definitions and 224 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.hm21_0_0_10.s0`, `OAI.SharpPlanar.CachedData.hm21_0_0_10.sums`, `OAI.SharpPlanar.CachedData.hm21_0_0_11.s0`, `OAI.SharpPlanar.CachedData.hm21_0_0_11.sums`, `OAI.SharpPlanar.CachedData.hm21_0_0_2.s1`, `OAI.SharpPlanar.CachedData.hm21_0_0_2.sums`, `OAI.SharpPlanar.CachedData.hm21_0_1_4.s1`, `OAI.SharpPlanar.CachedData.hm21_0_1_4.s2`, `OAI.SharpPlanar.CachedData.hm21_0_1_4.s3`, `OAI.SharpPlanar.CachedData.hm21_0_1_4.s4`, `OAI.SharpPlanar.CachedData.hm21_0_1_4.s5`, `OAI.SharpPlanar.CachedData.hm21_0_1_4.sums`, `OAI.SharpPlanar.CachedData.hm21_1_0_5.s0`, `OAI.SharpPlanar.CachedData.hm21_1_0_5.s1`, `OAI.SharpPlanar.CachedData.hm21_1_0_5.s2`, `OAI.SharpPlanar.CachedData.hm21_1_0_5.s3`, `OAI.SharpPlanar.CachedData.hm21_1_0_5.s4`, `OAI.SharpPlanar.CachedData.hm21_1_0_5.sums`, `OAI.SharpPlanar.CachedData.hm21_1_1_9.s0`, `OAI.SharpPlanar.CachedData.hm21_1_1_9.s1`, `OAI.SharpPlanar.CachedData.hm21_1_1_9.s2`, `OAI.SharpPlanar.CachedData.hm21_1_1_9.s3`, `OAI.SharpPlanar.CachedData.hm21_1_1_9.s4`, `OAI.SharpPlanar.CachedData.hm21_1_1_9.s5`, `OAI.SharpPlanar.CachedData.hm21_1_1_9.sums`, `OAI.SharpPlanar.CachedData.hm24_0_0_10.s0`, `OAI.SharpPlanar.CachedData.hm24_0_0_10.sums`, `OAI.SharpPlanar.CachedData.hm24_0_0_8.s0`, `OAI.SharpPlanar.CachedData.hm24_0_0_8.s1`, `OAI.SharpPlanar.CachedData.hm24_0_0_8.s2`, `OAI.SharpPlanar.CachedData.hm24_0_0_8.s3`, `OAI.SharpPlanar.CachedData.hm24_0_0_8.s4`, `OAI.SharpPlanar.CachedData.hm24_0_0_8.s5`, `OAI.SharpPlanar.CachedData.hm24_0_0_8.sums`, `OAI.SharpPlanar.CachedData.hm24_0_0_9.s0`, `OAI.SharpPlanar.CachedData.hm24_0_0_9.sums`, `OAI.SharpPlanar.CachedData.hm24_1_0_11.s0`, `OAI.SharpPlanar.CachedData.hm24_1_0_11.s1`, `OAI.SharpPlanar.CachedData.hm24_1_0_11.s2`, `OAI.SharpPlanar.CachedData.hm24_1_0_11.s3` and 77 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_HighMoments1_4`, `PlanarPacking_Certificate_HighMoments1_5`, `PlanarPacking_Certificate_HighMoments1_7`, `PlanarPacking_Certificate_LowBlock21_0`, `PlanarPacking_Certificate_LowBlock21_1`, `PlanarPacking_Certificate_LowBlock21_10`, `PlanarPacking_Certificate_LowBlock21_11`, `PlanarPacking_Certificate_LowBlock24_0`, `PlanarPacking_Certificate_LowBlock24_1`, `PlanarPacking_Certificate_LowBlock24_10`, `PlanarPacking_Certificate_LowBlock24_11`, `PlanarPacking_Certificate_LowBlock25_0`, `PlanarPacking_Certificate_LowBlock25_1`, `PlanarPacking_Certificate_LowBlock25_10`, `PlanarPacking_Certificate_LowBlock25_11`, `PlanarPacking_Certificate_LowBlock27_0`, `PlanarPacking_Certificate_LowBlock27_1`, `PlanarPacking_Certificate_LowBlock27_10`, `PlanarPacking_Certificate_LowBlock27_11`, `PlanarPacking_Certificate_LowBlock28_0`, `PlanarPacking_Certificate_LowBlock28_1`, `PlanarPacking_Certificate_LowBlock28_10`, `PlanarPacking_Certificate_LowBlock28_11`, `PlanarPacking_Certificate_LowBlock31_0`, `PlanarPacking_Certificate_LowBlock31_1`, `PlanarPacking_Certificate_LowBlock33_1`.
--
--   **Imports.** It imports the bundles `OAIQ098D041`, `OAIQ098D178`, `OAIQ098D180`, `OAIQ098D185`, `OAIQ098D186`, `OAIQ098D187`, `OAIQ098D188`, `OAIQ098D189`, `OAIQ098D190`, `OAIQ098D191`, `OAIQ098D192`, `OAIQ098D193`, `OAIQ098D194`, `OAIQ098D195`, `OAIQ098D196`, `OAIQ098D197`, `OAIQ098D198`, `OAIQ098D199`, `OAIQ098D200`, `OAIQ098D201`, `OAIQ098D202`, `OAIQ098D203`, `OAIQ098D204`, `OAIQ098D205` and `OAIQ098D206` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098D386`; the proofs of `OAI.SharpPlanar.Bernstein27.N0_left.bound`, `OAI.SharpPlanar.Bernstein27.N0_left.bound26`, `OAI.SharpPlanar.Bernstein27.N0_left.bound27`, `OAI.SharpPlanar.Bernstein27.N0_left.bound28`, `OAI.SharpPlanar.Bernstein27.N0_left.t0_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein27.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.bound`, `OAI.SharpPlanar.Bernstein27.N0_right.bound26`, `OAI.SharpPlanar.Bernstein27.N0_right.bound27`, `OAI.SharpPlanar.Bernstein27.N0_right.bound28`, `OAI.SharpPlanar.Bernstein27.N0_right.t0_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein27.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.bound`, `OAI.SharpPlanar.Bernstein27.N1_left.bound26`, `OAI.SharpPlanar.Bernstein27.N1_left.bound27`, `OAI.SharpPlanar.Bernstein27.N1_left.bound28`, `OAI.SharpPlanar.Bernstein27.N1_left.t0_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein27.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.bound`, `OAI.SharpPlanar.Bernstein27.N1_right.bound26`, `OAI.SharpPlanar.Bernstein27.N1_right.bound27`, `OAI.SharpPlanar.Bernstein27.N1_right.bound28`, `OAI.SharpPlanar.Bernstein27.N1_right.t0_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t6_contains`, `OAI.SharpPlanar.Bernstein27.N1_right.t7_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t0_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t1_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t2_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t3_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t4_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t5_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t6_contains`, `OAI.SharpPlanar.Bernstein28.N0_left.t7_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t0_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t1_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t2_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t3_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t4_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t5_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t6_contains`, `OAI.SharpPlanar.Bernstein28.N0_right.t7_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t0_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t1_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t2_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t3_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t4_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t5_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t6_contains`, `OAI.SharpPlanar.Bernstein28.N1_left.t7_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t0_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t1_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t2_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t3_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t4_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t5_contains`, `OAI.SharpPlanar.Bernstein28.N1_right.t6_contains` and `OAI.SharpPlanar.Bernstein28.N1_right.t7_contains`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D178
import Definitions.Def_OAIQ098D180
import Definitions.Def_OAIQ098D185
import Definitions.Def_OAIQ098D186
import Definitions.Def_OAIQ098D187
import Definitions.Def_OAIQ098D188
import Definitions.Def_OAIQ098D189
import Definitions.Def_OAIQ098D190
import Definitions.Def_OAIQ098D191
import Definitions.Def_OAIQ098D192
import Definitions.Def_OAIQ098D193
import Definitions.Def_OAIQ098D194
import Definitions.Def_OAIQ098D195
import Definitions.Def_OAIQ098D196
import Definitions.Def_OAIQ098D197
import Definitions.Def_OAIQ098D198
import Definitions.Def_OAIQ098D199
import Definitions.Def_OAIQ098D200
import Definitions.Def_OAIQ098D201
import Definitions.Def_OAIQ098D202
import Definitions.Def_OAIQ098D203
import Definitions.Def_OAIQ098D204
import Definitions.Def_OAIQ098D205
import Definitions.Def_OAIQ098D206

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
namespace hm1_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_3
namespace hm1_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_4
namespace hm1_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_5
namespace hm1_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_6
namespace hm1_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_7
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
namespace hm1_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_8
namespace hm1_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_9
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
namespace hm1_1_1_28
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_28
namespace hm1_1_1_29
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm1_1_1_29
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_0
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
namespace hm21_0_0_2
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_2
namespace hm21_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_2
namespace hm21_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_3
namespace hm21_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_3
namespace hm21_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_4
namespace hm21_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_4
namespace hm21_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_5
namespace hm21_1_0_5
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_5
namespace hm21_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_6
namespace hm21_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_6
namespace hm21_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_7
namespace hm21_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_1
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
namespace hm21_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_8
namespace hm21_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_8
namespace hm21_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_9
namespace hm21_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_9
namespace hm21_0_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_10
namespace hm21_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_10
namespace hm21_0_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_11
namespace hm21_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_11
namespace hm21_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_12
namespace hm21_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_12
namespace hm21_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_0_13
namespace hm21_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_10
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
namespace hm21_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_2
namespace hm21_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_2
namespace hm21_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_3
namespace hm21_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_3
namespace hm21_0_1_4
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_4
namespace hm21_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_4
namespace hm21_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_5
namespace hm21_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_5
namespace hm21_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_6
namespace hm21_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_6
namespace hm21_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_7
namespace hm21_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_11
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
namespace hm21_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_8
namespace hm21_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_8
namespace hm21_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_9
namespace hm21_1_1_9
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_9
namespace hm21_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_10
namespace hm21_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_10
namespace hm21_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_0_1_11
namespace hm21_1_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm21_1_1_11
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_0
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
namespace hm24_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_2
namespace hm24_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_2
namespace hm24_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_3
namespace hm24_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_3
namespace hm24_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_4
namespace hm24_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_4
namespace hm24_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_5
namespace hm24_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_5
namespace hm24_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_6
namespace hm24_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_6
namespace hm24_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_7
namespace hm24_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_1
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
namespace hm24_0_0_8
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_8
namespace hm24_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_8
namespace hm24_0_0_9
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_9
namespace hm24_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_9
namespace hm24_0_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_10
namespace hm24_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_10
namespace hm24_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_11
namespace hm24_1_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_11
namespace hm24_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_12
namespace hm24_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_12
namespace hm24_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_0_13
namespace hm24_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_10
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
namespace hm24_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_2
namespace hm24_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_2
namespace hm24_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_3
namespace hm24_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_3
namespace hm24_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_4
namespace hm24_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_4
namespace hm24_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_5
namespace hm24_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_5
namespace hm24_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_6
namespace hm24_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_6
namespace hm24_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_7
namespace hm24_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_11
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
namespace hm24_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_8
namespace hm24_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_8
namespace hm24_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_9
namespace hm24_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_9
namespace hm24_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_10
namespace hm24_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_10
namespace hm24_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_0_1_11
namespace hm24_1_1_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm24_1_1_11
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_0
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
namespace hm25_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_2
namespace hm25_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_2
namespace hm25_0_0_3
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_3
namespace hm25_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_3
namespace hm25_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_4
namespace hm25_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_4
namespace hm25_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_5
namespace hm25_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_5
namespace hm25_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_6
namespace hm25_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_6
namespace hm25_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_7
namespace hm25_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_1
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
namespace hm25_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_8
namespace hm25_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_8
namespace hm25_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_9
namespace hm25_1_0_9
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_9
namespace hm25_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_10
namespace hm25_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_10
namespace hm25_0_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_11
namespace hm25_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_11
namespace hm25_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_0_12
namespace hm25_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_10
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
namespace hm25_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_1_2
namespace hm25_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_1_2
namespace hm25_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_1_3
namespace hm25_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_1_3
namespace hm25_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_1_4
namespace hm25_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_1_4
namespace hm25_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_1_5
namespace hm25_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_1_5
namespace hm25_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_1_6
namespace hm25_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_1_6
namespace hm25_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_1_7
namespace hm25_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_11
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
namespace hm25_0_1_8
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_1_8
namespace hm25_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_1_8
namespace hm25_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_0_1_9
namespace hm25_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm25_1_1_9
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock27_0
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
namespace hm27_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_2
namespace hm27_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_2
namespace hm27_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_3
namespace hm27_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_3
namespace hm27_0_0_4
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_4
namespace hm27_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_4
namespace hm27_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_5
namespace hm27_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_5
namespace hm27_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_6
namespace hm27_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_6
namespace hm27_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_7
namespace hm27_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock27_1
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
namespace hm27_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_8
namespace hm27_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_8
namespace hm27_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_9
namespace hm27_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_9
namespace hm27_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_10
namespace hm27_1_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_10
namespace hm27_0_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_11
namespace hm27_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_11
namespace hm27_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_0_12
namespace hm27_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock27_10
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
namespace hm27_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_1_2
namespace hm27_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_1_2
namespace hm27_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_1_3
namespace hm27_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_1_3
namespace hm27_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_1_4
namespace hm27_1_1_4
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_1_4
namespace hm27_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_1_5
namespace hm27_1_1_5
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_1_5
namespace hm27_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_1_6
namespace hm27_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_1_6
namespace hm27_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_1_7
namespace hm27_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock27_11
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
namespace hm27_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_1_8
namespace hm27_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_1_8
namespace hm27_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_0_1_9
namespace hm27_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm27_1_1_9
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock28_0
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
namespace hm28_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_2
namespace hm28_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_2
namespace hm28_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_3
namespace hm28_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_3
namespace hm28_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_4
namespace hm28_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_4
namespace hm28_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_5
namespace hm28_1_0_5
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_5
namespace hm28_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_6
namespace hm28_1_0_6
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_6
namespace hm28_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_7
namespace hm28_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock28_1
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
namespace hm28_0_0_8
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_8
namespace hm28_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_8
namespace hm28_0_0_9
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_9
namespace hm28_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_9
namespace hm28_0_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_10
namespace hm28_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_10
namespace hm28_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_11
namespace hm28_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_11
namespace hm28_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_12
namespace hm28_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_12
namespace hm28_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_0_13
namespace hm28_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock28_10
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
namespace hm28_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_1_2
namespace hm28_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_1_2
namespace hm28_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_1_3
namespace hm28_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_1_3
namespace hm28_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_1_4
namespace hm28_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_1_4
namespace hm28_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_1_5
namespace hm28_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_1_5
namespace hm28_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_1_6
namespace hm28_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_1_6
namespace hm28_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_1_7
namespace hm28_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock28_11
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
namespace hm28_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_1_8
namespace hm28_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_1_8
namespace hm28_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_0_1_9
namespace hm28_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm28_1_1_9
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
namespace hm31_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_2
namespace hm31_1_0_2
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end hm31_1_0_2
namespace hm31_0_0_3
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_3
namespace hm31_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_4
namespace hm31_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_5
namespace hm31_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_6
namespace hm31_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_7
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
namespace hm31_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_8
namespace hm31_0_0_9
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end hm31_0_0_9
namespace hm31_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_10
namespace hm31_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_11
namespace hm31_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_12
namespace hm31_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm31_0_0_13
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
namespace hm33_0_0_13
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
end hm33_0_0_13
end SharpPlanar.CachedData

end OAI
end


