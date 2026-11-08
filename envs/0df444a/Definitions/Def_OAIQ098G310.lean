-- Prove2me | Definitions.Def_OAIQ098G310
-- name    : OAIQ098G310
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:08:30.157468+00:00
-- url     : https://prove2.me/theorems/0a9246b3-9057-4bcb-b306-8d876babfb97
-- title:
--   Definitions bundle OAIQ098G310 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel9_0Expr`, `OAI.SharpPlanar.CachedData.kernel9_1Expr`, `OAI.SharpPlanar.CachedData.trans10Expr`, `OAI.SharpPlanar.CachedData.trans9`, `OAI.SharpPlanar.CachedData.trans9_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues10.lean), [`PlanarPacking_Certificate_TransformedPowers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G064`, `OAIQ098G271` and `OAIQ098G308` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein9.N0_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t13_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t12_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t13_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t13_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t12_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t13_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t8_contains_g`, `OAI.SharpPlanar.CachedData.hk9_1_13_contains_g`, `OAI.SharpPlanar.CachedData.hk9_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hk9_1_8_contains_g`, `OAI.SharpPlanar.CachedData.hm9_0_1_11.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_1_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_1_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_1_7.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_0_1_9.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_1_11.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_1_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_1_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_1_7.realContains_g`, `OAI.SharpPlanar.CachedData.hm9_1_1_9.realContains_g`, `OAI.SharpPlanar.CachedData.kernel12_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel12_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel13_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel13_1_contains_g`, `OAI.SharpPlanar.CachedData.trans15_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_5_contains_g`, `OAI.SharpPlanar.Residual9.bound0_0_g`, `OAI.SharpPlanar.Residual9.bound0_1_g`, `OAI.SharpPlanar.Residual9.bound1_0_g` and `OAI.SharpPlanar.Residual9.bound1_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G064
import Definitions.Def_OAIQ098G271
import Definitions.Def_OAIQ098G308

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
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
noncomputable def trans9_r0 : Fin 16 → Fin 16 → CBox := ![trans9_r0_0,trans9_r0_1,trans9_r0_2,trans9_r0_3,trans9_r0_4,trans9_r0_5,trans9_r0_6,trans9_r0_7,trans9_r0_8,trans9_r0_9,trans9_r0_10,trans9_r0_11,trans9_r0_12,trans9_r0_13,trans9_r0_14,trans9_r0_15]
noncomputable def trans9 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans9_r0,trans9_r1,trans9_r2,trans9_r3,trans9_r4,trans9_r5]
noncomputable def trans10Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans9 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
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
noncomputable def kernel9_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans9 j i k)
noncomputable def kernel9_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans9 j i k)).mul (piI.mul (gridRows j i k).z)
end SharpPlanar.CachedData

end OAI
end


