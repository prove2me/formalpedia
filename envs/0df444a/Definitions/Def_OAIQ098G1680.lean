-- Prove2me | Definitions.Def_OAIQ098G1680
-- name    : OAIQ098G1680
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:30:48.185237+00:00
-- url     : https://prove2.me/theorems/1f6a1c7b-1f42-4e00-a349-1473cd8bffbe
-- title:
--   Definitions bundle OAIQ098G1680 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.fullFactor`, `OAI.SharpPlanar.fullMomentAtom`, `OAI.SharpPlanar.tableMomentAtom`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_HighMomentsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/HighMomentsBase.lean), [`PlanarPacking_TableMomentsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TableMomentsBase.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G072` and `OAIQ098G1643` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1682`; the statements `OAI.SharpPlanar.CachedData.hk0_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk0_0_19_contains_g`, `OAI.SharpPlanar.CachedData.hk0_1_14_contains_g`, `OAI.SharpPlanar.CachedData.hk0_1_19_contains_g`, `OAI.SharpPlanar.CachedData.hk0_1_24_contains_g`, `OAI.SharpPlanar.CachedData.hk0_1_9_contains_g`, `OAI.SharpPlanar.CachedData.hk12_0_2_contains_g`, `OAI.SharpPlanar.CachedData.hk12_0_8_contains_g`, `OAI.SharpPlanar.CachedData.hk13_0_8_contains_g`, `OAI.SharpPlanar.CachedData.hk15_0_7_contains_g`, `OAI.SharpPlanar.CachedData.hk15_0_8_contains_g`, `OAI.SharpPlanar.CachedData.hk15_1_9_contains_g`, `OAI.SharpPlanar.CachedData.hk16_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk16_0_7_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_13_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_8_contains_g`, `OAI.SharpPlanar.CachedData.hk19_0_12_contains_g`, `OAI.SharpPlanar.CachedData.hk19_0_13_contains_g`, `OAI.SharpPlanar.CachedData.hk19_0_3_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_29_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_30_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_8_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_14_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_19_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_24_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_29_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_9_contains_g`, `OAI.SharpPlanar.CachedData.hk24_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk24_0_7_contains_g`, `OAI.SharpPlanar.CachedData.hk24_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk25_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hk25_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk25_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk27_0_12_contains_g`, `OAI.SharpPlanar.CachedData.hk27_0_3_contains_g`, `OAI.SharpPlanar.CachedData.hk31_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk33_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hk36_0_2_contains_g`, `OAI.SharpPlanar.CachedData.hk37_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hk39_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk3_1_12_contains_g`, `OAI.SharpPlanar.CachedData.hk3_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk4_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk4_0_2_contains_g`, `OAI.SharpPlanar.CachedData.hk9_0_15_contains_g`, `OAI.SharpPlanar.CachedData.hk9_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hk9_1_13_contains_g`, `OAI.SharpPlanar.CachedData.hk9_1_3_contains_g` and `OAI.SharpPlanar.CachedData.hk9_1_8_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.hk0_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk0_0_19_contains_g`, `OAI.SharpPlanar.CachedData.hk0_1_14_contains_g`, `OAI.SharpPlanar.CachedData.hk0_1_19_contains_g`, `OAI.SharpPlanar.CachedData.hk0_1_24_contains_g`, `OAI.SharpPlanar.CachedData.hk0_1_9_contains_g`, `OAI.SharpPlanar.CachedData.hk12_0_2_contains_g`, `OAI.SharpPlanar.CachedData.hk12_0_8_contains_g`, `OAI.SharpPlanar.CachedData.hk13_0_8_contains_g`, `OAI.SharpPlanar.CachedData.hk15_0_7_contains_g`, `OAI.SharpPlanar.CachedData.hk15_0_8_contains_g`, `OAI.SharpPlanar.CachedData.hk15_1_9_contains_g`, `OAI.SharpPlanar.CachedData.hk16_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk16_0_7_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_13_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_8_contains_g`, `OAI.SharpPlanar.CachedData.hk19_0_12_contains_g`, `OAI.SharpPlanar.CachedData.hk19_0_13_contains_g`, `OAI.SharpPlanar.CachedData.hk19_0_3_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_29_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_30_contains_g`, `OAI.SharpPlanar.CachedData.hk1_0_8_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_14_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_19_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_24_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_29_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_9_contains_g`, `OAI.SharpPlanar.CachedData.hk24_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk24_0_7_contains_g`, `OAI.SharpPlanar.CachedData.hk24_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk25_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hk25_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk25_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk27_0_12_contains_g`, `OAI.SharpPlanar.CachedData.hk27_0_3_contains_g`, `OAI.SharpPlanar.CachedData.hk31_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk33_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hk36_0_2_contains_g`, `OAI.SharpPlanar.CachedData.hk37_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hk39_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk3_1_12_contains_g`, `OAI.SharpPlanar.CachedData.hk3_1_2_contains_g`, `OAI.SharpPlanar.CachedData.hk4_0_18_contains_g`, `OAI.SharpPlanar.CachedData.hk4_0_2_contains_g`, `OAI.SharpPlanar.CachedData.hk9_0_15_contains_g`, `OAI.SharpPlanar.CachedData.hk9_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hk9_1_13_contains_g`, `OAI.SharpPlanar.CachedData.hk9_1_3_contains_g` and `OAI.SharpPlanar.CachedData.hk9_1_8_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G1643

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableMomentsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Certified quadrature and atomic bounds for the Gaussian moments -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
open scoped BigOperators

noncomputable def tableMomentAtom (a : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ((tableConstant a:ℝ):ℂ) * ∑ j : Fin 7,
    (if j.val=0 then 1 else 2) * Pcoeff j.val *
      complexTransformedFactor m 1 ell ((j.val:ℝ)/6)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighMomentsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval enclosures for direct and transformed moments of arbitrary order -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
noncomputable def fullFactor (tr : Bool) (m : ℝ) (ell : ℕ) (t : ℂ) : ℂ :=
  if tr then complexTransformedFactor m 1 ell t else complexDirectFactor m 1 ell t
noncomputable def fullMomentAtom (a tr : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ((tableConstant a:ℝ):ℂ)*∑ j : Fin 7,
    (if j.val=0 then 1 else 2)*Pcoeff j.val*fullFactor tr m ell ((j.val:ℝ)/6)
end SharpPlanar

end OAI
end


