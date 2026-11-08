-- Prove2me | Definitions.Def_OAIQ098G365
-- name    : OAIQ098G365
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:14:53.589623+00:00
-- url     : https://prove2.me/theorems/d08f8803-3f35-47e0-8813-cb933c680f75
-- title:
--   Definitions bundle OAIQ098G365 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.IntegerBasis.densityCap`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_CanonicalRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G198` and `OAIQ098G231` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1675`, `OAIQ098G1676`, `OAIQ098G1683`, `OAIQ098G1689`, `OAIQ098G1698` and `OAIQ098G379`; the statements `OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_g`, `OAI.SharpPlanar.IntegerBasis.basis_density_bounds_g`, `OAI.SharpPlanar.IntegerBasis.uAmplitude_bound_g`, `OAI.SharpPlanar.densityCap_nonneg_g`, `OAI.SharpPlanar.piece_density_bound_g`, `OAI.SharpPlanar.piece_summand_bound_g`, `OAI.SharpPlanar.sharp_integral_piece_bound_g` and `OAI.SharpPlanar.sharp_moment_bound_g`; the proofs of `OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_g`, `OAI.SharpPlanar.IntegerBasis.basis_density_bounds_g`, `OAI.SharpPlanar.IntegerBasis.uAmplitude_bound_g`, `OAI.SharpPlanar.densityCap_nonneg_g`, `OAI.SharpPlanar.piece_density_bound_g`, `OAI.SharpPlanar.piece_summand_bound_g`, `OAI.SharpPlanar.sharp_integral_piece_bound_g` and `OAI.SharpPlanar.sharp_moment_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G198
import Definitions.Def_OAIQ098G231

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

noncomputable def densityCap (j : Fin 6) : ℝ := (densityNum j:ℝ)/(densityDen j:ℝ)

end SharpPlanar.IntegerBasis

end OAI
end


