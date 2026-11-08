-- Prove2me | Definitions.Def_OAIQ098G002
-- name    : OAIQ098G002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T17:28:44.046955+00:00
-- url     : https://prove2.me/theorems/95885f8c-07ae-4b88-960f-c5536435421d
-- title:
--   Definitions bundle OAIQ098G002 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.SharpPlanar.Sbound`, `OAI.SharpPlanar.allNodeWeight`, `OAI.SharpPlanar.densityBound`, `OAI.SharpPlanar.kappa`, `OAI.SharpPlanar.kernelEnvelope`, `OAI.SharpPlanar.nodeWeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G004` and `OAIQ098G381`; the statements `OAI.SharpPlanar.Slinear_bound_g`, `OAI.SharpPlanar.direct_basis_integral_bound_g` and `OAI.SharpPlanar.summand_bound_g`; the proofs of `OAI.SharpPlanar.Scoords_add_g`, `OAI.SharpPlanar.Scoords_mem_g`, `OAI.SharpPlanar.Slinear_bound_g`, `OAI.SharpPlanar.continuousOn_density_g`, `OAI.SharpPlanar.directDensity_tsum_g`, `OAI.SharpPlanar.direct_basis_integral_bound_g`, `OAI.SharpPlanar.direct_basis_integral_summable_g` and `OAI.SharpPlanar.summand_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G001

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

noncomputable def kappa : ℝ := 26 * Real.pi / 435

noncomputable def densityBound : ℝ := 20 * Real.pi^2


noncomputable def kernelEnvelope (ell : ℕ) (s : ℝ) : ℝ :=
  (1/(b*h)) * (Real.pi*(B/h+h))^ell * Real.exp (-kappa*s)

noncomputable def nodeWeight (n : ℕ) : ℝ := (1 + |D n|) / Q n
noncomputable def allNodeWeight : ℝ := ∑ a ∈ residues, nodeWeight a

noncomputable def Sbound : ℝ := allNodeWeight * densityBound *
  ∑' ni : Node × Bool, (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val)

end SharpPlanar

end OAI
end


