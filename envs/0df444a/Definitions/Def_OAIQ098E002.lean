-- Prove2me | Definitions.Def_OAIQ098E002
-- name    : OAIQ098E002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T05:23:25.771294+00:00
-- url     : https://prove2.me/theorems/9ddaa777-3826-4281-a4a5-5fd936cd9a07
-- title:
--   Definitions bundle OAIQ098E002 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.SharpPlanar.Sbound`, `OAI.SharpPlanar.allNodeWeight`, `OAI.SharpPlanar.densityBound`, `OAI.SharpPlanar.kappa`, `OAI.SharpPlanar.kernelEnvelope`, `OAI.SharpPlanar.nodeWeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean).
--
--   **Imports.** It imports the bundle `OAIQ098E001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098E004` and `OAIQ098E128`; the statements `OAI.SharpPlanar.Slinear_bound_e` and `OAI.SharpPlanar.summand_bound_e`; the proofs of `OAI.SharpPlanar.Scoords_add_e`, `OAI.SharpPlanar.Scoords_mem_e`, `OAI.SharpPlanar.Slinear_bound_e`, `OAI.SharpPlanar.continuousOn_density_e` and `OAI.SharpPlanar.summand_bound_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E001

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


