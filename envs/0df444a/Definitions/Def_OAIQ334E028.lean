-- Prove2me | Definitions.Def_OAIQ334E028
-- name    : OAIQ334E028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T12:54:24.966769+00:00
-- url     : https://prove2.me/theorems/ba1572a7-064f-4c22-814b-83b0ab767000
-- title:
--   Definitions bundle OAIQ334E028 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 definition and 1 theorem. The definitions and types are `OAI.AtomicTriangular.gaussianSchwartz`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularEnergy`; the bundle `OAIQ334E006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ334E029`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E006

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_GaussianPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular
open Construction

def gaussianSchwartz (α : ℝ) (hα : 0<α) : 𝓢(Plane,ℝ) :=
  Analysis.gaussianSchwartz (Real.pi*α) (mul_pos Real.pi_pos hα)
lemma realFourier_sub (f g : 𝓢(Plane,ℝ)) (w : Plane) :
    realFourier ((f-g : 𝓢(Plane,ℝ)) : Plane → ℝ) w=realFourier f w-realFourier g w := by
  have hf : Integrable (fun x => (f x:ℂ)) := f.integrable.ofReal
  have hg : Integrable (fun x => (g x:ℂ)) := g.integrable.ofReal
  simp only [realFourier,sub_apply,ofReal_sub,Real.fourier_eq,smul_sub]
  rw [integral_sub ((Real.fourierIntegral_convergent_iff w).mpr hf)
    ((Real.fourierIntegral_convergent_iff w).mpr hg)]

end AtomicTriangular
end

end OAI
end


