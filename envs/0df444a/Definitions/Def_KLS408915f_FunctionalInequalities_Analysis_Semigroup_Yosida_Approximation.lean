-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
-- name    : KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:12:45.517059+00:00
-- url     : https://prove2.me/theorems/7d58ecf3-0be4-4b4c-ac3c-4ad63fefd3e0
-- title:
--   Yosida approximation of an adjoint product
-- statement:
--   For a closed operator $T:H_0\to H_1$ and $s>0$, `yosida T hT hs` is the bounded operator $L_s=s^{-1}(I-J_s)$, where $J_s` is the resolvent. `yosida_apply` gives the pointwise formula $L_sf=s^{-1}(f-J_sf)$. No nonnegativity, symmetry, convergence, or identification with $T^\dagger T J_s$ is asserted in this bundle.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Approximation.lean#L25-L32 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Yosida.Approximation`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
/-- The Yosida approximation `L_s = s⁻¹ • (1 - J_s)` of `T†T`, a bounded operator on `H₀`. -/
def yosida (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) : H₀ →L[ℝ] H₀ :=
  s⁻¹ • (ContinuousLinearMap.id ℝ H₀ - resolventCLM T hT hs)
/-- `L_s f = s⁻¹ • (f - J_s f)`. -/
theorem yosida_apply (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀) :
    yosida T hT hs f = s⁻¹ • (f - resolventCLM T hT hs f) := by
  simp [yosida]
end Semigroup
end Analysis
end FunctionalInequalities


