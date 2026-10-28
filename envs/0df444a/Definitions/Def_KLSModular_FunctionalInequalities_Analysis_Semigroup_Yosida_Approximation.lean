-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
-- name    : KLSModular_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:12:07.170997+00:00
-- url     : https://prove2.me/theorems/f0551008-67e9-4e0b-b2b9-8b7f221a39fc
-- title:
--   Yosida approximation of an adjoint product
-- statement:
--   For a closed operator $T:H_0\to H_1$ and $s>0$, `yosida T hT hs` is the bounded operator $L_s=s^{-1}(I-J_s)$, where $J_s$ is the resolvent. `yosida_apply` gives the pointwise formula $L_sf=s^{-1}(f-J_sf)$. No nonnegativity, symmetry, convergence, or identification with $T^\dagger T J_s$ is asserted in this bundle.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def yosida (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) : H₀ →L[ℝ] H₀ :=
--     s⁻¹ • (ContinuousLinearMap.id ℝ H₀ - resolventCLM T hT hs)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Semigroup/Resolvent/Basic`](https://prove2.me/theorems/5d32777c-2d23-4054-9716-770b34fae308).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Approximation.lean) · `FunctionalInequalities.Analysis.Semigroup.Yosida.Approximation` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Approximation.lean#L25-L32 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Yosida.Approximation`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic

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


