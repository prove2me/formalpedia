-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Affine
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Affine
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:52:27.579816+00:00
-- url     : https://prove2.me/theorems/29516924-6815-4c08-8c28-b0309812c8d6
-- title:
--   Affine coordinate maps
-- statement:
--   `affineHomeomorph` packages the affine homeomorphism $x\mapsto Lx+c$ associated with a continuous linear equivalence $L$. `inverseAffineEquiv` packages its inverse $y\mapsto L^{-1}(y-c)$ as a measurable equivalence. This module provides the coordinate maps themselves; the regularity and measure-transport statements are separate declarations.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Regular.Basic
--   import FunctionalInequalities.Probability.Transport
--   import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def affineHomeomorph (L : E ≃L[ℝ] E) (c : E) : E ≃ₜ E :=
--     L.toHomeomorph.trans (Homeomorph.addRight c)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564).
--
--   Theorems in source order:
--
--   - [`RegularPotential.law_comp_affine`](https://prove2.me/theorems/a3faf409-b5c0-4734-ac62-cbff615f4315)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Affine.lean) · `FunctionalInequalities.KLS.LogConcave.Regular.Affine` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Affine.lean#L26-L32 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Regular.Affine`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Affine`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
noncomputable section
namespace FunctionalInequalities
namespace KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The affine homeomorphism `x ↦ L x + c`. -/
def affineHomeomorph (L : E ≃L[ℝ] E) (c : E) : E ≃ₜ E :=
  L.toHomeomorph.trans (Homeomorph.addRight c)
/-- The inverse affine map `y ↦ L⁻¹(y − c)` as a measurable equivalence. -/
def inverseAffineEquiv (L : E ≃L[ℝ] E) (c : E) : E ≃ᵐ E :=
  (affineHomeomorph L c).symm.toMeasurableEquiv
end KLS
end FunctionalInequalities
end


