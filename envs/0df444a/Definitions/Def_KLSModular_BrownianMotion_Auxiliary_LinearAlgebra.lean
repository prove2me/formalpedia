-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_LinearAlgebra
-- name    : KLSModular_BrownianMotion_Auxiliary_LinearAlgebra
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:35:28.28236+00:00
-- url     : https://prove2.me/theorems/2645f527-2309-4864-b86a-3ed36f94d2a7
-- title:
--   Linear isometry coercion simplification
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `LinearIsometryEquiv.coe_coe_eq_coe` is a simp lemma identifying the coercion of the continuous linear map underlying a linear isometry equivalence with the original equivalence.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.Analysis.InnerProductSpace.Dual
--   public import Mathlib.LinearAlgebra.Matrix.PosDef
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   @[simp]
--   lemma LinearIsometryEquiv.coe_coe_eq_coe {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
--       [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F) :
--       ⇑f.toLinearIsometry.toContinuousLinearMap = ⇑f := rfl
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/LinearAlgebra.lean) · `BrownianMotion.Auxiliary.LinearAlgebra` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/LinearAlgebra.lean#L82-L85 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.LinearAlgebra`, definition bundle `KLSModular_BrownianMotion_Auxiliary_LinearAlgebra`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Matrix.PosDef

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/LinearAlgebra.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
section InnerProductSpace
open scoped InnerProductSpace
@[simp]
lemma LinearIsometryEquiv.coe_coe_eq_coe {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F) :
    ⇑f.toLinearIsometry.toContinuousLinearMap = ⇑f := rfl
end InnerProductSpace


