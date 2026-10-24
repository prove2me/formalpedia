-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
-- name    : KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:11:23.363438+00:00
-- url     : https://prove2.me/theorems/e012a531-c279-4dd2-8ba0-d8bb4a0431c5
-- title:
--   Linear isometry coercion simplification
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `LinearIsometryEquiv.coe_coe_eq_coe` is a simp lemma identifying the coercion of the continuous linear map underlying a linear isometry equivalence with the original equivalence.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/LinearAlgebra.lean#L82-L85 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.LinearAlgebra`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

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


