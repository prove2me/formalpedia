-- Prove2me | Definitions.Def_CK_GeneralCK_EntropyCurvatureDefs
-- name    : CK_GeneralCK_EntropyCurvatureDefs
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:38:40.398679+00:00
-- url     : https://prove2.me/theorems/4324c317-9ec3-400a-adde-0be0c7bd664f
-- title:
--   Courtade–Kumar proof module `GeneralCK.EntropyCurvatureDefs` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EntropyCurvatureDefs` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EntropyCurvatureDefs` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EntropyCurvatureDefs (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyCurvatureDefs.lean)

import Definitions.Def_CK_GeneralCK_EntropyRadialDerivatives
import Definitions.Def_CK_GeneralCK_ProfileConvexity

namespace GeneralCK.EntropyCurvature

/-- The two natural-unit scalar signs in the upstream entropy-convexity proof. -/
noncomputable def polyP (x t B : ℝ) : ℝ :=
  B^3*(x*(1+t^2)-t)-x^3*t^2*(2*B-t^2)

noncomputable def polyR (x t B : ℝ) : ℝ :=
  4*B^3*(1+t^2)-2*B^2*t^3*x-8*B^2*t^2-6*B^2*t*x
    -B*t^5*x+3*B*t^4+9*B*t^3*x-3*t^5*x

noncomputable def xi (v : ℝ) : ℝ := Real.log 2*J v/2
noncomputable def P (v : ℝ) : ℝ := polyP (xi v) (1-2*v) (Certificates.Mixed.kap v)
noncomputable def R (v : ℝ) : ℝ := polyR (xi v) (1-2*v) (Certificates.Mixed.kap v)

/-- Natural entropy times natural entropy curvature of the perspective at its cap contact. -/
noncomputable def beta (v : ℝ) : ℝ :=
  2*Certificates.Mixed.hn v*(1-2*v)^2*(2*Certificates.Mixed.kap v-(1-2*v)^2) /
    ((Certificates.Mixed.kap v)^3*(4*v*(1-v))^2)

end GeneralCK.EntropyCurvature


