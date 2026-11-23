-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:49.316568+00:00
-- url     : https://prove2.me/theorems/f76ce76e-7928-43f8-8183-fc9c0dfcd52b
-- title:
--   Read Alg
-- statement:
--   Definitions and structural lemmas for Read Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ReadAlg.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open MvPolynomial
section Alg
variable {K : Type} [Field K]
def cvalR (σ : K →+* ℂ) : CAt σ →+* ℂ := RingHom.id ℂ
def toCAt (σ : K →+* ℂ) (z : ℂ) : CAt σ := z
end Alg
end Formalism.L2.Pj


