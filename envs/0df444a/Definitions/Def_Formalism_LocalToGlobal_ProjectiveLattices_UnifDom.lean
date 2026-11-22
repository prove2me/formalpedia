-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:17.194752+00:00
-- url     : https://prove2.me/theorems/4e989b92-2f6e-4fd5-8db2-2a707430804d
-- title:
--   Unif Dom
-- statement:
--   Definitions and structural lemmas for Unif Dom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Formalism.L2.Pj


