-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_RulInst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:12.11492+00:00
-- url     : https://prove2.me/theorems/e674d693-a64b-4f1e-966d-dd0767c0e204
-- title:
--   Rul Inst
-- statement:
--   Definitions and structural lemmas for Rul Inst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RulInst.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
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
open NumberField
section
variable {K : Type} [Field K] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
instance (priority := high) rulesCommRing : CommRing (Rules pts) := inferInstance
instance (priority := high) rulesAlgebra : Algebra K (Rules pts) := inferInstance
instance (priority := high) rulesModule : Module K (Rules pts) := inferInstance
instance (priority := high) rulesSMul : SMul K (Rules pts) := inferInstance
instance (priority := high) rulesAlgebraInt : Algebra (𝓞 K) (Rules pts) := inferInstance
instance (priority := high) rulesModuleInt : Module (𝓞 K) (Rules pts) := inferInstance
instance (priority := high) rulesTower : IsScalarTower (𝓞 K) K (Rules pts) := inferInstance
end
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
example : Algebra c.F (Rul Xo c) := inferInstance
example : Algebra (𝓞 c.F) (Rul Xo c) := inferInstance
example : IsScalarTower (𝓞 c.F) c.F (Rul Xo c) := inferInstance
example (a : c.F) (f : Rul Xo c) : Rul Xo c := a • f
example (a : 𝓞 c.F) (f : Rul Xo c) : Rul Xo c := a • f
end Formalism.L2.Pj


