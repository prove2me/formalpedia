-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:58:08.956707+00:00
-- url     : https://prove2.me/theorems/ec9ecc92-9715-4e58-bb7f-51aa9e95da85
-- title:
--   Eq WSer Subst
-- statement:
--   Definitions and structural lemmas for Eq WSer Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/EqWSerSubst.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.L2.Th1.A
namespace ISer
variable {R : Type u} [CommRing R]
def subHom (s : R⟦X⟧) (hs : constantCoeff s = 0) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom (HasSubst.of_constantCoeff_zero' hs)
end ISer
end Formalism.L2.Th1.A


