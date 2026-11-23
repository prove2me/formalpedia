-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:57.292621+00:00
-- url     : https://prove2.me/theorems/e6902f5f-befe-493b-b4a7-3d84cfc8d4fc
-- title:
--   Flow Basic
-- statement:
--   Definitions and structural lemmas for Flow Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowBasic.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace Formalism.L2.Th1.A
namespace IsDer
variable {A : Type u} [CommRing A] {D : A → A}
theorem map_zero (h : IsDer D) : D 0 = 0 := by
  have h0 := h.1 0 0
  rw [add_zero] at h0
  linear_combination -h0
def toDerivation (h : IsDer D) : Derivation ℤ A A :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap ⟨⟨D, h.map_zero⟩, h.1⟩) fun a b => by
    simpa [smul_eq_mul] using h.2 a b
end IsDer
end Formalism.L2.Th1.A


