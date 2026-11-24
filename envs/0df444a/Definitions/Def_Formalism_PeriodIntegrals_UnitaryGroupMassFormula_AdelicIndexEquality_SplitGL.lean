-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:13.425694+00:00
-- url     : https://prove2.me/theorems/826c44e7-c7df-45dc-b37b-9d57df957e25
-- title:
--   Split GL
-- statement:
--   Definitions and structural lemmas for Split GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitGL.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
open Matrix
variable {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
def p1 (π : R ≃+* k × k) : R →+* k := (RingHom.fst k k).comp π.toRingHom
def p2 (π : R ≃+* k × k) : R →+* k := (RingHom.snd k k).comp π.toRingHom
variable (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap)
include hπ
omit hπ in

def proj (J : Matrix n n R) : Formalism.UG.UJ σ J →* GL n k :=
  (Units.map ((p1 π).mapMatrix : Matrix n n R →+* Matrix n n k).toMonoidHom).comp (Formalism.UG.UJ σ J).subtype
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
end


