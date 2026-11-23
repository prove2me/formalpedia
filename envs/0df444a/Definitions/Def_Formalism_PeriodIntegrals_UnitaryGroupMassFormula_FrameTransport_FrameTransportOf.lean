-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_FrameTransportOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_FrameTransportOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:35.167729+00:00
-- url     : https://prove2.me/theorems/a01278d6-4363-4e0a-ae4c-988d8d90149f
-- title:
--   Frame Transport Of
-- statement:
--   Definitions and structural lemmas for Frame Transport Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/FrameTransportOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
instance instBorelHA {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : BorelSpace (HA (AF F) σ J) :=
  ⟨rfl⟩
end PI.FT


