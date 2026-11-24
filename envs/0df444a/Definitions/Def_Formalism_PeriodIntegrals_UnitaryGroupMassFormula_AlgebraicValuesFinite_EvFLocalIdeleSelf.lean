-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:44.44174+00:00
-- url     : https://prove2.me/theorems/ab4e0604-68bf-440d-82f2-beb56c3f770d
-- title:
--   Ev FLocal Idele Self
-- statement:
--   Definitions and structural lemmas for Ev FLocal Idele Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
namespace PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
def evF (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* (v.adicCompletion L)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 L) L => x.2 v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
def evI (w : InfinitePlace L) : Ideles L →* (w.Completion)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 L) L => x.1 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
end PI.AlgValsFin.W


