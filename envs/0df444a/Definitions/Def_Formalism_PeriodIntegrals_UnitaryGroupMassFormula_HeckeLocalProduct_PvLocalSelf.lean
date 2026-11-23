-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:27:08.3558+00:00
-- url     : https://prove2.me/theorems/a00e7d72-dfc2-444e-bdf6-7d5d62ee6ab9
-- title:
--   Pv Local Self
-- statement:
--   Definitions and structural lemmas for Pv Local Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct
namespace PI.HeckeProdW
variable {L : Type} [Field L] [NumberField L]
def pv (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* v.adicCompletion L where
  toFun a := (a : AdeleRing (𝓞 L) L).2 v
  map_one' := rfl
  map_mul' _ _ := rfl
def pw (w : InfinitePlace L) : Ideles L →* w.Completion where
  toFun a := (a : AdeleRing (𝓞 L) L).1 w
  map_one' := rfl
  map_mul' _ _ := rfl
end PI.HeckeProdW


