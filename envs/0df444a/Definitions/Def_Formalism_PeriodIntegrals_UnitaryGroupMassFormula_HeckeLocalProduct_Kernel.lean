-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:14.285556+00:00
-- url     : https://prove2.me/theorems/738763a5-c186-485d-8205-7d906463c535
-- title:
--   Kernel
-- statement:
--   Definitions and structural lemmas for Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/Kernel.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Lemmata_MiscLemmasM_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct Topology
namespace PI.HeckeProdW
variable (L : Type) [Field L] [NumberField L]
abbrev Pu : Type := (v : HeightOneSpectrum (𝓞 L)) → (v.adicCompletionIntegers L)ˣ
def gI : ((v : HeightOneSpectrum (𝓞 L)) → v.adicCompletionIntegers L) →* AdeleRing (𝓞 L) L where
  toFun x := ((1 : InfiniteAdeleRing L),
    (structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => v.adicCompletionIntegers L) Filter.cofinite x : FiniteAdeleRing (𝓞 L) L))
  map_one' := rfl
  map_mul' _ _ := Prod.ext (mul_one 1).symm rfl
def Phi : Pu L →* Ideles L :=
  (Units.map (gI L)).comp (MulEquiv.piUnits (M := fun v : HeightOneSpectrum (𝓞 L) =>
    v.adicCompletionIntegers L)).symm.toMonoidHom
variable {L}
end PI.HeckeProdW


