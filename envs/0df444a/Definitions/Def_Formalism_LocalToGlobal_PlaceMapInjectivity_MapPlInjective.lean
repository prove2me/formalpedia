-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_PlaceMapInjectivity_MapPlInjective
-- name    : Formalism_LocalToGlobal_PlaceMapInjectivity_MapPlInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:37.435407+00:00
-- url     : https://prove2.me/theorems/7078f1d3-9e9f-4113-92d3-4276f7f5b587
-- title:
--   Map Pl Injective
-- statement:
--   Definitions and structural lemmas for Map Pl Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PlaceMapInjectivity/MapPlInjective.lean

import Definitions.Def_Formalism_ConjugateSelfDual_StatementRest
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
namespace Formalism.L2
abbrev Fld : Type := IntermediateField ℚ (AlgebraicClosure ℚ)
def mapPl {F L : Type} [Field F] [Field L] (j : F ≃+* L) (v : HeightOneSpectrum (𝓞 F)) :
    HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.comap ((RingOfIntegers.mapRingEquiv j).symm : 𝓞 L →+* 𝓞 F)
    (RingOfIntegers.mapRingEquiv j).symm.surjective v
variable (F : Type) [Field F] [NumberField F] (n : ℕ)
variable {F n}
namespace PreObj
end PreObj
variable (F n)
variable {F n}
namespace RARep
end RARep
variable (F n)
variable {F n}
variable (F n)
variable {F n}
end Formalism.L2


