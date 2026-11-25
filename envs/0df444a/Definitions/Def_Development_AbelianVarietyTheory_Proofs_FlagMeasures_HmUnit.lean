-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HmUnit
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HmUnit
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:22:10.572091+00:00
-- url     : https://prove2.me/theorems/412d4d4a-e054-4c3f-9b20-2db25567f84f
-- title:
--   Hm Unit
-- statement:
--   Definitions and structural lemmas for Hm Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HmUnit.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
namespace GlobalTheory.HL.StdPlace
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
def coordLat {L : LocE F E} {r k : ℕ} (S : Frames L r k) : Submodule L.O S.V :=
  Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))
structure Good {L : LocE F E} {r k : ℕ} (S : Frames L r k) : Prop where
  gg : S.gg = false
  Hm_int : IsIntM L S.Hm
  Hm_unit : ∃ y ∈ L.O, S.Hm.det * y = 1
  f_int : ∀ a i, S.f a i ∈ L.O
  f'_int : ∀ a i, S.f' a i ∈ L.O
  es_int : ∀ a i, S.es a i ∈ L.O
  es'_int : ∀ a i, S.es' a i ∈ L.O
  G_unit : S.G ∈ L.O ∧ ∃ y ∈ L.O, S.G * y = 1
  D_unit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1
end GlobalTheory.HL.StdPlace


