-- Prove2me | Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
-- name    : GroundTheory_LocalFields_UnramifiedExistence
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:32.344568+00:00
-- url     : https://prove2.me/theorems/406fec73-1a22-4eca-a096-8d1976fc710e
-- title:
--   Unramified Existence
-- statement:
--   Definitions and structural lemmas for Unramified Existence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel IntermediateField
section Card
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
end Card
section SeparableClosure
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]
def IsUnramifiedSubextension (E : IntermediateField K Ksep) : Prop :=
  FiniteDimensional K E ∧
    ∀ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : ValuativeExtension K E), ramificationIndex K E = 1
variable {E : IntermediateField K Ksep} (hE : IsUnramifiedSubextension E)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
include hE
end SeparableClosure
end GroundTheory.LocalField


