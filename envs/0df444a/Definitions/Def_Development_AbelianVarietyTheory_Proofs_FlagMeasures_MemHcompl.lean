-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:08:30.693217+00:00
-- url     : https://prove2.me/theorems/b1eaa3e8-c8bb-40fb-b4a3-052c62de307e
-- title:
--   Mem Hcompl
-- statement:
--   Definitions and structural lemmas for Mem Hcompl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.LocWitt
section Abstract
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
def Rel (h : V →ₗ⋆[K] V →ₗ[K] K) (Λ : AddSubgroup V) (x y : V) : Prop :=
  ∃ g ∈ isom h, (∀ v, g v ∈ Λ ↔ v ∈ Λ) ∧ g x = y
end Abstract
end GlobalTheory.Mass.LocWitt


