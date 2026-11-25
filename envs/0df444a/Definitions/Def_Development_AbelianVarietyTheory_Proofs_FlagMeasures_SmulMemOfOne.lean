-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:17.942574+00:00
-- url     : https://prove2.me/theorems/17c47f21-dc1a-461c-add0-2867dda36cf1
-- title:
--   Smul Mem Of One
-- statement:
--   Definitions and structural lemmas for Smul Mem Of One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SmulMemOfOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.FrameMove
section Proj
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Proj
section Form
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
def Hyp (H : HermSpace K V) (e y : Fin r → V) : Prop :=
  (∀ a b, H.B (e a) (e b) = 0) ∧ (∀ a b, H.B (y a) (y b) = 0) ∧ ∀ a b, H.B (e a) (y b) = if a = b then 1 else 0
noncomputable def mid (H : HermSpace K V) (e y : Fin r → V) : V →ₗ[K] V :=
  LinearMap.id - ∑ a, (H.B.flip (y a)).smulRight (e a) - ∑ a, (H.B.flip (e a)).smulRight (y a)
noncomputable def move (H : HermSpace K V) (e y e' y' : Fin r → V) : V →ₗ[K] V :=
  ∑ a, (H.B.flip (y a)).smulRight (e' a) + ∑ a, (H.B.flip (e a)).smulRight (y' a) + mid H e' y' ∘ₗ mid H e y
end Form
section Lat
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
end Lat
end GlobalTheory.DegAsm.FrameMove


