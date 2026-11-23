-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:29.127108+00:00
-- url     : https://prove2.me/theorems/5d81f806-1494-4469-a919-59e757ad6be1
-- title:
--   Class Sum Nb
-- statement:
--   Definitions and structural lemmas for Class Sum Nb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ClassSumNb.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW
namespace NbAvg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
def nbIn (M : ℕ) (P : Ideal (𝓞 E)) (A B : Lt E n) : Set (Lt E n) :=
  {X | X ∈ Nb M P A ∧ ∃ h ∈ DH E n M, Moves h B X}
def carry (M : ℕ) (P : Ideal (𝓞 E)) (A B : Lt E n) : Set (Matrix (Fin n) (Fin n) E) :=
  {h | h ∈ DH E n M ∧ ∃ X ∈ Nb M P A, Moves h B X}
end NbAvg
end GlobalTheory.SW


