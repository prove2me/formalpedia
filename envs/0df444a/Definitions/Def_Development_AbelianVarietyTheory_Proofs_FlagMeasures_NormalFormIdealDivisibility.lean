-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:02:36.256483+00:00
-- url     : https://prove2.me/theorems/4ce512ff-1f0b-4275-a326-c502d3429f09
-- title:
--   Normal Form Ideal Divisibility
-- statement:
--   Definitions and structural lemmas for Normal Form Ideal Divisibility, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormIdealDivisibility.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
section Geometry
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def Ia (N : NF H r) (n : ℕ) : Submodule K V :=
  Submodule.span K ((fun b : Fin r => N.F.e b.castSucc) '' {b | N.j ≤ b.val ∧ b.val < n})
def Gs (N : NF H r) : Subgroup (V ≃ₗ[K] V) := N.Rs ⊓ N.fixing (N.F.Xa N.j ⊔ N.F'.Xa N.j)
end Geometry
end GlobalTheory.DegCnt.PosIso


