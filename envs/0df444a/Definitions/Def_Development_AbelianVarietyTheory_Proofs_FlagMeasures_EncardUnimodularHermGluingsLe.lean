-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:14.595719+00:00
-- url     : https://prove2.me/theorems/b854c42c-5888-5025-b104-b34f30223187
-- title:
--   Encard Unimodular Herm Gluings Le
-- statement:
--   Definitions and structural lemmas for Encard Unimodular Herm Gluings Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUnimodularHermGluingsLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegCnt.Glue
open TensorProduct
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
section Proj
variable (H : HermSpace K V) {U : Submodule K V} (hc : IsCompl U (perp H U)) {L : Submodule (𝓞 K) V}
  (hU : IsUnimod H L) {p : V →ₗ[K] V} (hp : ∀ v, p v ∈ U) (hq : ∀ v, v - p v ∈ perp H U)
end Proj
end GlobalTheory.DegCnt.Glue


