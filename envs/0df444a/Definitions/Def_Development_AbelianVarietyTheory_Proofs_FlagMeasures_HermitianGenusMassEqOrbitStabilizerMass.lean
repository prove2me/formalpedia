-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianGenusMassEqOrbitStabilizerMass
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianGenusMassEqOrbitStabilizerMass
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T04:26:13.628799+00:00
-- url     : https://prove2.me/theorems/5be411dc-3cb2-57bc-8de3-f03ff985a96d
-- title:
--   Hermitian Genus Mass Eq Orbit Stabilizer Mass
-- statement:
--   Definitions and structural lemmas for Hermitian Genus Mass Eq Orbit Stabilizer Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianGenusMassEqOrbitStabilizerMass.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumEqSumOrbitReps
import Definitions.Def_Formalism_HermitianLattices_FinalMass
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
namespace GlobalTheory.Mass.GenusOrb
section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def autEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) :
    Formalism.ThetaLiftIndependence.autL h M ≃ MulAction.stabilizer (isom h) M where
  toFun g := ⟨⟨g.1, g.2.1⟩, g.2.2⟩
  invFun g := ⟨g.1.1, g.1.2, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
end
end GlobalTheory.Mass.GenusOrb


