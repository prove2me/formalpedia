-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LineDegreeBundleStatement
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LineDegreeBundleStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:32.759087+00:00
-- url     : https://prove2.me/theorems/5a141c99-3088-4a18-abf4-8eefa3f881c1
-- title:
--   Line Degree Bundle Statement
-- statement:
--   Definitions and structural lemmas for Line Degree Bundle Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LineDegreeBundleStatement.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder
noncomputable section
def LineDegreeBundle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (F : HermLattice K n),
    F.lattice = (HermLattice.standard K n).lattice →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (E : HermitianBundle.{0} K')
      (φ : E.carrier ≃ₗ[𝓞 K'] (Fin n → 𝓞 K')),
      (∀ (σ' : K' →+* ℂ) (x y : E.carrier),
        (E.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 K'] x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 K'] y) =
          star (fun j ↦ σ' (φ x j : K')) ⬝ᵥ
            (F.metric (σ'.comp (algebraMap K K')) *ᵥ fun j ↦ σ' (φ y j : K'))) →
      ∀ v : Fin n → 𝓞 K', v ≠ 0 →
        HermitianBundle.normDegree E ((satLine v).comap φ.toLinearMap) =
          F.lineDegree K' fun j ↦ (v j : K')
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close


