-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalComplementConnected
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalComplementConnected
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:51.925542+00:00
-- url     : https://prove2.me/theorems/4100f886-6c6e-467d-9e10-64c195e42d3d
-- title:
--   St Normal Complement Connected
-- statement:
--   Definitions and structural lemmas for St Normal Complement Connected, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalComplementConnected.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology
def NormalComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I →
    ∀ U ∈ 𝓝 w, ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧
      IsPreconnected ((zeroSetIn I ∩ B) \ {z | eval z h = 0})
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


