-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StVarIntGraph
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StVarIntGraph
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:32.468746+00:00
-- url     : https://prove2.me/theorems/45c9790f-41ee-48cd-a4e9-31a4d6cbe64a
-- title:
--   St Var Int Graph
-- statement:
--   Definitions and structural lemmas for St Var Int Graph, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StVarIntGraph.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights (varInt SmoothNear euclPot contDiff_euclPot)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
open scoped ContDiff
def VarIntGraph.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))
end GroundTheory.Heights₂.Heights.Targets


