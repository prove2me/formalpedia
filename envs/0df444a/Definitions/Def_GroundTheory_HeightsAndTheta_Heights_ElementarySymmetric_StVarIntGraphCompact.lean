-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StVarIntGraphCompact
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StVarIntGraphCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:03.213966+00:00
-- url     : https://prove2.me/theorems/22a06b7a-0ba4-4d97-b88a-48f115999631
-- title:
--   St Var Int Graph Compact
-- statement:
--   Definitions and structural lemmas for St Var Int Graph Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StVarIntGraphCompact.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StVarIntGraph
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
def VarIntGraphCompact.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → HasCompactSupport F →
    (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))
end GroundTheory.Heights₂.Heights.Targets


