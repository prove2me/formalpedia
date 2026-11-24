-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:20.454162+00:00
-- url     : https://prove2.me/theorems/fe29ae10-fc41-4a04-8ffd-af643e1a2de9
-- title:
--   Graph Ideal
-- statement:
--   Definitions and structural lemmas for Graph Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}
def graphHom (p : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) ℂ) p : Fin (n + 1) → MvPolynomial (Fin n) ℂ)
def graphIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
  J.comap (graphHom p)
def graphPt (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.snoc x (eval x p)
end GroundTheory.Heights₂.Heights.Targets


