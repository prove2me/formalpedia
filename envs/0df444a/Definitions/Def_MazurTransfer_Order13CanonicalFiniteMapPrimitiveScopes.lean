-- Prove2me | Definitions.Def_MazurTransfer_Order13CanonicalFiniteMapPrimitiveScopes
-- name    : MazurTransfer_Order13CanonicalFiniteMapPrimitiveScopes
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T05:24:31.048977+00:00
-- url     : https://prove2.me/theorems/15a68620-9bcc-4768-bce8-70712ef67ad8
-- title:
--   The original scoped inverse-parameter algebra and module actions
-- statement:
--   This interface restores the original namespace-scoped algebra actions on the canonical aliases of the inverse-parameter primitives. The polynomial parameter acts by the specified inverse parameter $S\mapsto s$, its scalar and module actions use that algebra structure, and the candidate algebra has the specified base-ring algebra structure and compatible scalar tower. Three checked reflexive identities verify that instance search selects the specified actions. The five action values and their types are unchanged. This supplies the intended scalar structures for the inverse finite-chart basis and structural coefficient comparison.
-- source:
--   Namespace-scope restoration for five canonical aliases from public Def_MazurTransfer_Order13CanonicalFiniteMapPrimitives. Original Lean declaration ranges identify the five scoped-instance declarations. All five types and action values are kernel-compared again with the original public primitive library; the three coherence equalities are checked by reflexivity. No original alias, value, or mathematical statement is edited. Apache-2.0. Named downstream consumers are the inverse finite-chart polynomial basis and actual FiniteMapData. Vas and contributors.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restore the original five namespace-scoped parameter and base algebra actions on the canonical aliases of the published inverse-parameter primitives. The aliases and their values are unchanged.
Named downstream consumer: the original inverse finite-chart polynomial basis and structural coefficient comparison for actual FiniteMapData. -/
import Definitions.Def_MazurTransfer_Order13CanonicalFiniteMapPrimitives
noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
attribute [scoped instance] parameterAlgebra parameterSMul parameterModule
attribute [scoped instance] candidateBaseAlgebra candidateBaseTower
open Polynomial
open MazurTransfer.Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]
theorem canonicalParameterAlgebra_scope_coherent :
    (inferInstance : Algebra (Polynomial R) (ordinaryParameterLocalization R)) =
      parameterAlgebra R := rfl
theorem canonicalParameterModule_scope_coherent :
    (inferInstance : Module (Polynomial R) (ordinaryParameterLocalization R)) =
      parameterModule R := rfl
theorem canonicalCandidateBaseAlgebra_scope_coherent :
    (inferInstance : Algebra R (candidateAlgebra R)) = candidateBaseAlgebra R := rfl
end MazurTransfer.Order13InverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.canonicalParameterAlgebra_scope_coherent
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.canonicalParameterModule_scope_coherent
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.canonicalCandidateBaseAlgebra_scope_coherent


