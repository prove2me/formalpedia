-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:29.780219+00:00
-- url     : https://prove2.me/theorems/d9760d4e-3b23-4be1-a5cf-fffe9d410ce6
-- title:
--   Statements Fn Deg Rel Deg
-- statement:
--   Definitions and structural lemmas for Statements Fn Deg Rel Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsFnDegRelDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
def FnDegRelDeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hκv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (i' : ∀ k', ι' k'),
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsChart P' i' →
      haveI := hP'.isPrime
      ReciprocityTheory.ChartRestriction.G.AI.I1.fnDeg v P' i' = relDeg ⟨κ, hκv.1⟩ P'
section Inhabitants
def firstFactor : (Σ _ : Unit, Fin 2) → (Σ _ : Fin 2, Fin 2) := fun p => ⟨0, p.2⟩
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Targets


