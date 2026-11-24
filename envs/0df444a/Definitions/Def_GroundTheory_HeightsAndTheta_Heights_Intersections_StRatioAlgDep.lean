-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRatioAlgDep
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StRatioAlgDep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:43.053175+00:00
-- url     : https://prove2.me/theorems/5feef2b9-5432-4180-b32e-67be04abf7f3
-- title:
--   St Ratio Alg Dep
-- statement:
--   Definitions and structural lemmas for St Ratio Alg Dep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StRatioAlgDep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
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
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def RatioAlgDep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (d : ℕ)
    (c : ∀ k, ι k) (p : Fin d → Σ k, ι k),
    IsArithVar Q d →
    ∃ f : MvPolynomial (Fin d) ℤ, f ≠ 0 ∧
      ∀ z : (Σ k, ι k) → ℂ, (∀ g ∈ Q, eval z (map (Int.castRingHom ℂ) g) = 0) →
        (∀ k, z ⟨k, c k⟩ ≠ 0) →
          eval (fun j => z (p j) / z ⟨(p j).1, c (p j).1⟩) (map (Int.castRingHom ℂ) f) = 0
end GroundTheory.Heights₂.Heights.Inter


