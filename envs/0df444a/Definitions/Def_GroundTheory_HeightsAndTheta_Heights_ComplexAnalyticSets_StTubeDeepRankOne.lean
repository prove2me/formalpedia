-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:38.022069+00:00
-- url     : https://prove2.me/theorems/1b989cb1-92cc-48b2-82ca-9a9c0e96ba0b
-- title:
--   St Tube Deep Rank One
-- statement:
--   Definitions and structural lemmas for St Tube Deep Rank One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTubeDeepRankOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets
noncomputable section
def deepMap {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  vecCons (eval y P) fun i => s y (I i)
def deepJacDet {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : ℂ :=
  LinearMap.det ((fderiv ℂ (deepMap P s I) y : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))
def TubeDeepRankOne.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (U : Set (Fin (d + 1) → ℂ)) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ),
    IsOpen U → y ∈ U → DifferentiableOn ℂ s U → (∀ y' ∈ U, A *ᵥ s y' = y') → eval y P ≠ 0 →
      ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y =
        (2 / Real.pi) ^ (d + 1) * ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 / ‖eval y P‖ ^ 2
end
end GroundTheory.Heights₂.Heights


