-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
-- name    : GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:55.080829+00:00
-- url     : https://prove2.me/theorems/a3b89c21-a507-4282-83a5-2f18c7fff238
-- title:
--   Theta Three Fam Linear Independent
-- statement:
--   Definitions and structural lemmas for Theta Three Fam Linear Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
def lineCoeff (h : ℂ → ℂ) (k : ℤ) (y : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, h (x + y * I) * cexp (-2 * π * I * k * (x + y * I))
def thetaThree (ν : ℕ) (w : ℂ) : ℂ :=
  cexp (π * I * ν ^ 2 * I / 3 + 2 * π * I * ν * w) * jacobiTheta₂ (3 * w + ν * I) (3 * I)
def zeta3 : ℂ := cexp (2 * π * I / 3)
def thetaThreeSec (ν : ℕ) : (Fin 1 → ℂ) → ℂ := fun z => thetaThree ν (z 0)
def thetaThreeFam : Fin (2 + 1) → (Fin 1 → ℂ) → ℂ := fun ν => thetaThreeSec ν
abbrev thetaThreeSpace : Submodule ℂ ((Fin 1 → ℂ) → ℂ) := thetaSec tauI (HalfChar.zero 1) 3
lemma line_continuous {f : (Fin 1 → ℂ) → ℂ} (hf : f ∈ thetaThreeSpace) (k : ℕ) :
    Continuous (fun x : ℝ => f (fun _ => (x : ℂ)) * cexp (-2 * π * I * k * x)) :=
  (hf.1.continuous.comp (continuous_pi fun _ => Complex.continuous_ofReal)).mul (by fun_prop)
def coeffMap : thetaThreeSpace →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun f k := ∫ x in (0 : ℝ)..1,
    (f : (Fin 1 → ℂ) → ℂ) (fun _ => (x : ℂ)) * cexp (-2 * π * I * (k : ℕ) * x)
  map_add' f h := by
    funext k
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    exact intervalIntegral.integral_add
      ((line_continuous f.2 k).intervalIntegrable 0 1) ((line_continuous h.2 k).intervalIntegrable 0 1)
  map_smul' c f := by
    funext k
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact intervalIntegral.integral_const_mul _ _
end
end GroundTheory.Heights₂.Heights.KeyFormula


