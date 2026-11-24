-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:26.108902+00:00
-- url     : https://prove2.me/theorems/df6e380d-338f-43e8-a0f1-264e9d61f723
-- title:
--   PCone Map Area One
-- statement:
--   Definitions and structural lemmas for PCone Map Area One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
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
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal NNReal ComplexOrder
namespace ConeMapAreaFormula
def reImL (m : ℕ) : EuclideanSpace ℂ (Fin m) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin 2) where
  toFun y := WithLp.toLp 2 fun p => (![(y p.1).re, (y p.1).im] : Fin 2 → ℝ) p.2
  invFun w := WithLp.toLp 2 fun i => ⟨w (i, 0), w (i, 1)⟩
  map_add' y z := by
    ext p
    obtain ⟨i, k⟩ := p
    fin_cases k <;> simp
  map_smul' c y := by
    ext p
    obtain ⟨i, k⟩ := p
    fin_cases k <;> simp
  left_inv y := by
    ext i
    simp
  right_inv w := by
    ext p
    obtain ⟨i, k⟩ := p
    fin_cases k <;> simp
theorem reImL_apply (m : ℕ) (y : EuclideanSpace ℂ (Fin m)) (p : Fin m × Fin 2) :
    reImL m y p = (![(y p.1).re, (y p.1).im] : Fin 2 → ℝ) p.2 :=
  rfl
theorem norm_reImL (m : ℕ) (y : EuclideanSpace ℂ (Fin m)) : ‖reImL m y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [reImL_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply, sq, sq]
def reIm (m : ℕ) : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m × Fin 2) :=
  { reImL m with norm_map' := norm_reImL m }
def splitE (e : ℕ) : EuclideanSpace ℂ (Fin (e + 1)) ≃ᵐ (Fin e → ℂ) × ℂ :=
  ((MeasurableEquiv.toLp 2 (Fin (e + 1) → ℂ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0)).trans MeasurableEquiv.prodComm
def tailL (e : ℕ) : EuclideanSpace ℂ (Fin (e + 1)) →L[ℂ] (Fin e → ℂ) :=
  ContinuousLinearMap.pi fun j => EuclideanSpace.proj j.succ
def coneMapE {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (p : EuclideanSpace ℂ (Fin (e + 1))) :
    EuclideanSpace ℂ (Fin n) :=
  p 0 • WithLp.toLp 2 (v (tailL e p))
def gramVecs {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) : Fin (e + 1) → Fin n → ℂ :=
  Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
def coneIntegrand {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞)
    (q : (Fin e → ℂ) × ℂ) : ℝ≥0∞ :=
  F (q.2 • WithLp.toLp 2 (v q.1)) * ENNReal.ofReal (‖q.2‖ ^ (2 * e) * gramVol v q.1)
end ConeMapAreaFormula
end GroundTheory.Heights₂.Heights


