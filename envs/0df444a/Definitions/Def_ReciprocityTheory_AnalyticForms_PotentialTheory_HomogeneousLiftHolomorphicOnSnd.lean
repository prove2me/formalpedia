-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:24.358877+00:00
-- url     : https://prove2.me/theorems/f4a4ad94-1a66-4415-8564-85cef8b19c77
-- title:
--   Homogeneous Lift Holomorphic On Snd
-- statement:
--   Definitions and structural lemmas for Homogeneous Lift Holomorphic On Snd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply


set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
section Alg
variable {e : ℕ} {X : Type*} [TopologicalSpace X]
end Alg
namespace CompatibleChartOperations
def shearLE : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 0 - v 1, v 1]
  invFun v := ![v 0 + v 1, v 1]
  map_add' u v := by ext i; fin_cases i <;> simp [add_sub_add_comm]
  map_smul' c v := by ext i; fin_cases i <;> simp [mul_sub]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
def shearCLE : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) := shearLE.toContinuousLinearEquiv
def homogeneousCoord (p : OnePoint ℂ) : ℂ × ℂ := p.elim (0, 1) (fun z => (1, z))
open scoped Classical in

def homogeneousLift (a p : OnePoint ℂ) : ℂ × ℂ := if a = ∞ then (crd1 p, 1) else (1, crd0 p)
def det2 (u v : ℂ × ℂ) : ℂ := u.1 * v.2 - u.2 * v.1
def nrm2 (u : ℂ × ℂ) : ℝ := Real.sqrt (‖u.1‖ ^ 2 + ‖u.2‖ ^ 2)
open scoped Classical in

def chartIndexAt (a : OnePoint ℂ) : Fin 2 := if a = ∞ then 1 else 0
def chartCoordAt (a p : OnePoint ℂ) : ℂ := (p1.chart (chartIndexAt a) p) 0
end CompatibleChartOperations
end
end ReciprocityTheory.AnForm.M


