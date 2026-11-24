-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocFrame
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocFrame
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:25.784211+00:00
-- url     : https://prove2.me/theorems/24012111-3544-4e46-906c-494e5ca91c10
-- title:
--   Loc Frame
-- statement:
--   Definitions and structural lemmas for Loc Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocFrame.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open Matrix NumberField
namespace PI.ScPiBuildW.Rv
open PI.ScPiExists
lemma phi_star (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (a : I.E) :
    I.φ v (star a) = star (I.φ v a) := by
  exact I.cm.cmUnram.2.1 (I.φ v) a
lemma hJ_rv (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hJm : Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = (I.P v)ᴴ * I.J.map (I.φ v) := by
    rw [← I.P_spec v, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  have hPP : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one]
  set u : Fin I.n → ℂ := fun i => I.φ v (x i)
  set w : Fin I.n → ℂ := fun i => I.φ v (y i)
  have key : hJ (I.ε v) (rv I v x) (rv I v y) = star u ⬝ᵥ (I.J.map (I.φ v) *ᵥ w) := by
    unfold hJ rv
    rw [Matrix.mulVec_mulVec, hJm, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  rw [key]
  simp only [u, w, Formalism.UG.hform, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul,
    Pi.star_apply, Finset.mul_sum, starRingEnd_apply, phi_star, mul_assoc]
lemma phi_ite (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {r : ℕ} (a b : Fin r) :
    I.φ v (if a = b then (1 : I.E) else 0) = if a = b then 1 else 0 := by
  split_ifs <;> simp
def locFrame (I : Formalism.MainNotions.S.AutInst) {r k : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (hn : I.n = 2 * r + k + 1) (hF : IsFrame I e f z)
    (hz : Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0) (v : InfinitePlace I.F) (w : Fin k → Fin I.n → ℂ)
    (hw : (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0) :
    Loc.LocFrame I.n r k (I.ε v) where
  e := fun a => rv I v (e a)
  f := fun a => rv I v (f a)
  z := rv I v z
  w := w
  hn := hn
  ee := fun a b => by rw [hJ_rv, hF.1 a b, map_zero]
  ef := fun a b => by rw [hJ_rv, hF.2.2.1 a b, phi_ite]
  ez := fun a => by rw [hJ_rv, (hF.2.2.2 a).1, map_zero]
  fz := fun a => by rw [hJ_rv, (hF.2.2.2 a).2, map_zero]
  zz := by rw [hJ_rv]; exact (map_ne_zero (I.φ v)).2 hz
  ww := hw.1
  ew := fun c a => ((hw.2 a).1 c).1
  fw := fun c a => ((hw.2 a).1 c).2
  zw := fun a => (hw.2 a).2
section Simp
variable (I : Formalism.MainNotions.S.AutInst) {r k : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
  (hn : I.n = 2 * r + k + 1) (hF : IsFrame I e f z)
  (hz : Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0) (v : InfinitePlace I.F) (w : Fin k → Fin I.n → ℂ)
  (hw : (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0)
end Simp
end PI.ScPiBuildW.Rv


