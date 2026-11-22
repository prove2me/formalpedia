-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:48:26.234+00:00
-- url     : https://prove2.me/theorems/2d53e0b6-4755-4004-94a6-02710a20c2fa
-- title:
--   ZIter B
-- statement:
--   Definitions and structural lemmas for ZIter B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)
abbrev En : Type := (Fin s → ℂ) →L[ℝ] (Fin s → ℂ)
def act (Z : Fin s → Fin s → ℂ) : En s :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (Matrix.of Z).mulVec v
      map_add' := fun v w => Matrix.mulVec_add _ _ _
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }
theorem act_apply (Z : Fin s → Fin s → ℂ) (v : Fin s → ℂ) : act s Z v = (Matrix.of Z).mulVec v := rfl
def eA : (Fin s → Fin s → ℂ) →L[ℝ] En s :=
  LinearMap.toContinuousLinearMap
    { toFun := act s
      map_add' := fun Z Z' => by
        ext1 v
        simp only [act_apply, ContinuousLinearMap.add_apply]
        exact Matrix.add_mulVec _ _ _
      map_smul' := fun c Z => by
        ext1 v
        simp only [act_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        exact Matrix.smul_mulVec c (Matrix.of Z) v }
def invF (Z : Fin s → Fin s → ℂ) : Fin s → Fin s → ℂ := Matrix.of.symm (Matrix.of Z)⁻¹
def lamL (a b : Fin s) (ε : Bool) (T : En s) : (Fin s → Fin s → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W => if ε then (T (fun c => W c b) a).re else (T (fun c => W c b) a).im
      map_add' := fun W W' => by
        have : (fun c => (W + W') c b) = (fun c => W c b) + (fun c => W' c b) := rfl
        rw [this, map_add]
        cases ε <;> simp
      map_smul' := fun r W => by
        have : (fun c => (r • W) c b) = r • (fun c => W c b) := rfl
        rw [this, map_smul]
        cases ε <;> simp }
theorem lamL_apply (a b : Fin s) (ε : Bool) (T : En s) (W : Fin s → Fin s → ℂ) :
    lamL s a b ε T W = if ε then (T (fun c => W c b) a).re else (T (fun c => W c b) a).im := rfl
def lamF (i : Fin s × Fin s × Bool) : En s →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => lamL s i.1 i.2.1 i.2.2 T
      map_add' := fun T T' => by
        ext W; simp only [lamL_apply, ContinuousLinearMap.add_apply]
        cases i.2.2 <;> simp
      map_smul' := fun c T => by
        ext W; simp only [lamL_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        cases i.2.2 <;> simp }
def cF (i : Fin s × Fin s × Bool) (Z : Fin s → Fin s → ℂ) : (Fin s → Fin s → ℂ) →L[ℝ] ℝ :=
  lamF s i (Ring.inverse (eA s Z))
end PI.UnitaryGroupMassFormula.UsCost.ZI


