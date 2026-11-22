-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:50:25.874974+00:00
-- url     : https://prove2.me/theorems/82cce0bc-a0aa-49c8-8aca-db09e30fab20
-- title:
--   Model Map
-- statement:
--   Definitions and structural lemmas for Model Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace MMap
lemma poly_ext {N : ℕ} {p q : MvPolynomial (Fin N × Fin N) ℂ}
    (h : ∀ A : Matrix (Fin N) (Fin N) ℂ, evM A p = evM A q) : p = q := by
  apply MvPolynomial.funext
  intro x
  have := h (Matrix.of fun i j => x (i, j))
  simpa [evM] using this
lemma evM_add {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (p + q) = evM A p + evM A q := by simp [evM]
lemma evM_smul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (c • p) = c * evM A p := by
  rw [evM, evM, smul_eq_C_mul, eval_mul, eval_C]
lemma evM_rename_swap {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (rename Prod.swap q) = evM Aᵀ q := by
  simp only [evM, eval_rename]
  rfl
section
variable {N : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {P : Matrix (Fin N) (Fin N) ℂ → (V →ₗ[ℂ] V)} (hP : IsPolyMon P) (v0 : V)
def Fq (x : V) : MvPolynomial (Fin N × Fin N) ℂ :=
  rename Prod.swap (Classical.choose (hP.poly x v0))
lemma evM_Fq (x : V) (A : Matrix (Fin N) (Fin N) ℂ) : evM A (Fq hP v0 x) = ⟪v0, P Aᵀ x⟫_ℂ := by
  unfold Fq
  rw [evM_rename_swap]
  exact Classical.choose_spec (hP.poly x v0) Aᵀ
def Fl : V →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ where
  toFun := Fq hP v0
  map_add' x y := poly_ext fun A => by
    rw [evM_add, evM_Fq, evM_Fq, evM_Fq, map_add, inner_add_right]
  map_smul' c x := poly_ext fun A => by
    rw [RingHom.id_apply, evM_smul, evM_Fq, evM_Fq, map_smul, inner_smul_right]
end
end MMap
end PI.WMI


