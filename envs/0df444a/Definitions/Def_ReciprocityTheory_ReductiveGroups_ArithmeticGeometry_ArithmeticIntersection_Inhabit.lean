-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_Inhabit
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_Inhabit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:00.03044+00:00
-- url     : https://prove2.me/theorems/30e75a8b-91ed-4309-871e-1fffcba3c88a
-- title:
--   Inhabit
-- statement:
--   Definitions and structural lemmas for Inhabit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/Inhabit.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CompRightEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AI
namespace Inhabit
noncomputable def mon {n m : ℕ} (a : Fin n → Fin m) :
    MultilinearMap ℝ (fun _ : Fin n => (Fin m → ℝ)) ℝ :=
  (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap (fun j => LinearMap.proj (a j))
theorem mon_apply {n m : ℕ} (a : Fin n → Fin m) (v : Fin n → Fin m → ℝ) :
    mon a v = ∏ j, v j (a j) := by
  simp [mon]
noncomputable def formI : MultilinearMap ℝ (fun _ : Fin 2 => (Fin 2 → ℝ)) ℝ :=
  (1 / 2 : ℝ) • mon (fun _ => 0)
noncomputable def formW : MultilinearMap ℝ (fun _ : Fin 3 => (Fin 3 → ℝ)) ℝ :=
  (-(1 / 2) : ℝ) • ∑ k : Fin 3, mon (fun j => if j = k then 1 else 0)
theorem formI_apply (v : Fin 2 → Fin 2 → ℝ) : formI v = 1 / 2 * (v 0 0 * v 1 0) := by
  simp [formI, mon_apply, Fin.prod_univ_two]
theorem formW_apply' (v : Fin 3 → Fin 3 → ℝ) :
    formW v = -(1 / 2) * ∑ k : Fin 3, ∏ j, v j (if j = k then 1 else 0) := by
  simp only [formW, smul_apply, sum_apply, mon_apply, smul_eq_mul]
theorem formW_apply (v : Fin 3 → Fin 3 → ℝ) :
    formW v = -(1 / 2) * (v 0 1 * v 1 0 * v 2 0 + v 0 0 * v 1 1 * v 2 0 + v 0 0 * v 1 0 * v 2 1) := by
  rw [formW_apply']
  simp [Fin.sum_univ_three, Fin.prod_univ_three]
theorem formI_symm : IsSymmForm formI := by
  intro σ v
  simp only [formI, smul_apply, mon_apply, Function.comp_apply]
  rw [Equiv.prod_comp σ (fun j => v j 0)]
theorem formW_symm : IsSymmForm formW := by
  intro σ v
  rw [formW_apply', formW_apply', ← Equiv.sum_comp σ (fun k => ∏ j, v j (if j = k then 1 else 0))]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Equiv.prod_comp σ (fun j => v j (if j = σ k then 1 else 0))]
  simp
noncomputable def pOne : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![v 0, 0, v 1]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp
noncomputable def pTwo : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![0, v 0, v 1]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp
noncomputable def model : FibreSquare.{0} 1 where
  V := Fin 2 → ℝ
  VW := Fin 3 → ℝ
  I := formI
  IW := formW
  p₁ := pOne
  p₂ := pTwo
  ξ := ![1, 0]
  A := ![0, 1]
  Φ := (formW.curryLeft (pOne ![1, 0])).curryLeft (pOne ![1, 0]) -
    (formW.curryLeft (pTwo ![1, 0])).curryLeft (pTwo ![1, 0])
  symm := formI_symm
  symmW := formW_symm
  comp_right_eq_zero_alt v := by
    rw [formW_apply]
    simp [pTwo]
  cons_comp_left v := by
    have h : formW ![-(pTwo ![1, 0]), pOne (v 0), pOne (v 1)] = formI v := by
      rw [formW_apply, formI_apply]
      simp [pOne, pTwo]
    rw [← h]
    congr 1
    ext1 j
    fin_cases j <;> rfl
  base := by
    ext i
    fin_cases i <;> simp [pOne, pTwo]
  diag T := rfl
end Inhabit
end ReciprocityTheory.ChartRestriction.G.AI


