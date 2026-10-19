-- Prove2me | Definitions.Def_QAlgorithms_Defs_ReedSolomonData
-- name    : QAlgorithms_Defs_ReedSolomonData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:35.887904+00:00
-- url     : https://prove2.me/theorems/4375ed98-e67e-46e5-93fb-9335d5a77bf1
-- title:
--   ReedSolomonData
-- statement:
--   ReedSolomonData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ReedSolomonData.lean

import Definitions.Def_QAlgorithms_Defs_OPIFieldData
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.ReedSolomon

/-- GRS code as the actual scaled evaluation image;
2610.02145 p.10 (2.10), 2607.16541 p.10.
Distinct points, nonzero multipliers and k≤m are its source domain. -/
def grsCode {F : Type*} [Field F] {m : ℕ} (alpha v : Fin m → F) (k : ℕ)
    (_distinct : Function.Injective alpha) (_nonzero : ∀ i, v i ≠ 0) (_hk : k ≤ m) :
    Submodule F (Fin m → F) :=
  LinearMap.range ((Matrix.diagonal v * OPI.vandermondeEncoder alpha k).mulVecLin)

/-- Computed dual multipliers, including evaluation at zero;
2610.02145 p.10 (2.12), 2607.16541 p.10. -/
def dualMultipliers {F : Type*} [Field F] {m : ℕ} (alpha : Fin m → F)
    (_distinct : Function.Injective alpha) : Fin m → F :=
  fun i => (∏ j ∈ Finset.univ.erase i, (alpha i-alpha j))⁻¹

example {F : Type*} [Field F] (alpha v : Fin 0 → F)
    (hd : Function.Injective alpha) (hv : ∀ i, v i ≠ 0) :
    grsCode alpha v 0 hd hv (by omega) = ⊥ := by
  simp [grsCode, OPI.vandermondeEncoder]
  exact LinearMap.range_eq_bot.mpr (by ext x i; exact Fin.elim0 i)

example {F : Type*} [Field F] (alpha : Fin 1 → F) (h : Function.Injective alpha) :
    dualMultipliers alpha h 0 = 1 := by simp [dualMultipliers]

end QAlgorithms.ReedSolomon


