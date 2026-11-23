-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:54.421022+00:00
-- url     : https://prove2.me/theorems/688269aa-f2a3-47e7-b882-1bc73ccce990
-- title:
--   Bc GSmul R
-- statement:
--   Definitions and structural lemmas for Bc GSmul R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeSaturation/BcGSmulR.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}
def bcG (x : Fin n → K) : Fin n → S := fun i => φ (x i)
def latG (Λ : Submodule R (Fin n → K)) : Submodule O (Fin n → S) :=
  Submodule.span O (bcG φ '' (Λ : Set (Fin n → K)))
def fP (f : (Fin n → K) →ₗ[K] K) : (Fin n → S) →ₗ[S] S where
  toFun y := ∑ k, y k * φ (f fun j => if k = j then 1 else 0)
  map_add' y z := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.mul_sum, mul_assoc]
end PI.LocLatSat.UnitaryGroupMassFormula


