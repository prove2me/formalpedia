-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:54.806354+00:00
-- url     : https://prove2.me/theorems/18ff1d1e-bcf5-4776-a6e0-922012ef885b
-- title:
--   Finrank Val Perp
-- statement:
--   Definitions and structural lemmas for Finrank Val Perp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankValPerp.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
namespace DensInertW
section form
variable {L : Type} [Field L] {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
theorem val_add_left (x x' y : Fin n → L) : hf q M (x + x') y = hf q M x y + hf q M x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
theorem val_smul_left (c : L) (x y : Fin n → L) : hf q M (c • x) y = c * hf q M x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
def valL (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (y : Fin n → L) : (Fin n → L) →ₗ[L] L where
  toFun x := hf q M x y
  map_add' x x' := val_add_left x x' y
  map_smul' c x := by simp only [val_smul_left, smul_eq_mul, RingHom.id_apply]
def valPerp (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L))
    (e : Fin n → L) : Submodule L (Fin n → L) :=
  (LinearMap.ker ((valL q M e).domRestrict W)).map W.subtype
end form
section formK
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}
end formK
end DensInertW


