-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLattice
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:42.27117+00:00
-- url     : https://prove2.me/theorems/5085f501-4191-42c3-9cac-4a88267bda8b
-- title:
--   Exists Lattice Datum Of Self Dual Lattice
-- statement:
--   Definitions and structural lemmas for Exists Lattice Datum Of Self Dual Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeDatumOfSelfDualLattice.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Theorems.Thm_GlobalTheory_HermModel_herm_add_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix nonZeroDivisors TensorProduct
namespace GlobalTheory.LatticeDatum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]
noncomputable def traceHerm (ξ : E) (G : Matrix (Fin r) (Fin r) E) : (Fin r → E) →+ (Fin r → E) →+ ℚ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Algebra.trace ℚ E (ξ * herm G x y))
    fun y y' => by rw [HermModel.herm_add_right, mul_add, map_add])
    fun x x' => AddMonoidHom.ext fun y => by
      change Algebra.trace ℚ E (ξ * herm G (x + x') y) =
        Algebra.trace ℚ E (ξ * herm G x y) + Algebra.trace ℚ E (ξ * herm G x' y)
      rw [herm_add_left, mul_add, map_add]
end GlobalTheory.LatticeDatum


