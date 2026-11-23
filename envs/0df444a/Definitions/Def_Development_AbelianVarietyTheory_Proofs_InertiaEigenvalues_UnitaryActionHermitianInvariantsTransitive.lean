-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:36.784866+00:00
-- url     : https://prove2.me/theorems/cdc07328-27b7-4233-8514-59842e4f6a14
-- title:
--   Unitary Action Hermitian Invariants Transitive
-- statement:
--   Definitions and structural lemmas for Unitary Action Hermitian Invariants Transitive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
theorem star_algebraMap [Unram F E] (x : F) : star (algebraMap F E x) = algebraMap F E x := Unram.star_fix x
def starLin [Unram F E] : E →ₗ[F] E where
  toFun := star
  map_add' := star_add
  map_smul' c z := by
    simp only [Algebra.smul_def, RingHom.id_apply, star_mul, star_algebraMap, mul_comm]
section Gen
variable {r : ℕ} {K : Type} [CommRing K]
def ev (r : ℕ) (K : Type) [CommRing K] (j : ℕ) : Fin r → K := fun i => if (i : ℕ) = j then 1 else 0
end Gen
section Herm
variable {r : ℕ}
variable [Unram F E]
end Herm
section Act
variable {r : ℕ}
end Act
section Gen2
variable {r : ℕ} {K : Type} [CommRing K]
end Gen2
section Main
variable {r : ℕ}
end Main
section Three
variable {r : ℕ}
end Three
section Four
variable {r : ℕ}
end Four
end GlobalTheory.JR.HermInv


