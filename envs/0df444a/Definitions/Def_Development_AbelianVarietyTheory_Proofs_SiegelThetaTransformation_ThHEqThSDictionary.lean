-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:20.902203+00:00
-- url     : https://prove2.me/theorems/c3f7d1cc-14ff-4e22-ad6d-44c446f3fed8
-- title:
--   Th HEq Th SDictionary
-- statement:
--   Definitions and structural lemmas for Th HEq Th SDictionary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.Dict
noncomputable section
section Levels
end Levels
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
def ofQEquiv (E : Type) [Field E] [NumberField E] (n N : ℕ) :
    Matrix (Fin n) (QI E N) ℚ ≃+ Matrix (Fin n) (Fin N) E where
  toFun := ofQ
  invFun x := Matrix.of fun k p => (Module.finBasis ℚ E).repr (x k p.1) p.2
  left_inv m := by
    ext k p
    simp only [ofQ, Matrix.of_apply]
    rw [(Module.finBasis ℚ E).repr_sum_self]
  right_inv x := by
    ext k a
    simp only [ofQ, Matrix.of_apply]
    exact (Module.finBasis ℚ E).sum_repr _
  map_add' m m' := by
    ext k a
    simp [ofQ, add_smul, Finset.sum_add_distrib]
variable (Ψ : Finset (E →+* ℂ))
def vec (σ : E →+* ℂ) (m : QI E N → ℂ) : Fin N → ℂ :=
  fun a => ∑ j, σ (Module.finBasis ℚ E j) * m (a, j)
variable {Ψ}
end
end GlobalTheory.SW.Dict


