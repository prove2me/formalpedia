-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGL
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:18.153317+00:00
-- url     : https://prove2.me/theorems/d2129377-d1a4-4abd-93db-b5354ee0d6e8
-- title:
--   Transpose Invariant Of Conj Invariant Distribution GL
-- statement:
--   Definitions and structural lemmas for Transpose Invariant Of Conj Invariant Distribution GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TransposeInvariantOfConjInvariantDistributionGL.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaireStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhausStatement
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
noncomputable section
namespace GlobalTheory.GelfandKazhdan
section General
variable {G : Type} [Group G] [TopologicalSpace G]
def pull (t : G ≃ₜ G) : SB G →ₗ[ℂ] SB G where
  toFun φ := ⟨fun x => φ.1 (t x), φ.2.1.comp_continuous t.continuous, φ.2.2.comp_homeomorph t⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end General
section Transpose
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
def trGL (g : GL n R) : GL n R :=
  ⟨g.val.transpose, g.inv.transpose, by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]⟩
theorem trGL_trGL (g : GL n R) : trGL (trGL g) = g := rfl
theorem continuous_trGL [TopologicalSpace R] : Continuous (trGL : GL n R → GL n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_transpose,
    Units.continuous_coe_inv.matrix_transpose⟩
def trHomeo [TopologicalSpace R] : GL n R ≃ₜ GL n R where
  toFun := trGL
  invFun := trGL
  left_inv := trGL_trGL
  right_inv := trGL_trGL
  continuous_toFun := continuous_trGL
  continuous_invFun := continuous_trGL
end Transpose
end GlobalTheory.GelfandKazhdan


