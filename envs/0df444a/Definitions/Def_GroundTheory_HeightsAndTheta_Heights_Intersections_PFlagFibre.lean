-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:46.526271+00:00
-- url     : https://prove2.me/theorems/65cd810f-6134-4bb1-a04e-65503f510360
-- title:
--   PFlag Fibre
-- statement:
--   Definitions and structural lemmas for PFlag Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
section Linear
variable {K : Type} {ι : K → Type} {N1 n : ℕ}
def flagFibreBlocksEquiv : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)) ≃ Fin (n - 1) where
  toFun k := match k with
    | ⟨.inl k, h⟩ => (h ⟨k, rfl⟩).elim
    | ⟨.inr j, _⟩ => j
  invFun j := ⟨.inr j, by rintro ⟨k, hk⟩; cases hk⟩
  left_inv k := by
    match k with
    | ⟨.inl k, h⟩ => exact (h ⟨k, rfl⟩).elim
    | ⟨.inr j, _⟩ => rfl
  right_inv _ := rfl
def flagCompound {F : Type} [Field F] (B : Matrix (Fin n) (Fin N1) F) :
    ∀ k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)),
      fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl k → PluckerBlocks n n (flagFibreBlocksEquiv k) → F
  | ⟨.inl k, h⟩ => (h ⟨k, rfl⟩).elim
  | ⟨.inr _, _⟩ => fun S S' => (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det
end Linear
section Compound
variable {F : Type} [Field F] {N1 n : ℕ}
end Compound
section Fibre
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
end Fibre
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


