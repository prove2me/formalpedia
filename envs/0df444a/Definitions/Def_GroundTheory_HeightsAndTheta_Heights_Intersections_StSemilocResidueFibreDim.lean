-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFibreDim
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFibreDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:46.203984+00:00
-- url     : https://prove2.me/theorems/206cd360-8181-4e09-a04c-3994e4a9b0c6
-- title:
--   St Semiloc Residue Fibre Dim
-- statement:
--   Definitions and structural lemmas for St Semiloc Residue Fibre Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StSemilocResidueFibreDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocResidueDeg
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
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
def SemilocResidueFibreDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)),
    IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ W' ∈ fibreOver v P' W, ∀ G' : GenFibre v W', IsProjVarF (fibreIdeal κ G') 0
end GroundTheory.Heights₂.Heights.Inter


