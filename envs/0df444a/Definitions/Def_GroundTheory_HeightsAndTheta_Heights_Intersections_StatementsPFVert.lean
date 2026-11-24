-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:22.597853+00:00
-- url     : https://prove2.me/theorems/7d32433f-c776-4f36-800e-1b36e70d9d67
-- title:
--   Statements PFVert
-- statement:
--   Definitions and structural lemmas for Statements PFVert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsPFVert.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFSecRed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
def PFVert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι')
    (s : MRing ι') (a : K' → ℕ) (W : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d →
    (∀ j, IsPullHerm κ v (L j) (L' j)) → IsMultiHomog s a → s ∉ P' →
    W ∈ divSupp P' s → ¬ IsHorizontal W →
    geoNum (d + r) W (fun j => (Fin.append L' N j).a) = 0
section Inhabitants
def fibreAtTwo : Ideal (MRing PointLineBlocks) := Ideal.span {C 2}
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Inter


