-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueAdjoin
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueAdjoin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:58.998308+00:00
-- url     : https://prove2.me/theorems/9803736b-a932-41a3-8b60-73ba2535344f
-- title:
--   St Semiloc Residue Adjoin
-- statement:
--   Definitions and structural lemmas for St Semiloc Residue Adjoin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StSemilocResidueAdjoin.lean

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
def SemilocResidueAdjoin.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')]
      (G' : GenFibre v W') (i' : ∀ k', ι' k'), (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ W') →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.length (locRing (imageZ v P') W)
        (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' (fibreOver v P' W) W' hW') =
      (Module.finrank G'.Φ (IntermediateField.adjoin G'.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩)) : ℕ∞)
end GroundTheory.Heights₂.Heights.Inter


