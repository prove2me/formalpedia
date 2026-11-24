-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:22.891016+00:00
-- url     : https://prove2.me/theorems/bda1cf4f-1899-4fc8-b3c5-025373b016ab
-- title:
--   St Semiloc Rank Frac
-- statement:
--   Definitions and structural lemmas for St Semiloc Rank Frac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StSemilocRankFrac.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRankAdjoin
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
def SemilocRankFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (s : MRing ι) (α : K → ℕ) (W : Ideal (MRing ι)) (i' : ∀ k', ι' k')
    (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)) [Algebra ℚ G.Φ'],
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ P') →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) =
      IntermediateField.relfinrank
        (IntermediateField.adjoin ℚ
          (Set.range ((fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩))
end GroundTheory.Heights₂.Heights.Inter


