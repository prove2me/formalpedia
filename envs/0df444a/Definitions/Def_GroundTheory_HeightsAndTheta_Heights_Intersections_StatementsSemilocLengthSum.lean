-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocLengthSum
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocLengthSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:47.837423+00:00
-- url     : https://prove2.me/theorems/d17bb4fd-820f-491c-8fca-c96d90c7b193
-- title:
--   Statements Semiloc Length Sum
-- statement:
--   Definitions and structural lemmas for Statements Semiloc Length Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocLengthSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocLength
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
def SemilocLengthSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s t : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (E : Ideal (MRing ι') → ℤ) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1))
    (y : locRing (imageZ v P') W),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → IsMultiHomog t α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → t ∉ W →
    (y : FractionRing (MRing ι ⧸ imageZ v P')) * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) →
    (∀ W' ∈ fibreOver v P' W, rename v s ∈ W' →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (fibreIdeal κ G') 0 Fin.elim0) →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    (fibreOver v P' W).Finite ∧
      ∃ N : ℕ, Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ LinearMap.range
            (LinearMap.lsmul (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) y)) = N ∧
        (N : ℤ) = ∑ᶠ W' ∈ {W' | W' ∈ fibreOver v P' W ∧ rename v s ∈ W'},
          ((Module.length (locRing P' W') (locRing P' W' ⧸ locIdeal P' W' (fracMapZ v P' y))).toNat : ℤ) * E W'
end GroundTheory.Heights₂.Heights.Inter


