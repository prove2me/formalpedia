-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocLength
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:48.848029+00:00
-- url     : https://prove2.me/theorems/44cb1a7b-fe83-49f7-ac98-886c4664e967
-- title:
--   Statements Semiloc Length
-- statement:
--   Definitions and structural lemmas for Statements Semiloc Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocLength.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
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
def SemilocLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s t : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (E : Ideal (MRing ι') → ℤ) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1))
    (y : locRing (imageZ v P') W),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → IsMultiHomog t α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → t ∉ W →
    (y : FractionRing (MRing ι ⧸ imageZ v P')) * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) →
    (∀ W' ∈ divSupp P' (rename v s), imageZ v W' = W →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (fibreIdeal κ G') 0 Fin.elim0) →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    ∃ N : ℕ, Module.length (locRing (imageZ v P') W)
        (semiLocRing P' (fibreOver v P' W) ⧸ LinearMap.range
          (LinearMap.lsmul (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) y)) = N ∧
      (N : ℤ) = ∑ᶠ W' ∈ {W' | W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W},
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W'
end GroundTheory.Heights₂.Heights.Inter


