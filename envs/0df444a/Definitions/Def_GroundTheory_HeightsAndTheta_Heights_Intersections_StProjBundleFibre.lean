-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:30.294652+00:00
-- url     : https://prove2.me/theorems/6dd2a8c7-bbe6-4b67-88a9-2bf20cfeedf4
-- title:
--   St Proj Bundle Fibre
-- statement:
--   Definitions and structural lemmas for St Proj Bundle Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StProjBundleFibre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
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
def ProjBundleFibreLine.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin 2) (Fin N1) (FnField P)),
    IsArithVar P d → IsQuotRows P c m 2 → IsKerBasis P c B →
    ∃ G : GenFibre (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B),
      ∃ S : Set (MRingOver G.Φ (fibreIdx (PBlk ι N1) (Sum.inl : K → K ⊕ Unit))),
        (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ fibreIdeal Sum.inl G = Ideal.span S
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


