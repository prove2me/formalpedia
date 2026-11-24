-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:08.532646+00:00
-- url     : https://prove2.me/theorems/31d1fcb6-2559-4b97-a403-45a9e425bf6a
-- title:
--   PProj Bundle Multi Homog Span
-- statement:
--   Definitions and structural lemmas for PProj Bundle Multi Homog Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogSpan.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def toFn (P : Ideal (MRing ι)) : MRing ι →+* FnField P :=
  (algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)
def genMap (P : Ideal (MRing ι)) {N1 : ℕ} {S : Type} [Fintype S] (v : S → Fin N1 → FnField P) :
    MRing (PBlk ι N1) →+* MvPolynomial S (FnField P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt P ⟨k, i⟩)
    | ⟨.inr _, j⟩ => ∑ s, C (v s j) * X s
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


