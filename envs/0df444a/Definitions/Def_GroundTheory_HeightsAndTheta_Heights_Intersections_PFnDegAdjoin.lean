-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFnDegAdjoin
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PFnDegAdjoin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:26:11.700366+00:00
-- url     : https://prove2.me/theorems/b9ce1941-62b8-44f4-b5db-393130402c4f
-- title:
--   PFn Deg Adjoin
-- statement:
--   Definitions and structural lemmas for PFn Deg Adjoin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFnDegAdjoin.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFnDegAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
namespace FnDegAdjoin
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {σ : Type}
def quotEquiv (g : σ → Ω) (I : Ideal (MvPolynomial σ F))
    (h : I = RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] Ω)) :
    (MvPolynomial σ F ⧸ I) ≃ₐ[F] Algebra.adjoin F (Set.range g) :=
  let e1 := Ideal.quotientEquivAlgOfEq F h
  let e2 := Ideal.quotientKerEquivRange (aeval g : MvPolynomial σ F →ₐ[F] Ω)
  let e3 := Subalgebra.equivOfEq _ _ (aeval_range (R := F) g)
  (e1.trans e2).trans e3
end FnDegAdjoin
end GroundTheory.Heights₂.Heights.Inter


