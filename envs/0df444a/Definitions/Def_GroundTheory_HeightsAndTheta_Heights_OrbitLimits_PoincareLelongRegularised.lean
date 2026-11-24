-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongRegularised
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongRegularised
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:13.910988+00:00
-- url     : https://prove2.me/theorems/4b40e1f2-44e1-4bd2-9c4e-ee47a646e45d
-- title:
--   Poincare Lelong Regularised
-- statement:
--   Definitions and structural lemmas for Poincare Lelong Regularised, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PoincareLelongRegularised.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
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
namespace GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
def PoincareLelongRegularised.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    Tendsto (fun ε => ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε))
      (𝓝[>] 0) (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (logNorm A s)))
end GroundTheory.Heights₂.Heights.Targets


