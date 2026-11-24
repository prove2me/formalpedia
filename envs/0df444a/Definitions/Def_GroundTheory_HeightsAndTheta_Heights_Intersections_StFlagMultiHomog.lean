-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:06.646809+00:00
-- url     : https://prove2.me/theorems/347d304f-7612-4acc-8d17-4db023dcf232
-- title:
--   St Flag Multi Homog
-- statement:
--   Definitions and structural lemmas for St Flag Multi Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StFlagMultiHomog.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
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
def FlagMultiHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (P : Ideal (MRing ι)) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)),
    P.IsPrime → IsMultiHomogIdeal P → (∀ a j, IsMultiHomog (c a j) m) → IsKerBasis P c B →
    IsMultiHomogIdeal (flagIdeal P B)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


